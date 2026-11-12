import Langlands.GroupScheme.SymplecticMatrix.RootSystem
import Langlands.GroupScheme.Reductive.LinkedRootsAlmostSimple
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction

/-! # The split symplectic group is absolutely almost simple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TypeC

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} {l : Type}

/-- **Linked roots of type `C`.** Let `e : l → X(T)` be characters such that every root of `t`
is `±2e_a` or `e_b - e_a`, `-e_a - e_b`, `e_a + e_b` with `a ≠ b`. Suppose that for `a ≠ b` the
short roots `e_b - e_a` and `-e_a - e_b` are linked to `2e_a`, and `e_b - e_a` and `e_b + e_a`
are linked to `-2e_b`. If `l` has two distinct elements, any two roots are joined by a chain of
linked roots. -/
theorem reflTransGen_rootsLinked_of_typeC (e : l → characterLattice T)
    (hroots : ∀ χ ∈ relativeRoots t, (∃ a, χ = 2 • e a ∨ χ = -(2 • e a)) ∨
      ∃ a b, a ≠ b ∧ (χ = e b - e a ∨ χ = -e a - e b ∨ χ = e a + e b))
    (hlink₁ : ∀ a b, a ≠ b → RootsLinked t (e b - e a) (2 • e a))
    (hlink₂ : ∀ a b, a ≠ b → RootsLinked t (-e a - e b) (2 • e a))
    (hlink₃ : ∀ a b, a ≠ b → RootsLinked t (e b - e a) (-(2 • e b)))
    (hlink₄ : ∀ a b, a ≠ b → RootsLinked t (e b + e a) (-(2 • e b)))
    (hl : ∃ a b : l, a ≠ b) :
    ∀ α ∈ relativeRoots t, ∀ β ∈ relativeRoots t,
      Relation.ReflTransGen (RootsLinked t) α β := by
  obtain ⟨a₀, a₁, h₀₁⟩ := hl
  let R := Relation.ReflTransGen (RootsLinked t)
  have hsymm : ∀ {α β}, R α β → R β α := by
    intro α β h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single hbc.symm).trans ih
  have edge : ∀ {α β}, RootsLinked t α β → R α β := fun h => Relation.ReflTransGen.single h
  have edge' : ∀ {α β}, RootsLinked t α β → R β α := fun h => Relation.ReflTransGen.single h.symm
  have other : ∀ a : l, ∃ b, a ≠ b := fun a => by
    by_cases ha : a = a₀
    · exact ⟨a₁, ha ▸ h₀₁⟩
    · exact ⟨a₀, ha⟩
  -- Every long root `2e_a` is joined to `2e_{a₀}`.
  have hpos : ∀ a, R (2 • e a) (2 • e a₀) := by
    intro a
    by_cases ha : a = a₀
    · subst ha
      exact Relation.ReflTransGen.refl
    · have h₁ := edge' (hlink₂ a a₀ ha)
      have h₂ := edge (hlink₂ a₀ a (Ne.symm ha))
      rw [show -e a₀ - e a = -e a - e a₀ by abel] at h₂
      exact h₁.trans h₂
  -- Every root `-2e_a` is joined to some `2e_b`.
  have hneg : ∀ a, R (-(2 • e a)) (2 • e a₀) := by
    intro a
    obtain ⟨b, hab⟩ := other a
    have h₁ := edge' (hlink₃ b a (Ne.symm hab))
    have h₂ := edge (hlink₁ b a (Ne.symm hab))
    exact h₁.trans (h₂.trans (hpos b))
  have hbase : ∀ α ∈ relativeRoots t, R α (2 • e a₀) := by
    intro α hα
    rcases hroots α hα with ⟨a, rfl | rfl⟩ | ⟨a, b, hab, rfl | rfl | rfl⟩
    · exact hpos a
    · exact hneg a
    · exact (edge (hlink₁ a b hab)).trans (hpos a)
    · exact (edge (hlink₂ a b hab)).trans (hpos a)
    · exact (edge (hlink₄ b a (Ne.symm hab))).trans (hneg a)
  intro α hα β hβ
  exact (hbase α hα).trans (hsymm (hbase β hβ))

/-- **Almost simplicity from a type `C` root datum.** Over an algebraically closed field, let `G`
be nontrivial and semisimple with a split maximal torus `t`. Let `e : l → X(T)` and
`ν : l → X_*(T)` be dual families, with `l` having two distinct elements. Suppose the roots of `t`
are among `±2e_a`, `e_b - e_a`, `-e_a - e_b`, `e_a + e_b` (`a ≠ b`), that `2e_a`, `e_b - e_a` and
`-e_a - e_b` are roots, and that a root datum `P` realizing `t` has coroot `ν_a` at `2e_a`. Then
`G` is almost simple. -/
theorem isAlmostSimple_of_typeC [IsAlgClosed k] [DecidableEq l] (hG : IsSemisimple G)
    (hT : IsSplitTorus T.toGrp) (hsplit : IsSplitSubtorus t) (hmax : IsMaximalTorus t)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥)
    (e : l → characterLattice T) (ν : l → cocharacterLattice T)
    (hdual : ∀ a c, latticePairing T (e a) (ν c) = if a = c then 1 else 0)
    (hroots : ∀ χ ∈ relativeRoots t, (∃ a, χ = 2 • e a ∨ χ = -(2 • e a)) ∨
      ∃ a b, a ≠ b ∧ (χ = e b - e a ∨ χ = -e a - e b ∨ χ = e a + e b))
    (hlong : ∀ a, 2 • e a ∈ relativeRoots t)
    (hshort : ∀ a b, a ≠ b → e b - e a ∈ relativeRoots t ∧ -e a - e b ∈ relativeRoots t)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf t P) (hcoroot : ∀ r a, P.root r = 2 • e a → P.coroot r = ν a)
    (hl : ∃ a b : l, a ≠ b) : IsAlmostSimple G := by
  have : Infinite k := inferInstance
  have hmemP : ∀ χ ∈ relativeRoots t, ∃ r, P.root r = χ := fun χ hχ => by
    have h : χ ∈ Set.range P.root := by rw [hP.2.1]; exact hχ
    exact h
  have hneg : ∀ χ ∈ relativeRoots t, -χ ∈ relativeRoots t := fun χ hχ => by
    have h : χ ∈ Set.range P.root := by rw [hP.2.1]; exact hχ
    have h' := P.neg_mem_range_root_iff.mpr h
    rw [hP.2.1] at h'
    exact h'
  have hcoroot' : ∀ r a, P.root r = -(2 • e a) → P.coroot r = -ν a := by
    intro r a hr
    obtain ⟨r₀, hr₀⟩ := hmemP _ (hlong a)
    have hrr : r = P.reflectionPerm r₀ r₀ := P.root_eq_neg_iff.mp (by rw [hr, hr₀])
    rw [P.coroot_eq_neg_iff.mpr hrr, hcoroot r₀ a hr₀]
  have hpair : ∀ r r', P.pairing r r' = latticePairing T (P.root r) (P.coroot r') :=
    fun r r' => by rw [← P.root_coroot_eq_pairing, hP.1]
  let f : l → characterLattice T →+ ℤ := fun c => ((latticePairing T).flip (ν c)).toAddMonoidHom
  have hf : ∀ c χ, f c χ = latticePairing T χ (ν c) := fun _ _ => rfl
  have hbound : ∀ c, ∀ χ ∈ relativeRoots t, -2 ≤ f c χ ∧ f c χ ≤ 2 := by
    intro c χ hχ
    rcases hroots χ hχ with ⟨a, rfl | rfl⟩ | ⟨a, b, -, rfl | rfl | rfl⟩ <;>
      simp only [hf, map_nsmul, map_neg, map_sub, map_add, LinearMap.neg_apply,
        LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, hdual, nsmul_eq_mul] <;>
      split_ifs <;> omega
  have mk : ∀ {r r' : J} (g : characterLattice T →+ ℤ), P.pairing r r' = -1 →
      g (P.root r) = -1 → g (P.root r') = 2 → (∀ χ ∈ roots t, -2 ≤ g χ) →
      RootsLinked t (P.root r) (P.root r') := fun g hp h₁ h₂ hb =>
    rootsLinked_of_pairing_eq_neg_one hG.isConnectedReductive hT hmax hP hp
      (strict_combinations_of_coordinate g h₁ h₂ hb)
  have hnegbound : ∀ b, ∀ χ ∈ roots t, -2 ≤ (-(f b)) χ := fun b χ hχ => by
    have := (hbound b χ hχ).2
    rw [AddMonoidHom.neg_apply]
    omega
  have link₁ : ∀ a b, a ≠ b → RootsLinked t (e b - e a) (2 • e a) := by
    intro a b hab
    obtain ⟨r, hr⟩ := hmemP _ (hshort a b hab).1
    obtain ⟨r', hr'⟩ := hmemP _ (hlong a)
    have h := mk (r := r) (r' := r') (f a)
      (by simp [hpair, hr, hcoroot r' a hr', hdual, Ne.symm hab])
      (by simp [hr, hf, hdual, Ne.symm hab])
      (by simp [hr', hf, hdual])
      (fun χ hχ => (hbound a χ hχ).1)
    rwa [hr, hr'] at h
  have link₂ : ∀ a b, a ≠ b → RootsLinked t (-e a - e b) (2 • e a) := by
    intro a b hab
    obtain ⟨r, hr⟩ := hmemP _ (hshort a b hab).2
    obtain ⟨r', hr'⟩ := hmemP _ (hlong a)
    have h := mk (r := r) (r' := r') (f a)
      (by simp [hpair, hr, hcoroot r' a hr', hdual, Ne.symm hab])
      (by simp [hr, hf, hdual, Ne.symm hab])
      (by simp [hr', hf, hdual])
      (fun χ hχ => (hbound a χ hχ).1)
    rwa [hr, hr'] at h
  have link₃ : ∀ a b, a ≠ b → RootsLinked t (e b - e a) (-(2 • e b)) := by
    intro a b hab
    obtain ⟨r, hr⟩ := hmemP _ (hshort a b hab).1
    obtain ⟨r', hr'⟩ := hmemP _ (hneg _ (hlong b))
    have h := mk (r := r) (r' := r') (-(f b))
      (by simp [hpair, hr, hcoroot' r' b hr', hdual, hab])
      (by simp [hr, hf, hdual, hab])
      (by simp [hr', hf, hdual])
      (hnegbound b)
    rwa [hr, hr'] at h
  have link₄ : ∀ a b, a ≠ b → RootsLinked t (e b + e a) (-(2 • e b)) := by
    intro a b hab
    have hmem : e b + e a ∈ relativeRoots t := by
      have h := hneg _ (hshort b a (Ne.symm hab)).2
      rwa [show -(-e b - e a) = e b + e a by abel] at h
    obtain ⟨r, hr⟩ := hmemP _ hmem
    obtain ⟨r', hr'⟩ := hmemP _ (hneg _ (hlong b))
    have h := mk (r := r) (r' := r') (-(f b))
      (by simp [hpair, hr, hcoroot' r' b hr', hdual, hab])
      (by simp [hr, hf, hdual, hab])
      (by simp [hr', hf, hdual])
      (hnegbound b)
    rwa [hr, hr'] at h
  exact isAlmostSimple_of_rootsLinked hG t hsplit hmax hnt
    (reflTransGen_rootsLinked_of_typeC e hroots link₁ link₂ link₃ link₄ hl)

end TypeC

namespace SymplecticMatrix

variable (l : Type) [Fintype l] [DecidableEq l]

/-- The split symplectic group of positive size over a field is nontrivial. -/
theorem range_id_ne_bot [Nonempty l] (K : Type u) [Field K] :
    SubgroupFunctor.range (𝟙 (groupScheme l (CommRingCat.of K))) ≠ ⊥ := by
  obtain ⟨i⟩ := ‹Nonempty l›
  intro hbot
  let T₀ : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 (Spec (CommRingCat.of K)))
  let x : T₀ ⟶ (groupScheme l (CommRingCat.of K)).X :=
    (pointsEquiv l _ T₀).symm ⟨upper 1, upper_mem (by simp [Matrix.IsSymm])⟩
  have hx : x ∈ (SubgroupFunctor.range (𝟙 (groupScheme l (CommRingCat.of K)))).carrier T₀ :=
    SubgroupFunctor.mem_range.2 ⟨x, Category.comp_id x⟩
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
  have h1 := congrArg (fun y => ((pointsEquiv l _ T₀ y : Matrix.symplecticGroup l _) :
    Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) (Sum.inl i) (Sum.inr i)) hx
  simp only [x, MulEquiv.apply_symm_apply, map_one] at h1
  have h2 : (1 : Γ(T₀.left, ⊤)) = 0 := by simpa [upper] using h1
  let e : K ≃+* Γ(T₀.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact one_ne_zero (e.injective (by rw [map_one, map_zero, h2]))

variable {l}

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- **Almost simplicity of the split symplectic group.** Over an algebraically closed field, the
split symplectic group `Sp_{2l}` is almost simple once `l` has two distinct elements. The roots
of the diagonal torus are `±2e_a` and `±e_a ± e_b` (`a ≠ b`), and the long coroot at `2e_a` is
the coordinate cocharacter `e_a^∨`. -/
theorem isAlmostSimple [IsAlgClosed k] (hl : ∃ a b : l, a ≠ b) :
    IsAlmostSimple (groupScheme l (CommRingCat.of k)) := by
  have : Nonempty l := hl.elim fun a _ => ⟨a⟩
  obtain ⟨J, _, P, hP, -⟩ := exists_rootDatum l k
  obtain ⟨e, he⟩ : ∃ e : l → characterLattice 𝔻,
      ∀ a, GeneralLinear.characterCoordEquiv l k (e a) = Pi.single a 1 :=
    ⟨fun a => (GeneralLinear.characterCoordEquiv l k).symm (Pi.single a 1),
      fun a => LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨ν, hν⟩ : ∃ ν : l → cocharacterLattice 𝔻,
      ∀ a, GeneralLinear.cocharacterCoordEquiv l k (ν a) = Pi.single a 1 :=
    ⟨fun a => (GeneralLinear.cocharacterCoordEquiv l k).symm (Pi.single a 1),
      fun a => LinearEquiv.apply_symm_apply _ _⟩
  have hlongRoot : ∀ a, longRoot l k a = 2 • e a := fun a => by
    apply (GeneralLinear.characterCoordEquiv l k).injective
    rw [characterCoordEquiv_longRoot, map_nsmul, he]
    funext c
    simp only [Pi.smul_apply, Pi.single_apply]
    split_ifs <;> rfl
  refine isAlmostSimple_of_typeC (isSimplyConnected l k).isSemisimple
    (isSplitTorus_diagonalTorus l k) (isSplitSubtorus_diagonalTorus l k)
    (isMaximalTorus_diagonalTorus l k) (range_id_ne_bot l k) e ν ?_ ?_ ?_ ?_ hP ?_ hl
  · intro a c
    rw [GeneralLinear.latticePairing_coord, he, hν]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul])
        (by simp), Pi.single_eq_same, mul_one]
    · refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i = a
      · rw [hi, Pi.single_eq_of_ne h, mul_zero]
      · rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro χ hχ
    obtain ⟨x, y, hxy, hχ'⟩ := (mem_roots_iff χ).mp hχ
    have key : ∀ ψ : characterLattice 𝔻,
        GeneralLinear.characterCoordEquiv l k ψ = weightCoord l x - weightCoord l y → χ = ψ :=
      fun ψ hψ => (GeneralLinear.characterCoordEquiv l k).injective (hχ'.trans hψ.symm)
    rcases x with a | a <;> rcases y with b | b
    · have hab : a ≠ b := fun h => hxy (congrArg Sum.inl h)
      refine Or.inr ⟨b, a, Ne.symm hab, Or.inl (key _ ?_)⟩
      rw [map_sub, he, he, weightCoord_inl, weightCoord_inl]
    · by_cases hab : a = b
      · subst hab
        refine Or.inl ⟨a, Or.inl (key _ ?_)⟩
        rw [map_nsmul, he, weightCoord_inl, weightCoord_inr]
        funext c
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply]
        split_ifs <;> rfl
      · refine Or.inr ⟨a, b, hab, Or.inr (Or.inr (key _ ?_))⟩
        rw [map_add, he, he, weightCoord_inl, weightCoord_inr, Pi.single_neg, sub_neg_eq_add]
    · by_cases hab : a = b
      · subst hab
        refine Or.inl ⟨a, Or.inr (key _ ?_)⟩
        rw [map_neg, map_nsmul, he, weightCoord_inl, weightCoord_inr]
        funext c
        simp only [Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply]
        split_ifs <;> rfl
      · refine Or.inr ⟨a, b, hab, Or.inr (Or.inl (key _ ?_))⟩
        rw [map_sub, map_neg, he, he, weightCoord_inl, weightCoord_inr, Pi.single_neg]
    · have hab : a ≠ b := fun h => hxy (congrArg Sum.inr h)
      refine Or.inr ⟨a, b, hab, Or.inl (key _ ?_)⟩
      rw [map_sub, he, he, weightCoord_inr, weightCoord_inr, Pi.single_neg, Pi.single_neg]
      abel
  · intro a
    rw [← hlongRoot]
    exact longRoot_mem_roots a
  · intro a b hab
    constructor
    · have h : e b - e a = diffRoot l k b a := by
        apply (GeneralLinear.characterCoordEquiv l k).injective
        rw [characterCoordEquiv_diffRoot, map_sub, he, he]
      rw [h]
      exact diffRoot_mem_roots (Ne.symm hab)
    · have h : -e a - e b = -sumRoot l k a b := by
        apply (GeneralLinear.characterCoordEquiv l k).injective
        rw [map_neg, characterCoordEquiv_sumRoot, map_sub, map_neg, he, he, neg_add']
      rw [h]
      exact neg_mem_roots (sumRoot_mem_roots hab)
  · intro r a hr
    apply (GeneralLinear.cocharacterCoordEquiv l k).injective
    rw [hν, cocharacterCoordEquiv_coroot_of_root_eq_longRoot hP (hr.trans (hlongRoot a).symm)]

end Field

/-- Almost simplicity of the split symplectic groups over algebraically closed fields gives
absolute almost simplicity of the standard symplectic group over every field. -/
theorem _root_.Langlands.GroupScheme.Symplectic.isAbsolutelyAlmostSimple_of_isAlgClosed
    (n : ℕ) (h : ∀ (k : Type u) [Field k] [IsAlgClosed k],
      IsAlmostSimple (groupScheme (Fin n) (CommRingCat.of k)))
    (K : Type u) [Field K] :
    IsAbsolutelyAlmostSimple (Symplectic.groupScheme K n) := by
  let b := toAlgebraicClosure K
  have hbar : IsAlmostSimple
      ((GroupScheme.baseChange b).obj (Symplectic.groupScheme K n)) :=
    IsAlmostSimple.of_iso
      ((GroupScheme.baseChange b).mapIso (comparisonIso K n).symm ≪≫
        baseChangeModelIso (Fin n) b)
      (h (AlgebraicClosure K))
  exact ⟨IsAlmostSimple.of_fieldExtension (K := AlgebraicClosure K) hbar, hbar⟩

/-- **Absolute almost simplicity.** For `n ≥ 2` the standard symplectic group `Sp_{2n}` over
every field is absolutely almost simple. -/
theorem _root_.Langlands.GroupScheme.Symplectic.isAbsolutelyAlmostSimple_groupScheme
    (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    IsAbsolutelyAlmostSimple (Symplectic.groupScheme K n) :=
  Symplectic.isAbsolutelyAlmostSimple_of_isAlgClosed n
    (fun _ _ _ => isAlmostSimple ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩) K

end SymplecticMatrix

end Langlands.GroupScheme
