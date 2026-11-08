import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation

/-! # Noncommuting root subgroups of a split reductive group

Two roots `β` and `β'` of a split maximal torus with `⟨β, β'^∨⟩ = -1`, for which no strict
combination `n β - m β'` is a root, have noncommuting root subgroups: a point of the
`β`-subgroup commuting with the `β'`- and `-β'`-subgroups would commute with the coroot
`β'^∨`, by the rank-one relation, while `β'^∨(u)` scales it by `u⁻¹`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RootPairNoncommutation

variable {k : Type u} [Field k]

section Commutation

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Two root subgroups commute on every test scheme when no strict positive combination of
their characters is zero or a root. -/
theorem commute_of_no_strict_combinations (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (c d : characterLattice S) (hc : c ≠ 0) (hd : d ≠ 0)
    (hcd : ∀ n m : ℕ, 0 < n → 0 < m → n • c + m • d ≠ 0 ∧ n • c + m • d ∉ roots i)
    {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup i c).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup i d).carrier Z) :
    Commute x y := by
  let action := AutomorphicAction.conjugation i
  have hbot : RelativeRoot.semigroupSubgroup action
      (RelativeRoot.semigroupSum (RelativeRoot.cyclicTail c 1)
        (RelativeRoot.cyclicTail d 1)) = ⊥ := by
    apply RelativeRoot.semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization
      action hS
    rintro χ ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨m, _, hm, rfl⟩, rfl⟩ hweight
    obtain ⟨hzero, hroot⟩ := hcd n m hn hm
    exact hroot ((RelativeRoot.mem_actionWeightSupport_conjugation_iff i hzero).mp hweight)
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail c 1)).carrier Z := by
    change x ∈ (RelativeRoot.weightFiltration action c 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hS i c hc]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail d 1)).carrier Z := by
    change y ∈ (RelativeRoot.weightFiltration action d 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hS i d hd]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G inferInstance inferInstance
    S hS action (RelativeRoot.cyclicTail c 1) (RelativeRoot.cyclicTail d 1) Z x y hx' hy'
  rw [hbot] at h
  have heq : x * y * x⁻¹ * y⁻¹ = 1 := h
  exact commutatorElement_eq_one_iff_commute.mp heq

end Commutation

section Lattice

variable {J X Y M : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup M]
  (P : RootPairing J ℤ X Y)

/-- If `⟨β, β'^∨⟩ = -1`, the reflection in `β'` sends `n β - m β'` to `n β + (n + m) β'`. -/
theorem reflection_strict_combination {r r' : J} (h : P.pairing r r' = -1) (n m : ℕ) :
    P.reflection r' (n • P.root r + m • (-P.root r')) =
      n • P.root r + (n + m) • P.root r' := by
  rw [map_add, map_nsmul, map_nsmul, map_neg, P.reflection_apply_root, P.reflection_apply_self,
    h, neg_neg, add_nsmul]
  simp only [neg_smul, one_smul, sub_neg_eq_add, nsmul_add]
  abel

/-- The pairing of a strict combination `n β - m β'` with `β'^∨` is `-(n + 2 m)`. -/
theorem pairing_strict_combination {r r' : J} (h : P.pairing r r' = -1) (n m : ℕ) :
    P.toLinearMap (n • P.root r + m • (-P.root r')) (P.coroot r') =
      -((n : ℤ) + 2 * m) := by
  rw [map_add, map_nsmul, map_nsmul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, P.root_coroot_eq_pairing,
    P.root_coroot_eq_pairing, h, P.pairing_same]
  simp only [nsmul_eq_mul]
  ring

/-- **Strict combinations of an obtuse pair restricting to the same character.** Let `f`
restrict characters, with `f β = f β' = a`, `⟨β, β'^∨⟩ = -1`, and no root restricting to a
multiple `n • a` with `n ≥ 3`. Then no strict combination `n β - m β'` is zero or a root. -/
theorem strict_combination_not_root (f : X →+ M) (a : M) {r r' : J}
    (hr : f (P.root r) = a) (hr' : f (P.root r') = a) (h : P.pairing r r' = -1)
    (hhigh : ∀ (s : J) (n : ℕ), 3 ≤ n → f (P.root s) ≠ n • a)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • P.root r + m • (-P.root r') ≠ 0 ∧
      n • P.root r + m • (-P.root r') ∉ Set.range P.root := by
  constructor
  · intro h0
    have hp := pairing_strict_combination P h n m
    rw [h0, map_zero, LinearMap.zero_apply] at hp
    omega
  · rintro ⟨s, hs⟩
    have hrefl := reflection_strict_combination P h n m
    rw [← hs, ← P.root_reflectionPerm] at hrefl
    apply hhigh (P.reflectionPerm r' s) (2 * n + m) (by omega)
    rw [hrefl, map_add, map_nsmul, map_nsmul, hr, hr', ← add_nsmul]
    congr 1
    ring

end Lattice

section CharacterValue

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A character takes the value `u ^ ⟨χ, ν⟩` at the point `ν(u)` of a cocharacter. -/
theorem cu_cocharacter (χ : characterLattice T) (ν : cocharacterLattice T)
    {Z : Over (Spec (CommRingCat.of k))} (u : Γ(Z.left, ⊤)ˣ) :
    RankOneRootCellRelation.cu χ
        ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom) =
      u ^ latticePairing T χ ν := by
  have hcomp : (CommGroupScheme.groupHom ν).hom.hom ≫ (CommGroupScheme.groupHom χ).hom.hom =
      (CommGroupScheme.groupHom (ν ≫ χ)).hom.hom := rfl
  rw [RankOneRootCellRelation.cu, Category.assoc, hcomp, eq_gmEndEquiv_zsmul k (ν ≫ χ),
    ← gmEndEquiv_symm_apply, gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply,
    latticePairing_apply]

end CharacterValue

section Noncommutation

/-- Solving `a b = c t d` for the middle factor `t`. -/
theorem solve_middle {H : Type*} [Group H] {a b c d t : H} (h : a * b = c * t * d) :
    t = c⁻¹ * (a * b) * d⁻¹ := by
  rw [h]
  group

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {J : Type u}

omit [IsAffineHom G.X.hom] in
/-- Two subgroup functors do not commute over the test scheme `Z`: some `Z`-point of `F`
does not commute with some `Z`-point of `F'`. -/
def NotCommuteOver (F F' : SubgroupFunctor G) (Z : Over (Spec (CommRingCat.of k))) : Prop :=
  ∃ x ∈ F.carrier Z, ∃ y ∈ F'.carrier Z, ¬ Commute x y

omit [IsAffineHom G.X.hom] in
/-- Points through a representing homomorphism belong to the represented subgroup. -/
theorem mem_of_isRepresentedBy {H : GroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {f : H ⟶ G} (hf : F.IsRepresentedBy f)
    {Z : Over (Spec (CommRingCat.of k))} (y : Z ⟶ H.X) : y ≫ f.hom.hom ∈ F.carrier Z := by
  rw [← hf.2]
  exact ⟨y, rfl⟩

/-- The root datum of a split maximal torus of a connected reductive group is reduced. -/
theorem isReduced (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P) :
    P.IsReduced := by
  refine ⟨fun r s hrs => ?_⟩
  have hr : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have hs : P.root s ∈ roots i := hP.2.1 ▸ Set.mem_range_self s
  exact rootReducedness k G hG T hT i hi _ hr _ hs hrs

/-- No positive multiple `n • β`, `n ≥ 2`, of a root `β` is a root. -/
theorem hasNoHigherRoots (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (r : J) : RelativeRoot.HasNoHigherRoots i (P.root r) := by
  let : P.IsReduced := isReduced hG hT hi hP
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T) := IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree toRat
  intro n hn
  let : n.AtLeastTwo := ⟨hn⟩
  rw [relativeRoots_eq_roots, ← hP.2.1]
  exact P.nsmul_notMem_range_root

/-- **Noncommuting root subgroups.** Let `β = P.root r` and `β' = P.root r'` be roots of a
split maximal torus of a connected reductive group with `⟨β, β'^∨⟩ = -1`, such that no strict
combination `n β - m β'` is zero or a root. Over every test scheme with a global function `c ≠ 0`
for which `1 + c` is a unit, the `β`- and `β'`-subgroups do not commute: the point
`x_β(1)` does not commute with some point of the `β'`-subgroup. -/
theorem exists_not_commute (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    {r r' : J} (hpair : P.pairing r r' = -1)
    (hstrict : ∀ n m : ℕ, 0 < n → 0 < m →
      n • P.root r + m • (-P.root r') ≠ 0 ∧ n • P.root r + m • (-P.root r') ∉ roots i)
    {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)) (hc : c ≠ 0) (hu : IsUnit (1 + c)) :
    NotCommuteOver (RelativeRoot.subgroup i (P.root r))
      (RelativeRoot.subgroup i (P.root r')) Z := by
  unfold NotCommuteOver
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨xp, -, hxpm, -, hxp, -, -⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi P hP r
  obtain ⟨yp, ym, hypm, hymm, hyp, hym, hrel⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi P hP r'
  have hroot (s : J) : P.root s ∈ roots i := hP.2.1 ▸ Set.mem_range_self s
  obtain ⟨s', hs'⟩ : -P.root r' ∈ Set.range P.root :=
    P.neg_mem_range_root_iff.mpr (Set.mem_range_self r')
  have hneg : -P.root r' ∈ roots i := hs' ▸ hroot s'
  have hnegHigh : RelativeRoot.HasNoHigherRoots i (-P.root r') :=
    hs' ▸ hasNoHigherRoots hG hT hi hP s'
  have hxrep := hxp.represents_root hG hT hi (hroot r) (hasNoHigherRoots hG hT hi hP r)
  have hyprep := hyp.represents_root hG hT hi (hroot r') (hasNoHigherRoots hG hT hi hP r')
  have hymrep := hym.represents_root hG hT hi hneg hnegHigh
  let x : Z ⟶ G.X := RootCell.pt 1 ≫ xp.hom.hom
  refine ⟨x, mem_of_isRepresentedBy hxrep _, ?_⟩
  by_contra! hall
  -- `x` commutes with the whole `-β'`-subgroup.
  have hm : ∀ b : Γ(Z.left, ⊤), Commute x (RootCell.pt b ≫ ym.hom.hom) := fun b =>
    commute_of_no_strict_combinations hT i (P.root r) (-P.root r') (hroot r).1 hneg.1 hstrict
      (mem_of_isRepresentedBy hxrep _) (mem_of_isRepresentedBy hymrep _)
  have hp : ∀ b : Γ(Z.left, ⊤), Commute x (RootCell.pt b ≫ yp.hom.hom) := fun b =>
    hall _ (mem_of_isRepresentedBy hyprep _)
  -- The rank-one relation for `β'` at `X = 1`, `Y = c`.
  let v : Γ(Z.left, ⊤)ˣ := hu.unit
  have hv : (v : Γ(Z.left, ⊤)) = 1 + c := hu.unit_spec
  let t : Z ⟶ T.X :=
    (Gm.pointsEquiv _ Z).symm v ≫ (CommGroupScheme.groupHom (P.coroot r')).hom.hom
  let w : Γ(Z.left, ⊤) := ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))
  have hrelZ := hrel Z (RootCell.pt 1) (RootCell.pt c) (RootCell.pt (w * 1))
    (RootCell.pt (w * c)) v (by rw [RootCell.crd_pt, RootCell.crd_pt, one_mul, hv])
    (by rw [RootCell.crd_pt, RootCell.crd_pt]) (by rw [RootCell.crd_pt, RootCell.crd_pt])
  change _ = _ * (t ≫ i.hom.hom) * _ at hrelZ
  have ht := solve_middle hrelZ
  have hcomm : Commute x (t ≫ i.hom.hom) := by
    rw [ht]
    exact (((hm _).inv_right.mul_right ((hp _).mul_right (hm _))).mul_right (hp _).inv_right)
  -- The torus point `β'^∨(v)` scales the `β`-coordinate by `v⁻¹`.
  have heq := hxp Z t 1
  have hval : VectorGroup.charValue (P.root r) Z t = ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
    rw [RankOneRootCellRelation.charValue_eq_cu, cu_cocharacter, ← hP.1,
      P.root_coroot_eq_pairing, hpair, zpow_neg_one]
  have hx1 : (t ≫ i.hom.hom) * x * (t ≫ i.hom.hom)⁻¹ = x := by
    rw [hcomm.eq.symm, mul_inv_cancel_right]
  change (t ≫ i.hom.hom) * x * (t ≫ i.hom.hom)⁻¹ = _ at heq
  rw [hx1, hval, mul_one] at heq
  have hpt : (RootCell.pt (1 : Γ(Z.left, ⊤)) : Z ⟶ (RootCell.Ga k).X) =
      RootCell.pt ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := (cancel_mono xp.hom.hom).1 heq
  have h1 := congrArg RootCell.crd hpt
  rw [RootCell.crd_pt, RootCell.crd_pt] at h1
  have hv1 : v = 1 := by
    exact inv_eq_one.mp (Units.val_eq_one.mp h1.symm)
  apply hc
  have := congrArg Units.val hv1
  rw [hv, Units.val_one] at this
  simpa using this

end Noncommutation

end Langlands.GroupScheme.RootPairNoncommutation
