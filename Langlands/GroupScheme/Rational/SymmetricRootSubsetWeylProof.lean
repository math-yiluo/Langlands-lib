import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.RelativeRealCorootProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Mathlib.LinearAlgebra.RootSystem.Chain

/-! # Symmetric closed root subsets and their Weyl groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

private lemma add_nsmul_mem_of_steps {M : Type*} [AddCommGroup M]
    {A Y : Set M}
    (hadd : ∀ x ∈ Y, ∀ y ∈ Y, x + y ∈ A → x + y ∈ Y)
    {x a : M} (hx : x ∈ Y) (ha : a ∈ Y) (n : ℕ)
    (hs : ∀ m ≤ n, x + m • a ∈ A) :
    x + n • a ∈ Y := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have hn := ih (fun m hm => hs m (by omega))
    have hr : (x + n • a) + a ∈ A := by
      simpa only [succ_nsmul, add_assoc] using hs (n + 1) le_rfl
    simpa only [succ_nsmul, add_assoc] using hadd _ hn _ ha hr

private lemma reflection_root_mem_of_closed_symmetric
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic]
    {Y : Set M}
    (hadd : ∀ x ∈ Y, ∀ y ∈ Y, x + y ∈ Set.range P.root → x + y ∈ Y)
    (hneg : ∀ x ∈ Y, -x ∈ Y)
    {a b : ι} (ha : P.root a ∈ Y) (hb : P.root b ∈ Y) :
    P.reflection a (P.root b) ∈ Y := by
  classical
  by_cases hli : LinearIndependent ℝ ![P.root a, P.root b]
  · have hr : P.root b - P.pairingIn ℤ b a • P.root a ∈ Set.range P.root := by
      rw [← P.reflection_apply_root' ℤ]
      exact ⟨P.reflectionPerm a b, P.root_reflectionPerm a b⟩
    have hbound := (P.root_sub_zsmul_mem_range_iff hli).mp hr
    rcases (P.pairingIn ℤ b a).eq_nat_or_neg with ⟨n, hz | hz⟩
    · rw [P.reflection_apply_root' ℤ, hz, natCast_zsmul, sub_eq_add_neg, ← smul_neg]
      apply add_nsmul_mem_of_steps hadd hb (hneg _ ha) n
      intro m hm
      rw [smul_neg, ← sub_eq_add_neg, ← natCast_zsmul]
      apply (P.root_sub_zsmul_mem_range_iff hli).mpr
      simp only [Set.mem_Icc] at hbound ⊢
      rw [hz] at hbound
      omega
    · rw [P.reflection_apply_root' ℤ, hz, neg_smul, sub_neg_eq_add, natCast_zsmul]
      apply add_nsmul_mem_of_steps hadd hb ha n
      intro m hm
      rw [← natCast_zsmul]
      apply (P.root_add_zsmul_mem_range_iff hli).mpr
      simp only [Set.mem_Icc] at hbound ⊢
      rw [hz] at hbound
      omega
  · have heq : P.reflection a (P.root b) = -P.root b := by
      rw [P.reflection_apply_root,
        P.pairing_smul_root_eq_of_not_linearIndependent hli, two_smul]
      abel
    rw [heq]
    exact hneg _ hb

open RealTorusSpace

private lemma reflection_mapsTo_of_real_pairing
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp)
    {R X : Set (characterLattice T)} [Finite R]
    (hX : IsSymmetricRootSubset R X)
    {N : Type*} [AddCommGroup N] [Module ℝ N]
    (P : RootPairing R ℝ (relativeRootSpanReal i) N)
    [P.IsRootSystem] [P.IsCrystallographic]
    (hroot : ∀ a, (P.root a : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] a.1)
    (hambient : ∀ w : relativeWeylGroup i,
      Set.MapsTo (relativeWeylCharacterAction i w) R R)
    (a : R) (ha : a.1 ∈ X) (w : relativeWeylGroup i)
    (hw : IsRootReflection i w a.1) :
    Set.MapsTo (relativeWeylCharacterAction i w) X X := by
  classical
  obtain ⟨c, hc, hact⟩ := hw
  have htensor (χ : characterLattice T) (n : ℤ) :
      (1 : ℝ) ⊗ₜ[ℤ] (n • χ) = (n : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
    rw [TensorProduct.tmul_smul, Int.cast_smul_eq_zsmul]
  let f : Module.Dual ℝ (relativeRootSpanReal i) :=
    ((pair T).flip ((1 : ℝ) ⊗ₜ[ℤ] c)).comp (relativeRootSpanReal i).subtype
  have hf (b : R) : f (P.root b) = (latticePairing T b.1 c : ℝ) := by
    simp only [f, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.flip_apply, hroot, pair_tmul_tmul, one_mul]
  have hpre (b : R) :
      (Module.preReflection (P.root a) f (P.root b) : Vstar T) =
        (1 : ℝ) ⊗ₜ[ℤ] relativeWeylCharacterAction i w b.1 := by
    rw [Module.preReflection_apply]
    change (P.root b : Vstar T) - f (P.root b) • (P.root a : Vstar T) = _
    rw [hf, hroot, hroot, hact, TensorProduct.tmul_sub, htensor]
  have hmaps : Set.MapsTo (Module.preReflection (P.root a) f)
      (Set.range P.root) (Set.range P.root) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨⟨relativeWeylCharacterAction i w b.1, hambient w b.2⟩, ?_⟩
    apply Subtype.ext
    rw [hroot, hpre]
  have hfg : f = P.coroot' a :=
    Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range P.root)
      RootPairing.IsRootSystem.span_root_eq_top
      (by rw [hf, hc]; norm_num) hmaps (P.coroot_root_two a)
      (P.mapsTo_reflection_root a)
  have hreflect (b : R) :
      (P.reflection a (P.root b) : Vstar T) =
        (1 : ℝ) ⊗ₜ[ℤ] relativeWeylCharacterAction i w b.1 := by
    change (Module.preReflection (P.root a) (P.coroot' a) (P.root b) : Vstar T) = _
    rw [← hfg]
    exact hpre b
  let Y : Set (relativeRootSpanReal i) :=
    {x | ∃ χ ∈ X, (x : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] χ}
  have hadd : ∀ x ∈ Y, ∀ y ∈ Y, x + y ∈ Set.range P.root → x + y ∈ Y := by
    rintro x ⟨χ, hχ, hx⟩ y ⟨ψ, hψ, hy⟩ ⟨b, hb⟩
    have heq : b.1 = χ + ψ := by
      apply RelativeRootSystem.character_realTensor_injective hT
      change (1 : ℝ) ⊗ₜ[ℤ] b.1 = (1 : ℝ) ⊗ₜ[ℤ] (χ + ψ)
      rw [← hroot b, hb]
      change (x : Vstar T) + (y : Vstar T) = _
      rw [hx, hy, TensorProduct.tmul_add]
    refine ⟨χ + ψ, hX.1.2 χ hχ ψ hψ (heq ▸ b.2), ?_⟩
    change (x : Vstar T) + (y : Vstar T) = _
    rw [hx, hy, TensorProduct.tmul_add]
  have hneg : ∀ x ∈ Y, -x ∈ Y := by
    rintro x ⟨χ, hχ, hx⟩
    refine ⟨-χ, hX.2 χ hχ, ?_⟩
    change -(x : Vstar T) = _
    rw [hx, TensorProduct.tmul_neg]
  intro χ hχ
  let b : R := ⟨χ, hX.1.1 hχ⟩
  have hr := reflection_root_mem_of_closed_symmetric P hadd hneg
    (show P.root a ∈ Y from ⟨a.1, ha, hroot a⟩)
    (show P.root b ∈ Y from ⟨χ, hχ, hroot b⟩)
  obtain ⟨ψ, hψ, hψeq⟩ := hr
  have heq : relativeWeylCharacterAction i w χ = ψ :=
    RelativeRootSystem.character_realTensor_injective hT ((hreflect b).symm.trans hψeq)
  exact heq ▸ hψ

/-- Renard V.4.2: every symmetric closed subset in either relative-root ambient
set is preserved by its root reflections and by the subgroup they generate. -/
theorem symmetricRootSubsetWeyl : SymmetricRootSubsetWeylStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro R hR X hX
  classical
  have hT := hi.isSplitSubtorus.1
  obtain ⟨D, -⟩ := relativeRootReflectionExistence k G hG T i hi
  obtain ⟨-, -, -, -, -, -, hfinite, hfull, hindiv⟩ :=
    relativeRealCoroot k G hG T i hi D
  let := hfinite
  have hRsub : R ⊆ relativeRoots i := by
    rcases hR with rfl | rfl
    · exact subset_rfl
    · exact fun _ h => h.1
  have hambient : ∀ w : relativeWeylGroup i,
      Set.MapsTo (relativeWeylCharacterAction i w) R R := by
    intro w
    refine Quotient.inductionOn w ?_
    intro n
    rw [relativeWeylCharacterAction_mk]
    rcases hR with rfl | rfl
    · exact weylAction_mapsTo_relativeRoots i n
    · exact fun χ hχ => RelativeRootSystem.weylAction_indivisible n ⟨χ, hχ⟩
  have hmaps : ∀ β ∈ X, ∀ w : relativeWeylGroup i, IsRootReflection i w β →
      Set.MapsTo (relativeWeylCharacterAction i w) X X := by
    intro β hβ w hw
    rcases hR with rfl | rfl
    · obtain ⟨P, hP, hC, hroot, -⟩ := hfull
      let := hP
      let := hC
      exact reflection_mapsTo_of_real_pairing i hT hX P hroot hambient
        ⟨β, hX.1.1 hβ⟩ hβ w hw
    · have hf : (RelativeRoot.indivisibleRoots i).Finite :=
        (Set.toFinite (relativeRoots i)).subset (fun _ h => h.1)
      let := hf.to_subtype
      obtain ⟨P, hP, hC, -, hroot, -⟩ := hindiv
      let := hP
      let := hC
      exact reflection_mapsTo_of_real_pairing i hT hX P hroot hambient
        ⟨β, hX.1.1 hβ⟩ hβ w hw
  have hpres : ∀ β ∈ X, ∀ w : relativeWeylGroup i, IsRootReflection i w β →
      relativeWeylCharacterAction i w '' X = X := by
    intro β hβ w hw
    have hm := hmaps β hβ w hw
    obtain ⟨c, hc, hact⟩ := hw
    have hinv : Function.Involutive (relativeWeylCharacterAction i w) := by
      intro χ
      simpa only [Module.preReflection_apply, LinearMap.flip_apply, ← hact] using
        (Module.involutive_preReflection
          (x := β) (f := (latticePairing T).flip c) hc χ)
    apply Set.Subset.antisymm (Set.image_subset_iff.mpr hm)
    intro χ hχ
    exact ⟨relativeWeylCharacterAction i w χ, hm hχ, hinv χ⟩
  refine ⟨?_, hpres, ?_⟩
  · intro β hβ
    let a : relativeRoots i := ⟨β, hRsub (hX.1.1 hβ)⟩
    refine ⟨QuotientGroup.mk (D.representative a), D.coroot a, D.pair_self a, ?_⟩
    intro χ
    rw [relativeWeylCharacterAction_mk]
    exact D.action a χ
  · intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, hr⟩ := hw
      exact hpres β hβ w hr
    | one => simp
    | mul w v _ _ hw hv =>
      rw [map_mul]
      change (fun χ => relativeWeylCharacterAction i w
        (relativeWeylCharacterAction i v χ)) '' X = X
      rw [← Set.image_image, hv, hw]
    | inv w _ hw =>
      have h := congrArg (fun Y => relativeWeylCharacterAction i w⁻¹ '' Y) hw
      have hcomp :
          (fun χ => relativeWeylCharacterAction i w⁻¹
            (relativeWeylCharacterAction i w χ)) = id := by
        funext χ
        change relativeWeylCharacterAction i w⁻¹
          (relativeWeylCharacterAction i w χ) = χ
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [Set.image_image, hcomp, Set.image_id] at h
      exact h.symm

end Langlands.GroupScheme
