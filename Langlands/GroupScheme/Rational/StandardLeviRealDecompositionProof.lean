import Langlands.GroupScheme.Rational.LanglandsCharacterRestriction
import Langlands.GroupScheme.Rational.StandardLeviLinearAlgebra
import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.Geometry.Building.RealTorusInvariantForm

/-! # Standard Levi decompositions on the actual real torus spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace
open Langlands.LinearAlgebra.StandardLevi

namespace StandardLevi

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (D : RelativeRootReflectionData i)

/-- The defining coroot equations are the left annihilator of their real span. -/
theorem corootAnnihilator_eq_leftAnn [(pair T).IsPerfPair]
    (J : Set (characterLattice T)) :
    corootAnnihilator i D J = leftAnn (pair T) (Submodule.span ℝ (D.realCorootsOf J)) := by
  ext x
  rw [mem_corootAnnihilator, mem_leftAnn]
  constructor
  · intro hx
    have hspan : Submodule.span ℝ (D.realCorootsOf J) ≤ (pair T x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨α, hα, rfl⟩
      exact hx α hα
    exact fun v hv => hspan hv
  · intro hx α hα
    exact hx _ (Submodule.subset_span ⟨α, hα, rfl⟩)

/-- The defining root equations are the right annihilator of their real span. -/
theorem rootAnnihilator_eq_rightAnn [(pair T).IsPerfPair]
    (J : Set (characterLattice T)) :
    rootAnnihilator T J = rightAnn (pair T)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) :=
  rootAnnihilator_eq_cocharacterAnnihilator J

/-- Every subset of actual roots has complementary root and coroot annihilators. -/
theorem complements (hT : IsSplitTorus T.toGrp)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (J : Set (characterLattice T)) (hJ : J ⊆ relativeRoots i) :
    IsCompl (corootAnnihilator i D J)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) ∧
    IsCompl (rootAnnihilator T J) (Submodule.span ℝ (D.realCorootsOf J)) ∧
    ((pair T).domRestrict₁₂ (corootAnnihilator i D J) (rootAnnihilator T J)).IsPerfPair := by
  let := hT.finite_realCharacterSpace
  let := isPerfPair_of_isSplitTorus hT
  have hE : IsCompl (corootAnnihilator i D J)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) := by
    rw [corootAnnihilator_eq_orthogonal i D B hB J hJ]
    exact (Langlands.LinearAlgebra.isCompl_orthogonal_of_positive B hB.1 hB.2.1 _).symm
  have hF := (rightAnn_isCompl (pair T) hE).symm
  rw [← rootAnnihilator_eq_rightAnn J, corootAnnihilator_eq_leftAnn,
    rightAnn_leftAnn] at hF
  refine ⟨hE, hF, ?_⟩
  rw [corootAnnihilator_eq_leftAnn, rootAnnihilator_eq_rightAnn]
  exact restricted_perfect (pair T)
    (by simpa only [← corootAnnihilator_eq_leftAnn] using hE)
    (by simpa only [← rootAnnihilator_eq_rightAnn] using hF)

/-- The cocharacter action of the supplied reflection is the actual coreflection. -/
theorem real_coreflection [(pair T).IsPerfPair] (α : relativeRoots i) (v : V T) :
    relativeWeylRealAction i (QuotientGroup.mk (D.representative α)) v =
      v - pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v • D.realCoroot α := by
  let s : relativeWeylGroup i := QuotientGroup.mk (D.representative α)
  have hr : pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (relativeWeylRealAction i s v) =
      -pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v := by
    have h := Langlands.GroupScheme.pair_relativeWeyl i s ((1 : ℝ) ⊗ₜ[ℤ] α.1) v
    rw [D.real_reflection_self i] at h
    simp only [map_neg, LinearMap.neg_apply] at h
    linarith
  apply (LinearMap.IsPerfPair.bijective_right (pair T)).injective
  apply LinearMap.ext
  intro x
  change pair T x (relativeWeylRealAction i s v) =
    pair T x (v - pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v • D.realCoroot α)
  have h := Langlands.GroupScheme.pair_relativeWeyl i s x v
  rw [D.real_reflection i] at h
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [hr] at h
  change pair T x (relativeWeylRealAction i s v) -
    pair T x (D.realCoroot α) * -pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) v = pair T x v at h
  linarith

/-- Every invariant cocharacter form makes root annihilators orthogonal to coroot spans. -/
theorem cocharacter_orthogonal [(pair T).IsPerfPair]
    (C : LinearMap.BilinForm ℝ (V T)) (hC : IsWeylInvariantCocharacterInnerProduct i C)
    (K : Set (characterLattice T)) {v : V T} (hv : v ∈ rootAnnihilator T K)
    {w : V T} (hw : w ∈ Submodule.span ℝ (D.realCorootsOf K)) : C v w = 0 := by
  have hspan : Submodule.span ℝ (D.realCorootsOf K) ≤ (C v).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    have hfix : relativeWeylRealAction i (QuotientGroup.mk (D.representative α)) v = v := by
      rw [real_coreflection i D, ← eval_eq_pair, (mem_rootAnnihilator K v).mp hv _ hα,
        zero_smul, sub_zero]
    have hneg : relativeWeylRealAction i (QuotientGroup.mk (D.representative α))
        (D.realCoroot α) = -D.realCoroot α := by
      rw [real_coreflection i D, D.pair_root_realCoroot]
      module
    have h := hC.2.2 (QuotientGroup.mk (D.representative α)) v (D.realCoroot α)
    rw [hfix, hneg, map_neg] at h
    change C v (D.realCoroot α) = 0
    linarith
  exact hspan hw

/-- Simple roots span the full real root space by scalar extension of their rational span. -/
theorem simpleRootSpan_eq (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) :
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) ''
      simpleRelativeRoots i ν) = relativeRootSpanReal i := by
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i := by
    intro α hα
    obtain ⟨n, hn⟩ := hG.exists_weylAction_eq_neg i hi α hα
    rw [← hn]
    exact weylAction_mapsTo_relativeRoots i n hα
  rw [← Langlands.LinearAlgebra.map_ratSpan_baseChange,
    ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν hneg,
    map_relativeRootSpan_baseChange]

/-- At the full simple set, the two annihilators and the simple coroot span are intrinsic. -/
theorem full_simple (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B) :
    corootAnnihilator i D (simpleRelativeRoots i ν) =
      LinearMap.range (rationalCharacterRestrictReal i) ∧
    rootAnnihilator T (simpleRelativeRoots i ν) = relativeCentralDirections i ∧
    Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) =
      cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) := by
  let := isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1
  have hspan := simpleRootSpan_eq i hG hi ν hν
  have hE := (complements i D hi.isSplitSubtorus.1 B hB _
    (simpleRelativeRoots_subset_relativeRoots i ν)).1
  rw [hspan] at hE
  have hR := (relativeCharacterRootComplement k G hG T i hi).2.symm
  have hle : (rationalCharacterRestrictReal i).range ≤
      corootAnnihilator i D (simpleRelativeRoots i ν) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_corootAnnihilator]
    intro α _
    exact D.restrictedCharacter_coroot i B hB x α
  have hfull : corootAnnihilator i D (simpleRelativeRoots i ν) =
      (rationalCharacterRestrictReal i).range := by
    apply (eq_of_le_of_inf_le_of_sup_le (z := relativeRootSpanReal i) hle ?_ ?_).symm
    · rw [hE.inf_eq_bot, hR.inf_eq_bot]
    · rw [hE.sup_eq_top, hR.sup_eq_top]
  refine ⟨hfull, ?_, ?_⟩
  · rw [rootAnnihilator_eq_cocharacterAnnihilator, hspan,
      relativeCentralDirections, rootAnnihilator_eq_cocharacterAnnihilator]
    rfl
  · change Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) =
      rightAnn (pair T) (LinearMap.range (rationalCharacterRestrictReal i))
    rw [← hfull, corootAnnihilator_eq_leftAnn, rightAnn_leftAnn]

/-- All nested decomposition and projection clauses follow from the complements. -/
theorem nested (hT : IsSplitTorus T.toGrp)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (J K : Set (characterLattice T)) (hJK : J ⊆ K) (hK : K ⊆ relativeRoots i) :
    IsCompl (corootAnnihilator i D J)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) ∧
    IsCompl (rootAnnihilator T J) (Submodule.span ℝ (D.realCorootsOf J)) ∧
    ((pair T).domRestrict₁₂ (corootAnnihilator i D J) (rootAnnihilator T J)).IsPerfPair ∧
    Disjoint (corootAnnihilator i D K) (D.leviRootSpace J K) ∧
    corootAnnihilator i D K ⊔ D.leviRootSpace J K = corootAnnihilator i D J ∧
    D.leviRootSpace J K = Submodule.span ℝ (D.projectedRoots J (K \ J)) ∧
    Disjoint (rootAnnihilator T K) (D.leviCorootSpace J K) ∧
    rootAnnihilator T K ⊔ D.leviCorootSpace J K = rootAnnihilator T J ∧
    D.leviCorootSpace J K = Submodule.span ℝ (D.projectedCoroots J (K \ J)) ∧
    (∀ B' : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B' →
      ∀ x ∈ corootAnnihilator i D K, ∀ y ∈ D.leviRootSpace J K, B' x y = 0) ∧
    ∀ C : LinearMap.BilinForm ℝ (V T), IsWeylInvariantCocharacterInnerProduct i C →
      ∀ v ∈ rootAnnihilator T K, ∀ w ∈ D.leviCorootSpace J K, C v w = 0 := by
  let := isPerfPair_of_isSplitTorus hT
  have hj := complements i D hT B hB J (hJK.trans hK)
  have hk := complements i D hT B hB K hK
  have ha : corootAnnihilator i D K ≤ corootAnnihilator i D J := by
    intro x hx
    rw [mem_corootAnnihilator] at hx ⊢
    exact fun α hα => hx α (hJK hα)
  have hb : rootAnnihilator T K ≤ rootAnnihilator T J := by
    intro v hv
    rw [mem_rootAnnihilator] at hv ⊢
    exact fun α hα => hv α (hJK hα)
  have hroot := nested_complement hk.1 ha
  have hcoroot := nested_complement hk.2.1 hb
  refine ⟨hj.1, hj.2.1, hj.2.2, hroot.1, hroot.2, ?_, hcoroot.1, hcoroot.2, ?_, ?_, ?_⟩
  · exact projected_span (fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) hJK hj.1
  · have hp := projected_span D.realCoroot
      (J := {α : relativeRoots i | α.1 ∈ J}) (K := {α : relativeRoots i | α.1 ∈ K})
      (fun _ hα => hJK hα) hj.2.1
    change rootAnnihilator T J ⊓ Submodule.span ℝ
      (D.realCoroot '' {α : relativeRoots i | α.1 ∈ K}) = _
    rw [hp]
    congr 1
    ext v
    constructor
    · rintro ⟨hv, α, hα, hd⟩
      exact ⟨hv, D.realCoroot α, ⟨α, hα, rfl⟩, hd⟩
    · rintro ⟨hv, w, ⟨α, hα, rfl⟩, hd⟩
      exact ⟨hv, α, hα, hd⟩
  · intro B' hB' x hx y hy
    rw [corootAnnihilator_eq_orthogonal i D B' hB' K hK] at hx
    rw [hB'.1]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y hy.2
  · intro C hC v hv w hw
    exact cocharacter_orthogonal i D C hC K hv hw.2

end StandardLevi

/-- Renard V.3.13, with the corrected nested Levi pieces in the published target. -/
theorem standardLeviRealDecomposition : StandardLeviRealDecompositionStatement.{u} := by
  classical
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν D
  let hT := hi.isSplitSubtorus.1
  let : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  let B := relativeWeylInvariantForm i hT
  have hB : IsWeylInvariantInnerProduct i B :=
    ⟨relativeWeylInvariantForm_symm i hT, fun _ hx => relativeWeylInvariantForm_pos i hT hx,
      relativeWeylInvariantForm_invariant i hT⟩
  have hf := StandardLevi.full_simple i D hG hi ν hν B hB
  refine ⟨hf.1, hf.2.1, hf.2.2, ?_⟩
  intro J K hJK hK
  exact StandardLevi.nested i D hT B hB J K hJK
    (hK.trans (simpleRelativeRoots_subset_relativeRoots i ν))

end Langlands.GroupScheme
