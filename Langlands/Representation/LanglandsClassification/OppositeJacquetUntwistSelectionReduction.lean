import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwistSelectionStatement
import Langlands.Representation.LanglandsClassification.OppositeStandardExponentParameters
import Langlands.Representation.LanglandsClassification.OppositeStandardExponentRestrictionStatement
import Langlands.GroupScheme.Rational.LanglandsDecompositionStatement
import Langlands.Representation.Exponents.LeviJacquetFiniteLengthStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Geometry.Building.RealTorusInvariantForm
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Reduction of the tempered-untwist selection (Renard VII.4.2 (iii))

A closed temperedness criterion for a unitary untwist, in terms of ambient
opposite standard exponents, is stated. Together with restriction of exponents
to a larger standard Levi, Langlands' combinatorial lemma (V.3.18),
admissibility of irreducible representations and finite length of Jacquet
modules, it implies `OppositeJacquetUntwistSelectionStatement` by Renard's
maximal-positive-part argument.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

/-- Temperedness of a unitary untwist from its ambient exponents (Renard VII.2.1
on the standard Levi with the opposite ordering, as used in VII.4.2 (iii)). Let
`W` be a unitary untwist of an exponent `x` on the label `K`. Suppose that for
every exponent `y` on a label contained in `K` whose full real parameter differs
from that of `x` by an element of the real span of the roots in `K`, the
difference is a nonpositive combination of simple roots. Then the untwist is
tempered on the standard Levi of `K`. -/
def OppositeUntwistTemperedCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν),
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) →
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (x : OppositeStandardJacquetFamily.exponents i ν hG hi hν π)
        (W : OppositeStandardJacquetFamily.UnitaryUntwist i ν hG hi hν π x),
        (∀ y : OppositeStandardJacquetFamily.exponents i ν hG hi hν π,
          y.1.val ⊆ x.1.val →
          OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
              OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x ∈
            Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' x.1.val) →
          -(OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D y -
              OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x) ∈
            PointedCone.hull ℝ
              ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' simpleRelativeRoots i ν)) →
        (let S := StandardJacquetFamily.datum i ν hG hi hν x.1
         haveI := S.hl.isConnectedReductive.isAffineHom
         letI := leviPointTopology S.l S.hl
         haveI := leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
         haveI := leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
         IsNormalizedExponentTempered S.hl.isConnectedReductive W.untwist)

namespace UntwistSelection

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] (D : RelativeRootReflectionData i)
  {B : LinearMap.BilinForm ℝ (Vstar T)}

/-- Weyl invariance under the reflection of `α` gives the coroot formula
`⟨y, α̌⟩ B(α, α) = 2 B(y, α)`. -/
theorem pair_coroot_mul_form_root (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (y : Vstar T) :
    pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) *
        B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) =
      2 * B y ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h := hB.2.2 (QuotientGroup.mk (D.representative α)) y ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  rw [D.fullRealAction_representative, D.fullRealAction_representative, pair_tmul_tmul,
    D.pair_self] at h
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    one_mul] at h
  push_cast at h
  linear_combination h

include D in
/-- The real vector of an actual relative root is nonzero. -/
theorem tmul_root_ne_zero (α : relativeRoots i) :
    ((1 : ℝ) ⊗ₜ[ℤ] α.val : Vstar T) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z => pair T z ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) h
  simp only [pair_tmul_tmul, D.pair_self, map_zero, LinearMap.zero_apply] at h2
  norm_num at h2

omit [IsAffineHom G.X.hom] in
/-- The full real Weyl action fixes the restrictions of real rational
characters of `G`. -/
theorem relativeWeylFullRealAction_restrictReal (w : relativeWeylGroup i)
    (x : ℝ ⊗[ℤ] rationalCharacters G) :
    relativeWeylFullRealAction i w (rationalCharacterRestrictReal i x) =
      rationalCharacterRestrictReal i x := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change r ⊗ₜ[ℤ] relativeWeylLatticeAction i w (torusCharacterRestrict i χ) =
      r ⊗ₜ[ℤ] torusCharacterRestrict i χ
    rw [relativeWeylLatticeAction_torusCharacterRestrict]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restrictions of real rational characters of `G` annihilate every coroot. -/
theorem pair_coroot_eq_zero_of_mem_range {z : Vstar T}
    (hz : z ∈ LinearMap.range (rationalCharacterRestrictReal i)) (α : relativeRoots i) :
    pair T z ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 := by
  obtain ⟨x, rfl⟩ := hz
  have h := relativeWeylFullRealAction_restrictReal (QuotientGroup.mk (D.representative α)) x
  rw [D.fullRealAction_representative, sub_eq_self, smul_eq_zero] at h
  exact h.resolve_right (tmul_root_ne_zero D α)

/-- A vector annihilating the coroots of a set of roots is `B`-orthogonal to
their real span. -/
theorem form_eq_zero_of_pair_eq_zero (hB : IsWeylInvariantInnerProduct i B)
    {K : Set (characterLattice T)} (hK : K ⊆ relativeRoots i) {m z : Vstar T}
    (hm : ∀ α : relativeRoots i, α.1 ∈ K → pair T m ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hz : z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K)) :
    B m z = 0 := by
  have hle : Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) ≤
      LinearMap.ker (B m) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    have h := pair_coroot_mul_form_root D hB ⟨α, hK hα⟩ m
    rw [hm ⟨α, hK hα⟩ hα, zero_mul] at h
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    linarith
  exact hle hz

include D in
/-- Central directions are `B`-orthogonal to the real root span. -/
theorem form_eq_zero_of_mem_range_of_mem_rootSpan (hB : IsWeylInvariantInnerProduct i B)
    {z c : Vstar T} (hz : z ∈ LinearMap.range (rationalCharacterRestrictReal i))
    (hc : c ∈ relativeRootSpanReal i) : B z c = 0 :=
  form_eq_zero_of_pair_eq_zero D hB subset_rfl
    (fun α _ => pair_coroot_eq_zero_of_mem_range D hz α) hc

/-- Nonnegative combinations of simple roots pair nonnegatively with the
closed simple-coroot chamber. -/
theorem form_nonneg_of_mem_hull (ν : cocharacterLattice T)
    (hB : IsWeylInvariantInnerProduct i B)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν) {z c : Vstar T}
    (hz : z ∈ PointedCone.hull ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S))
    (hc : c ∈ closedCorootFace i ν D ∅) : 0 ≤ B z c := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hαr : α ∈ relativeRoots i := positiveRelativeRoots_subset_relativeRoots i ν
      (simpleRelativeRoots_subset_positive i ν (hS hα))
    have h := pair_coroot_mul_form_root D hB ⟨α, hαr⟩ c
    have hpos := hc.2.2 ⟨α, hαr⟩ (hS hα) (Set.notMem_empty α)
    have hnn := hB.2.1 _ (tmul_root_ne_zero D ⟨α, hαr⟩)
    have hm := mul_nonneg hpos hnn.le
    rw [hB.1]
    linarith
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply]
    linarith
  | smul t x _ hx =>
    change 0 ≤ B ((t : ℝ) • x) c
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg t.2 hx

/-- Renard's maximal-positive-part argument (VII.4.2 (iii)) in the ambient
real character space. Let `mG + mp` have central part `mG` and positive part
`mp` in the open coroot face of `K`, and let `vy` differ from it by an element
of the real span of `K`. If the `P_∅` decomposition of `vy` has a positive part
of `B`-length at most that of `mp`, then the difference is a nonpositive
combination of simple roots. -/
theorem neg_mem_hull_of_positivePart_le (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hB : IsWeylInvariantInnerProduct i B)
    {K Ky : Set (characterLattice T)} {mG mp vy yG yp ym : Vstar T}
    (hK : K ⊆ simpleRelativeRoots i ν)
    (hmG : mG ∈ LinearMap.range (rationalCharacterRestrictReal i))
    (hmp : mp ∈ openCorootFace i ν D K)
    (hdec : IsLanglandsDecomposition i ν D ∅ vy Ky yG yp ym)
    (hspan : vy - (mG + mp) ∈
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K))
    (hnorm : B yp yp ≤ B mp mp) :
    -(vy - (mG + mp)) ∈ PointedCone.hull ℝ
      ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' simpleRelativeRoots i ν) := by
  obtain ⟨-, hKyΔ, hvy, hyG, -, hym⟩ := hdec
  have hym' : -ym ∈ PointedCone.hull ℝ
      ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' Ky) := by
    obtain ⟨-, z, hz, hzspan⟩ := hym
    rw [Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at hzspan
    rw [Set.sdiff_empty] at hz
    rwa [hzspan]
  have hmpC : mp ∈ closedCorootFace i ν D ∅ := by
    refine ⟨hmp.1, fun α h => absurd h (Set.notMem_empty _), fun α hα _ => ?_⟩
    by_cases hαK : α.1 ∈ K
    · exact (hmp.2.1 α hαK).ge
    · exact (hmp.2.2 α hα hαK).le
  have hKr : K ⊆ relativeRoots i := fun α hα =>
    positiveRelativeRoots_subset_relativeRoots i ν
      (simpleRelativeRoots_subset_positive i ν (hK hα))
  have hKyr : Ky ⊆ relativeRoots i := fun α hα =>
    positiveRelativeRoots_subset_relativeRoots i ν
      (simpleRelativeRoots_subset_positive i ν (hKyΔ hα))
  have h1 := form_eq_zero_of_pair_eq_zero D hB hKr hmp.2.1 hspan
  have h2 := form_eq_zero_of_mem_range_of_mem_rootSpan D hB (sub_mem hyG hmG) hmp.1
  have h3 := form_nonneg_of_mem_hull D ν hB hKyΔ hym' hmpC
  have hyp_eq : yp = mp := by
    by_contra hne
    have hpos := hB.2.1 (yp - mp) (sub_ne_zero.mpr hne)
    have hdiff : vy - (mG + mp) = (yG - mG) + (yp - mp) + ym := by rw [hvy]; abel
    rw [hdiff] at h1
    simp only [map_add, map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply]
      at h1 h2 h3 hpos
    have s1 := hB.1 mp yG
    have s2 := hB.1 mp mG
    have s3 := hB.1 mp yp
    have s4 := hB.1 mp ym
    linarith
  rw [hyp_eq] at hvy
  have hdiff : vy - (mG + mp) = (yG - mG) + ym := by rw [hvy]; abel
  have hymspan : ym ∈ relativeRootSpanReal i := by
    have h' : -ym ∈ relativeRootSpanReal i :=
      Submodule.span_mono (Set.image_mono hKyr) (PointedCone.hull_le_span ℝ _ hym')
    simpa using neg_mem h'
  have hroot : yG - mG ∈ relativeRootSpanReal i := by
    have heq : yG - mG = (vy - (mG + mp)) - ym := by rw [hdiff]; abel
    rw [heq]
    exact sub_mem (Submodule.span_mono (Set.image_mono hKr) hspan) hymspan
  have hzero : yG - mG = 0 :=
    Submodule.disjoint_def.mp (relativeCharacterRootComplement k G hG T i hi).2.1 _ hroot
      (sub_mem hyG hmG)
  rw [hdiff, hzero, zero_add]
  exact Submodule.span_mono (Set.image_mono hKyΔ) hym'

end UntwistSelection

open OppositeStandardJacquetFamily in
/-- Renard VII.4.2 (iii), selection step: Langlands' combinatorial lemma,
admissibility of irreducible representations, finite length of Jacquet modules,
restriction of exponents and the temperedness criterion imply the selection of
a tempered unitary untwist with real part in the open chamber. -/
theorem oppositeJacquetUntwistSelection_of_inputs
    (hDec : LanglandsCombinatorialDecompositionStatement.{u})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hFL : LeviJacquetFiniteLengthStatement.{u, v})
    (hRes : OppositeStandardExponentRestrictionStatement.{u, v})
    (hTemp : OppositeUntwistTemperedCriterionStatement.{u, v}) :
    OppositeJacquetUntwistSelectionStatement.{u, v} := by
  classical
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D hi hν hmin π hπ
  have hadm : π.IsAdmissible := hAdm k G hG π hπ
  have hfl : π.HasFiniteLength := SmoothRep.hasFiniteLength_of_isIrreducible hπ
  have hnt : Nontrivial π := by
    have : IsSimpleModule (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hπ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G))
      π.representation.asModule
  -- The Weyl-invariant inner product.
  have : Fintype (relativeWeylGroup i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup i hi)
  let B := relativeWeylInvariantForm i hi.1.1
  have hB : IsWeylInvariantInnerProduct i B :=
    ⟨relativeWeylInvariantForm_symm i hi.1.1,
      fun x hx => relativeWeylInvariantForm_pos i hi.1.1 hx,
      fun w x y => relativeWeylInvariantForm_invariant i hi.1.1 w x y⟩
  -- Langlands decompositions of the full real parameters.
  have hdecJ : ∀ y : exponents i ν hG hi hν π, ∃ K mG mp mm,
      IsLanglandsDecomposition i ν D y.1.val (fullRealPart i ν hG hi hν π D y) K mG mp mm ∧
      ∀ K' mG' mp' mm', IsLanglandsDecomposition i ν D ∅
          (fullRealPart i ν hG hi hν π D y) K' mG' mp' mm' ↔
        K' = K ∧ mG' = mG ∧ mp' = mp ∧ mm' = mm := by
    intro y
    have hmem : fullRealPart i ν hG hi hν π D y ∈ corootAnnihilator i D y.1.val :=
      (mem_corootAnnihilator i D _ _).mpr
        (fun α hα => pair_fullRealPart_selectedCoroot i ν hG hi hν π D y α hα)
    have h := (hDec k G hG T i hi ν hν D B hB (component i ν hG hi hν y.1).A
      (StandardJacquetFamily.datum i ν hG hi hν y.1).P
      (StandardJacquetFamily.datum i ν hG hi hν y.1).M
      (StandardJacquetFamily.datum i ν hG hi hν y.1).p
      (StandardJacquetFamily.datum i ν hG hi hν y.1).l
      (component i ν hG hi hν y.1).a y.1.val
      (Additive.ofMul (component i ν hG hi hν y.1).g)
      (rootPresentation i ν hG hi hν y.1).isCompatible).2 _ hmem
    obtain ⟨⟨⟨K, mG, mp, mm⟩, hd, -⟩, hprops⟩ := h
    exact ⟨K, mG, mp, mm, hd, (hprops K mG mp mm hd).2.2.2.2.2.2⟩
  have hex : ∀ y : exponents i ν hG hi hν π, ∃ mp : Vstar T, ∃ K mG mm,
      IsLanglandsDecomposition i ν D ∅ (fullRealPart i ν hG hi hν π D y) K mG mp mm := by
    intro y
    obtain ⟨K, mG, mp, mm, -, hiff⟩ := hdecJ y
    exact ⟨mp, K, mG, mm, (hiff K mG mp mm).mpr ⟨rfl, rfl, rfl, rfl⟩⟩
  let pos : exponents i ν hG hi hν π → Vstar T := fun y => (hex y).choose
  have hpos : ∀ y, ∃ K mG mm,
      IsLanglandsDecomposition i ν D ∅ (fullRealPart i ν hG hi hν π D y) K mG (pos y) mm :=
    fun y => (hex y).choose_spec
  -- An exponent with maximal positive part.
  have := finite_exponents i ν hG hi hν π hadm hfl
  have := nonempty_exponents i ν hG hi hν π hadm hnt
  obtain ⟨x0, hx0⟩ := Finite.exists_max (fun y => B (pos y) (pos y))
  obtain ⟨K, mG, mp, mm, hd0, hiff0⟩ := hdecJ x0
  have hpos0 : pos x0 = mp := by
    obtain ⟨K', mG', mm', h'⟩ := hpos x0
    exact ((hiff0 K' mG' (pos x0) mm').mp h').2.2.1
  obtain ⟨hJK, hKΔ, hv0, hmG, hmp, hmm⟩ := hd0
  -- Restriction of `x0` to the standard Levi of `K`.
  have hmmspan : fullRealPart i ν hG hi hν π D x0 - (mG + mp) ∈
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) := by
    have heq : fullRealPart i ν hG hi hν π D x0 - (mG + mp) = -(-mm) := by rw [hv0]; abel
    rw [heq]
    refine neg_mem ?_
    obtain ⟨-, z, hz, hzspan⟩ := hmm
    have hz' : z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) :=
      Submodule.span_mono (Set.image_mono Set.sdiff_subset) (PointedCone.hull_le_span ℝ _ hz)
    have h2 : -mm - z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K) :=
      Submodule.span_mono (Set.image_mono hJK) hzspan
    have hsplit : -mm = (-mm - z) + z := by abel
    rw [hsplit]
    exact add_mem h2 hz'
  have hwK : ∀ α : relativeRoots i, α.1 ∈ K →
      pair T (mG + mp) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 := by
    intro α hα
    rw [map_add, LinearMap.add_apply,
      UntwistSelection.pair_coroot_eq_zero_of_mem_range D hmG α, hmp.2.1 α hα, add_zero]
  obtain ⟨x, hxK, hxv⟩ := hRes k G hG T i ν D hi hν hmin π hadm hfl x0 ⟨K, hKΔ⟩ (mG + mp)
    hJK hwK hmmspan
  have hxK' : x.1.val = K := congrArg Subtype.val hxK
  -- The unitary untwist.
  have hfinJ := hFL k G hG (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).P
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).M
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).U
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).p
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).l
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).r
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).hp
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).hl
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).hr
    (OppositeStandardJacquetFamily.datum i ν hG hi hν x.1).hmul π hfl
  refine ⟨x, irreducibleUnitaryUntwist i ν hG hi hν π x hadm hfinJ, ?_, ?_⟩
  · apply hTemp k G hG T i ν D hi hν hmin π x
    intro y _ hyspan
    obtain ⟨Ky, yG, ym, hdy⟩ := hpos y
    rw [hxK'] at hyspan
    rw [hxv] at hyspan ⊢
    have hnorm : B (pos y) (pos y) ≤ B mp mp := by
      have h := hx0 y
      rw [hpos0] at h
      exact h
    exact UntwistSelection.neg_mem_hull_of_positivePart_le D hG hi ν hB hKΔ hmG hmp hdy
      hyspan hnorm
  · refine ⟨fullRealPart i ν hG hi hν π D x, restrict_fullRealPart i ν hG hi hν π D x,
      fun α hα => pair_fullRealPart_selectedCoroot i ν hG hi hν π D x α hα, ?_⟩
    intro α hα hαx
    rw [hxK'] at hαx
    rw [hxv, map_add, LinearMap.add_apply,
      UntwistSelection.pair_coroot_eq_zero_of_mem_range D hmG α, zero_add]
    exact hmp.2.2 α hα hαx

end Langlands.Aubert.General.RepresentedParabolic
