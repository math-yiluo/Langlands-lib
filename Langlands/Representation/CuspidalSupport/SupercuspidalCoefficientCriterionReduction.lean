import Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionStatement
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.Aubert.General.RationalCuspidalCoefficientCompactSupport
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.Plancherel.RationalNormKernelSmoothDual
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Renard VI.2.1, (a) ⇔ (b): the reverse implication and a structural reduction

`isSupercuspidal_of_coefficients_compactModCenter` proves (b) ⇒ (a) without
structural premises. `coefficients_compactModCenter_of_isSupercuspidal` proves
(a) ⇒ (b) from `JointSpecialCompactBasisExistenceStatement`, and
`supercuspidalCoefficientCriterionReduction` reduces the whole published
`SupercuspidalCoefficientCriterionStatement` to that one statement.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v w

open GroupScheme RationalPointFamily

section Group

variable {Γ : Type w} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- A set that is compact modulo the centre meets an open subgroup `H` inside a
compact set, provided `H` meets the centre in a compact set. -/
theorem exists_isCompact_superset_mul_center_inter
    (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (hHZ : IsCompact ((H ⊓ Subgroup.center Γ : Subgroup Γ) : Set Γ))
    (C : Set Γ) (hC : IsCompact C) :
    ∃ K : Set Γ, IsCompact K ∧
      (C * (Subgroup.center Γ : Set Γ)) ∩ (H : Set Γ) ⊆ K := by
  classical
  have hopen : ∀ c : Γ, IsOpen {x : Γ | x * c⁻¹ ∈ H} := fun c =>
    hH.preimage (continuous_id.mul continuous_const)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : Γ => {x : Γ | x * c⁻¹ ∈ H}) hopen
    (fun c _ => Set.mem_iUnion.mpr ⟨c, by simp [H.one_mem]⟩)
  let zc : Γ → Γ := fun c =>
    if hc : ∃ z ∈ Subgroup.center Γ, c * z ∈ H then hc.choose else 1
  have hzc : ∀ c, (∃ z ∈ Subgroup.center Γ, c * z ∈ H) →
      zc c ∈ Subgroup.center Γ ∧ c * zc c ∈ H := by
    intro c hc
    simp only [zc, hc, dite_true]
    exact hc.choose_spec
  let Zt : Set Γ := zc '' (t : Set Γ)
  have hZt : Zt.Finite := t.finite_toSet.image zc
  refine ⟨C * Zt * ((H ⊓ Subgroup.center Γ : Subgroup Γ) : Set Γ),
    (hC.mul hZt.isCompact).mul hHZ, ?_⟩
  rintro x ⟨hxCZ, hx⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := Set.mem_mul.mp hxCZ
  have hct := ht hc
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hct
  obtain ⟨c', hc't, hcc'⟩ := hct
  have hc'z : c' * z ∈ H := by
    have hmem : (c * c'⁻¹)⁻¹ * (c * z) ∈ H := H.mul_mem (H.inv_mem hcc') hx
    have heq : (c * c'⁻¹)⁻¹ * (c * z) = c' * z := by group
    rwa [heq] at hmem
  obtain ⟨hzc1, hzc2⟩ := hzc c' ⟨z, hz, hc'z⟩
  have hw : (zc c')⁻¹ * z ∈ (H ⊓ Subgroup.center Γ : Subgroup Γ) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hmem : (c' * zc c')⁻¹ * (c' * z) ∈ H := H.mul_mem (H.inv_mem hzc2) hc'z
      have heq : (c' * zc c')⁻¹ * (c' * z) = (zc c')⁻¹ * z := by group
      rwa [heq] at hmem
    · exact (Subgroup.center Γ).mul_mem ((Subgroup.center Γ).inv_mem hzc1) hz
  refine Set.mem_mul.mpr ⟨c * zc c', Set.mem_mul.mpr ⟨c, hc, zc c', ⟨c', hc't, rfl⟩, rfl⟩,
    (zc c')⁻¹ * z, hw, ?_⟩
  group

end Group

section Rational

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Renard VI.2.1, (b) ⇒ (c): coefficients compactly supported modulo the
centre give compact coefficients on the common norm kernel `⁰G`. -/
theorem compactNormKernelRestriction_of_coefficients_compactModCenter
    (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (∀ (w : A) (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ →
          ∃ C : Set (rationalPoints G), IsCompact C ∧
            Function.support (matrixCoefficient A.representation ℓ w) ⊆
              C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G))) →
      HasCompactNormKernelRestriction A := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  intro A hb v ℓ hℓ
  have hℓG : IsSmoothVector A.representation.dual ℓ :=
    (Plancherel.isSmoothVector_dual_rationalNormKernel_iff G A.representation ℓ).mp hℓ
  obtain ⟨C, hC, hsupp⟩ := hb v ℓ hℓG
  obtain ⟨K, hK, hCK⟩ := exists_isCompact_superset_mul_center_inter
    (Plancherel.rationalCommonNormKernel G)
    (Plancherel.isOpen_rationalCommonNormKernel G)
    (Plancherel.isCompact_rationalCommonNormKernel_inf_center G hG) C hC
  have hHc : IsClosed (Plancherel.rationalCommonNormKernel G : Set (rationalPoints G)) :=
    Plancherel.isClosed_rationalCommonNormKernel G
  apply HasCompactSupport.of_support_subset_isCompact
    (hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  intro h hh
  exact hCK ⟨hsupp hh, h.property⟩

/-- Renard VI.2.1, (b) ⇒ (a), unconditionally: coefficients compactly supported
modulo the centre imply represented supercuspidality. -/
theorem isSupercuspidal_of_coefficients_compactModCenter
    (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (∀ (w : A) (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ →
          ∃ C : Set (rationalPoints G), IsCompact C ∧
            Function.support (matrixCoefficient A.representation ℓ w) ⊆
              C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G))) →
      IsSupercuspidal A := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ A hb
  exact isSupercuspidal_of_compactRestriction parabolicDynamic smoothMaximalSplitTorusConjugacy
    standardCocharacter relativeRootSystem hG A
    (compactNormKernelRestriction_of_coefficients_compactModCenter hG A hb)

/-- Renard VI.2.1, (a) ⇒ (b), from the joint geometric existence statement:
every coefficient of a represented supercuspidal representation against a
smooth dual vector is supported in `C · Z` for a compact `C`. -/
theorem coefficients_compactModCenter_of_isSupercuspidal
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)), IsSupercuspidal A →
        ∀ (w : A) (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ →
          ∃ C : Set (rationalPoints G), IsCompact C ∧
            Function.support (matrixCoefficient A.representation ℓ w) ⊆
              C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G)) := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ A hA w ℓ hℓ
  classical
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := relativeRootSystem k G hG T i hi
  obtain ⟨D, x, Z, j, s, -, hrep, hsj, hchar, -, hprops, -, -, hcomp, -, -, hbasis⟩ :=
    hJoint k G hG T i hi ν hν
  have hcover := rationalPositiveCartanCover k G T i ν D x Z j s hchar hrep hsj hcomp
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hcusp := isCuspidal_of_all_represented_parabolics_of_standardCocharacter
    i ν standardCocharacter hG hi hν hRoots hU A hA
  let K0 := D.specialCompactSubgroup x
  have hK0 : IsCompact (K0 : Set (rationalPoints G)) := hprops.2.1.1
  obtain ⟨F₀, hF₀⟩ := hcover
  let Fset : Set (rationalPoints G) := Subtype.val '' (F₀ : Set (centralizerPoints i))
  have hfinite : Fset.Finite := F₀.finite_toSet.image _
  have hcentral : Fset ⊆ centralizerPoints i := by
    rintro _ ⟨f, _, rfl⟩
    exact f.property
  obtain ⟨B, hB⟩ := exists_rational_compact_translate_pairing_bound i ν hG hi hν
    standardCocharacter hRoots hU hbasis hfinite hcentral (K0 : Set (rationalPoints G)) hK0
    A hcusp ℓ hℓ w
  have hdet := cartanDetectionModulo_center i ν hi.isSplitSubtorus.1 hν
    (fun _ hα => hRoots.neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα)
  let Zc := Subgroup.center (rationalPoints G)
  let e : cocharacterLattice T → rationalPoints G ⧸ Zc :=
    fun y => QuotientGroup.mk' Zc (uniformizerPowers i (.ofAdd y))
  let box : Set (cocharacterLattice T) :=
    {y | ∀ β, 0 ≤ simpleRootPairing i ν β y ∧ simpleRootPairing i ν β y ≤ B}
  have hfin : (e '' box).Finite := hdet.finite_bounded_image 0 B
  have hsurj : Function.Surjective (QuotientGroup.mk' Zc) := QuotientGroup.mk'_surjective Zc
  let T0 : Set (rationalPoints G) := Function.surjInv hsurj '' (e '' box)
  have hT0 : T0.Finite := hfin.image _
  refine ⟨(K0 : Set (rationalPoints G)) * Fset * T0 * (K0 : Set (rationalPoints G)),
    ((hK0.mul hfinite.isCompact).mul hT0.isCompact).mul hK0, ?_⟩
  intro g hg
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hrep⟩ := hF₀ g
  obtain ⟨y, rfl, hy⟩ := exists_cocharacter_of_mem_CAplus i ν ha
  have he : rationalPoints.map i (CocharacterUniformizer.latticeSection k T (.ofAdd y)) =
      uniformizerPowers i (.ofAdd y) := rfl
  rw [he] at hrep
  have hyT : uniformizerPowers i (.ofAdd y) ∈ torusPoints i :=
    (mem_torusPoints i _).mpr ⟨CocharacterUniformizer.latticeSection k T (.ofAdd y), rfl⟩
  have hcomm : (f : rationalPoints G) * uniformizerPowers i (.ofAdd y) =
      uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) :=
    (centralizerPoints_le_pointCentralizer i f.property _ hyT).symm
  have hrep' : g = k₁ * uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) * k₂ := by
    rw [mul_assoc k₁, hcomm, ← mul_assoc] at hrep
    exact hrep
  have hne : matrixCoefficient A.representation ℓ w
      (k₁ * uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) * k₂) ≠ 0 := by
    rw [← hrep']
    exact hg
  have hupper := hB k₁ hk₁ k₂ hk₂ y hy f ⟨f, hf, rfl⟩ hne
  have hybox : y ∈ box := fun β => ⟨hy β, hupper β⟩
  let t := Function.surjInv hsurj (e y)
  have ht : t ∈ T0 := ⟨e y, ⟨y, hybox, rfl⟩, rfl⟩
  have hteq : QuotientGroup.mk' Zc t = QuotientGroup.mk' Zc (uniformizerPowers i (.ofAdd y)) :=
    Function.surjInv_eq hsurj (e y)
  have hz : t⁻¹ * uniformizerPowers i (.ofAdd y) ∈ Zc := QuotientGroup.eq.mp hteq
  set z := t⁻¹ * uniformizerPowers i (.ofAdd y) with hzdef
  have hyz : uniformizerPowers i (.ofAdd y) = t * z := by
    rw [hzdef, mul_inv_cancel_left]
  have hzk : z * k₂ = k₂ * z := (Subgroup.mem_center_iff.mp hz k₂).symm
  refine Set.mem_mul.mpr ⟨k₁ * (f : rationalPoints G) * t * k₂, ?_, z, hz, ?_⟩
  · exact Set.mem_mul.mpr ⟨k₁ * (f : rationalPoints G) * t,
      Set.mem_mul.mpr ⟨k₁ * (f : rationalPoints G),
        Set.mem_mul.mpr ⟨k₁, hk₁, (f : rationalPoints G), ⟨f, hf, rfl⟩, rfl⟩, t, ht, rfl⟩,
      k₂, hk₂, rfl⟩
  · rw [hrep, hyz, mul_assoc (k₁ * (f : rationalPoints G) * t) k₂ z, ← hzk]
    simp only [mul_assoc]

end Rational

/-- The structural reduction of the published (a) ⇔ (b) statement: the joint
special-compact/Cartan/basis existence statement implies it. -/
def SupercuspidalCoefficientCriterionReductionStatement : Prop :=
  JointSpecialCompactBasisExistenceStatement.{u} →
    SupercuspidalCoefficientCriterionStatement.{u, v}

/-- `JointSpecialCompactBasisExistenceStatement` implies Renard VI.2.1, (a) ⇔ (b). -/
theorem supercuspidalCoefficientCriterionReduction :
    SupercuspidalCoefficientCriterionReductionStatement.{u, v} := by
  intro hJoint k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ A
  exact ⟨coefficients_compactModCenter_of_isSupercuspidal hJoint hG A,
    isSupercuspidal_of_coefficients_compactModCenter hG A⟩

end Langlands.Aubert.General.RepresentedParabolic
