import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Parabolic.QuotientInductionComparison
import Langlands.Representation.Aubert.RootSubsetExpansion
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso
import Langlands.Group.GL.CompactOpen

noncomputable section

open CategoryTheory
open scoped Pointwise NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV

section Algebra

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)

/-- The actual upper parabolic normalizes its kernel radical in GL. -/
theorem parabolic_le_normalizer_unipotentSubgroup :
    B.parabolic F ≤ Subgroup.normalizer (B.unipotentSubgroup F : Set (GeneralLinear n F)) := by
  have h := (B.unipotentRadical F).le_normalizer_map (B.parabolic F).subtype
  simpa only [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype,
    unipotentSubgroup] using h

/-- The actual block Levi and radical give the general semidirect decomposition. -/
theorem generalSemidirectDecomposition :
    Aubert.General.IsSemidirectDecomposition
      (B.parabolic F) (B.leviSubgroup F) (B.unipotentSubgroup F) := by
  refine ⟨B.leviSubgroup_le_parabolic F, B.unipotentSubgroup_le_parabolic F,
    B.parabolic_le_normalizer_unipotentSubgroup, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro g hg
    have hmem : (g : GeneralLinear n F) ∈ B.leviSubgroup F ⊓ B.unipotentSubgroup F := hg
    rw [B.leviSubgroup_inf_unipotentSubgroup F] at hmem
    exact Subtype.ext hmem
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    have hg : (g : GeneralLinear n F) ∈
        (B.leviSubgroup F : Set (GeneralLinear n F)) *
          (B.unipotentSubgroup F : Set (GeneralLinear n F)) := by
      rw [← B.parabolic_eq_levi_mul_unipotent F]
      exact g.2
    obtain ⟨m, hm, u, hu, heq⟩ := hg
    exact ⟨⟨m, B.leviSubgroup_le_parabolic F hm⟩, hm,
      ⟨u, B.unipotentSubgroup_le_parabolic F hu⟩, hu, Subtype.ext heq⟩

/-- The general projection is the existing actual diagonal-block projection. -/
@[simp] theorem generalSemidirectDecomposition_projection (g : B.parabolic F) :
    B.generalSemidirectDecomposition.projection g =
      B.leviEquiv F (B.leviProjection F g) := by
  apply (B.generalSemidirectDecomposition.projection_eq_iff g _).mpr
  let u : B.parabolic F := (B.leviInParabolic F (B.leviProjection F g))⁻¹ * g
  have hu : u ∈ B.unipotentRadical F := by
    change B.leviProjection F u = 1
    simp only [u, map_mul, map_inv, leviProjection_section, inv_mul_cancel]
  exact ⟨u, hu, rfl⟩

end Algebra

section Functors

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} (B : BlockShape n)
  [LocallyCompactSpace (GeneralLinear n F)] [NonarchimedeanGroup (GeneralLinear n F)]

/-- The full Haar conjugation modulus agrees with the supplied full block character.
This is a visible structural prerequisite, taken on the entire actual parabolic. -/
def GeneralModulusCompatibility (δ : B.Levi F →* ℝ≥0ˣ) : Prop :=
  HaarModulus.closedRestrictCharacter (B.unipotentSubgroup F)
    (B.isClosed_unipotentSubgroup F) (B.parabolic F)
    B.generalSemidirectDecomposition.le_normalizer = δ.comp (B.leviProjection F)

/-- The positive half of any open-kernel full block character, as a smooth character. -/
def blockHalfCharacterOf (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) : Induction.SmoothCharacter ℂ (B.Levi F) where
  toMonoidHom := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)
  isOpen_ker := by
    have he : (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)).ker =
        (Jacquet.inverseHalfCharacter δ).ker := by
      ext m
      simp [Jacquet.inverseHalfCharacter]
    rw [he]
    exact Jacquet.isOpen_ker_inverseHalfCharacter δ hδ

omit [NonarchimedeanGroup (GeneralLinear n F)] in
/-- Full compatibility fixes the positive induction half on every element of P. -/
theorem generalHalfCharacter_eq (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ) :
    HaarModulus.closedHalfCharacter (B.unipotentSubgroup F)
      (B.isClosed_unipotentSubgroup F) (B.parabolic F)
      B.generalSemidirectDecomposition.le_normalizer =
        (B.blockHalfCharacterOf δ hδ).toMonoidHom.comp (B.leviProjection F) := by
  unfold HaarModulus.closedHalfCharacter
  rw [hc]
  rfl

omit [NonarchimedeanGroup (GeneralLinear n F)] in
/-- The full Haar modulus restricted to the embedded Levi is the same block modulus. -/
theorem generalLeviModulus_eq (δ : B.Levi F →* ℝ≥0ˣ)
    (hc : B.GeneralModulusCompatibility δ) :
    HaarModulus.closedRestrictCharacter (B.unipotentSubgroup F)
      (B.isClosed_unipotentSubgroup F) (B.leviSubgroup F)
      B.generalSemidirectDecomposition.levi_le_normalizer =
        δ.comp (B.leviEquiv F).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro m
  exact congrArg (fun χ => χ (B.leviAsParabolic F m)) hc

omit [NonarchimedeanGroup (GeneralLinear n F)] in
/-- The inverse half on the embedded Levi is the existing Jacquet inverse half. -/
theorem generalInverseHalfCharacter_eq (δ : B.Levi F →* ℝ≥0ˣ)
    (hc : B.GeneralModulusCompatibility δ) :
    HaarModulus.closedInverseHalfCharacter (B.unipotentSubgroup F)
      (B.isClosed_unipotentSubgroup F) (B.leviSubgroup F)
      B.generalSemidirectDecomposition.levi_le_normalizer =
        (Jacquet.inverseHalfCharacter δ).comp (B.leviEquiv F).symm.toMonoidHom := by
  unfold HaarModulus.closedInverseHalfCharacter
  rw [B.generalLeviModulus_eq δ hc]
  rfl

/-- The general inducing action after actual Levi transport is the block action. -/
theorem generalInducingRepresentation_eq (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) :
    Aubert.General.inducingRepresentation B.generalSemidirectDecomposition
      (B.isClosed_unipotentSubgroup F) ((Parabolic.productToEmbeddedLevi B).obj A) =
        B.inducingRepresentation (B.blockHalfCharacterOf δ hδ) A.representation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change ((HaarModulus.closedHalfCharacter (B.unipotentSubgroup F)
      (B.isClosed_unipotentSubgroup F) (B.parabolic F)
      B.generalSemidirectDecomposition.le_normalizer g : ℂˣ) : ℂ) •
        A.representation ((B.leviEquiv F).symm (B.generalSemidirectDecomposition.projection g)) v =
      ((B.blockHalfCharacterOf δ hδ).toMonoidHom (B.leviProjection F g) : ℂ) •
        A.representation (B.leviProjection F g) v
  rw [B.generalHalfCharacter_eq δ hδ hc, B.generalSemidirectDecomposition_projection]
  simp only [MonoidHom.comp_apply, MulEquiv.symm_apply_apply]

/-- Identity-vector intertwining equivalence of the actual covariance actions. -/
def generalInducingEquiv (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) :
    (Aubert.General.inducingRepresentation B.generalSemidirectDecomposition
      (B.isClosed_unipotentSubgroup F) ((Parabolic.productToEmbeddedLevi B).obj A)).Equiv
        (B.inducingRepresentation (B.blockHalfCharacterOf δ hδ) A.representation) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => by
    rw [B.generalInducingRepresentation_eq δ hδ hc A]
    rfl

/-- General and block induction are naturally isomorphic on the full smooth categories. -/
def generalInductionIso (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ) :
    Parabolic.productToEmbeddedLevi.{uF, uV} B ⋙
      Aubert.General.normalizedInductionFunctor B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F) ≅
          B.normalizedInductionFunctorOf (B.blockHalfCharacterOf δ hδ) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (Induction.smoothInducedEquiv (B.parabolic F)
      (B.generalInducingEquiv δ hδ hc A)))
    fun f => by
      ext φ
      rfl

/-- The induction comparison keeps every underlying function pointwise. -/
@[simp] theorem generalInductionIso_hom_eval (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F))
    (f : ((Parabolic.productToEmbeddedLevi.{uF, uV} B ⋙
      Aubert.General.normalizedInductionFunctor B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F)).obj A)) (g : GeneralLinear n F) :
    Induction.eval (B.parabolic F)
        (B.inducingRepresentation (B.blockHalfCharacterOf δ hδ) A.representation)
        (SmoothRep.hom ((B.generalInductionIso δ hδ hc).app A).hom f) g =
      Induction.eval (B.parabolic F)
        (Aubert.General.inducingRepresentation B.generalSemidirectDecomposition
          (B.isClosed_unipotentSubgroup F) ((Parabolic.productToEmbeddedLevi B).obj A)) f g := rfl

/-- Compare the two genuine quotient carriers by sending `[v]` to `[v]`. -/
def generalJacquetLinearEquiv (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) :
    B.JacquetModule A.representation ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation (B.unipotentSubgroup F) 1 :=
  (B.jacquetModuleEquiv A.representation).trans
    (Jacquet.Localization.trivialEquiv A.representation (B.unipotentSubgroup F)
      (B.leviSubgroup F) B.generalSemidirectDecomposition.levi_le_normalizer).toLinearEquiv.symm

omit [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace (GeneralLinear n F)]
  [NonarchimedeanGroup (GeneralLinear n F)] in
@[simp] theorem generalJacquetLinearEquiv_mk
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) (v : A) :
    B.generalJacquetLinearEquiv A (B.jacquetMk A.representation v) =
      Jacquet.Localization.mk A.representation (B.unipotentSubgroup F) 1 v := rfl

/-- The quotient-carrier comparison intertwines the normalized embedded Levi actions. -/
def generalJacquetEquiv (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) :
    (((B.normalizedJacquetFunctorOf δ hδ) ⋙
      Parabolic.productToEmbeddedLevi B).obj A).representation.Equiv
        ((Aubert.General.jacquetFunctor B.generalSemidirectDecomposition
          (B.isClosed_unipotentSubgroup F)).obj A).representation :=
  Representation.Equiv.mk (B.generalJacquetLinearEquiv A) fun m => by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation q
    change B.generalJacquetLinearEquiv A
        (B.normalizedJacquetOf δ A.representation ((B.leviEquiv F).symm m)
          (B.jacquetMk A.representation v)) = _
    rw [B.normalizedJacquetOf_mk, map_smul, B.generalJacquetLinearEquiv_mk]
    change _ = ((Aubert.General.normalizedJacquetFunctor (B.unipotentSubgroup F)
      (B.leviSubgroup F) (B.isClosed_unipotentSubgroup F)
      B.generalSemidirectDecomposition.levi_le_normalizer).obj A).representation m
        (Jacquet.Localization.mk A.representation (B.unipotentSubgroup F) 1 v)
    rw [Aubert.General.normalizedJacquetFunctor_obj_apply,
      B.generalInverseHalfCharacter_eq δ hc, MonoidHom.comp_apply,
      Jacquet.inverseHalfCharacter_apply]
    have hm : B.leviEmbedding F ((B.leviEquiv F).symm m) = (m : GeneralLinear n F) :=
      congrArg Subtype.val ((B.leviEquiv F).apply_symm_apply m)
    rw [hm]
    rfl

/-- General and block Jacquet restriction are naturally isomorphic on all smooth objects. -/
def generalJacquetIso (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ) :
    B.normalizedJacquetFunctorOf.{uF, uV} δ hδ ⋙ Parabolic.productToEmbeddedLevi B ≅
      Aubert.General.jacquetFunctor B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F) :=
  NatIso.ofComponents (fun A => SmoothRep.mkIso (B.generalJacquetEquiv δ hδ hc A))
    fun {A C} f => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation q
      rfl

@[simp] theorem generalJacquetIso_hom_mk (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)) (v : A) :
    SmoothRep.hom ((B.generalJacquetIso δ hδ hc).app A).hom
        (B.jacquetMk A.representation v) =
      Jacquet.Localization.mk A.representation (B.unipotentSubgroup F) 1 v := rfl

/-- Inverse change from the actual embedded Levi to the block product. -/
def embeddedToProductLevi :
    SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F) :=
  SmoothRep.pullbackFunctor (B.leviEquivContinuous F)

/-- The direct general covariance on every embedded-Levi object agrees with
the block covariance after inverse Levi transport. -/
def generalEmbeddedInducingEquiv (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (A : SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F)) :
    (Aubert.General.inducingRepresentation B.generalSemidirectDecomposition
      (B.isClosed_unipotentSubgroup F) A).Equiv
        (B.inducingRepresentation (B.blockHalfCharacterOf δ hδ)
          ((B.embeddedToProductLevi).obj A).representation) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => by
    apply LinearMap.ext
    intro v
    change ((HaarModulus.closedHalfCharacter (B.unipotentSubgroup F)
      (B.isClosed_unipotentSubgroup F) (B.parabolic F)
      B.generalSemidirectDecomposition.le_normalizer g : ℂˣ) : ℂ) •
        A.representation (B.generalSemidirectDecomposition.projection g) v =
      ((B.blockHalfCharacterOf δ hδ).toMonoidHom (B.leviProjection F g) : ℂ) •
        A.representation (B.leviEquiv F (B.leviProjection F g)) v
    rw [B.generalHalfCharacter_eq δ hδ hc, B.generalSemidirectDecomposition_projection]
    rfl

/-- Comparison on the entire embedded-Levi smooth category. -/
def generalEmbeddedInductionIso (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ) :
    Aubert.General.normalizedInductionFunctor.{uF, uV} B.generalSemidirectDecomposition
      (B.isClosed_unipotentSubgroup F) ≅
        B.embeddedToProductLevi ⋙ B.normalizedInductionFunctorOf (B.blockHalfCharacterOf δ hδ) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (Induction.smoothInducedEquiv (B.parabolic F)
      (B.generalEmbeddedInducingEquiv δ hδ hc A)))
    fun f => by
      ext φ
      rfl

/-- The existing block preservation proofs supply all four general preservation
properties through actual natural isomorphisms. -/
theorem generalParabolicFiniteLength_of_block (δ : B.Levi F →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (B.Levi F))) (hc : B.GeneralModulusCompatibility δ)
    (hIl : SmoothRep.PreservesFiniteLength
      (B.normalizedInductionFunctorOf.{uF, uV} (B.blockHalfCharacterOf δ hδ)))
    (hIx : SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedInductionFunctorOf.{uF, uV} (B.blockHalfCharacterOf δ hδ)))
    (hJl : SmoothRep.PreservesFiniteLength (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ))
    (hJx : SmoothRep.PreservesFiniteLengthShortExact
      (B.normalizedJacquetFunctorOf.{uF, uV} δ hδ)) :
    Aubert.General.ParabolicFiniteLength.{uF, uV} B.generalSemidirectDecomposition
      (B.isClosed_unipotentSubgroup F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((SmoothRep.pullbackFunctor_preservesFiniteLength
      (B.leviEquivContinuous F)).comp hIl).of_iso
        (B.generalEmbeddedInductionIso δ hδ hc).symm
  · exact (SmoothRep.PreservesFiniteLengthShortExact.comp
      (SmoothRep.pullbackFunctor_preservesFiniteLength (B.leviEquivContinuous F))
      (SmoothRep.pullbackFunctor_preservesShortExact (B.leviEquivContinuous F))
      hIx).of_iso (B.generalEmbeddedInductionIso δ hδ hc).symm
  · exact (hJl.comp (SmoothRep.pullbackFunctor_preservesFiniteLength
      (B.leviEquivContinuous F).symm)).of_iso (B.generalJacquetIso δ hδ hc)
  · exact (SmoothRep.PreservesFiniteLengthShortExact.comp hJl hJx
      (SmoothRep.pullbackFunctor_preservesShortExact
        (B.leviEquivContinuous F).symm)).of_iso (B.generalJacquetIso δ hδ hc)

end Functors

end Langlands.GeneralLinear.BlockShape


namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem generalLinear_isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The remaining full Haar-to-block modulus comparison for the actual p-adic GL
parabolic, with the supplied topology. This is a structural proposition target. -/
def GeneralLinearModulusCompatibility : Prop :=
  letI := T.topology
  letI := generalLinear_isTopologicalRing F T
  letI := T.fieldT2
  letI := T.generalLinearLocallyCompactSpace n
  letI := T.generalLinearNonarchimedean n
  B.GeneralModulusCompatibility (T.leviModulus B)

/-- The general actual GL functors preserve finite length and actual short exact
sequences by the existing block proofs; only the full modulus comparison remains. -/
theorem generalLinearParabolicFiniteLength
    (hc : GeneralLinearModulusCompatibility F T B) :
    letI := T.topology
    letI := generalLinear_isTopologicalRing F T
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    Aubert.General.ParabolicFiniteLength.{uF, max uF uV}
      B.generalSemidirectDecomposition (B.isClosed_unipotentSubgroup F.Carrier) := by
  let := T.topology
  let := generalLinear_isTopologicalRing F T
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  exact B.generalParabolicFiniteLength_of_block (T.leviModulus B)
    (T.isOpen_ker_leviModulus B) hc
    (normalizedInductionK0_hasFiniteLength.{uF, uV} F T B)
    (FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B)
    (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B)
    (FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact F T B)


/-- The general induction map on full exact K0 equals the unchanged block map
following inverse transport from the actual embedded Levi. -/
theorem generalInductionK0_eq (hc : GeneralLinearModulusCompatibility F T B) :
    letI := T.topology
    letI := generalLinear_isTopologicalRing F T
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    let hfl := generalLinearParabolicFiniteLength.{uF, uV} F T B hc
    Aubert.General.inductionK0 B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F.Carrier) hfl.1 hfl.2.1 =
      (normalizedInductionK0.{uF, uV} F T B).comp
        (embeddedLeviK0Equiv B).symm.toLinearMap := by
  let := T.topology
  let := generalLinear_isTopologicalRing F T
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let hfl := generalLinearParabolicFiniteLength.{uF, uV} F T B hc
  let hIl := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B
  let hIx := FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact
    F T B
  let hEl := SmoothRep.pullbackFunctor_preservesFiniteLength
    (B.leviEquivContinuous F.Carrier)
  let hEx := SmoothRep.pullbackFunctor_preservesShortExact
    (B.leviEquivContinuous F.Carrier)
  change SmoothRep.FiniteLengthGrothendieckGroup.map _ hfl.1 hfl.2.1 =
    (SmoothRep.FiniteLengthGrothendieckGroup.map
      (B.normalizedInductionFunctorOf (T.leviHalfCharacter B)) hIl hIx).comp
        (SmoothRep.FiniteLengthGrothendieckGroup.map B.embeddedToProductLevi hEl hEx)
  exact (SmoothRep.FiniteLengthGrothendieckGroup.map_eq_of_iso
    (B.generalEmbeddedInductionIso (T.leviModulus B) (T.isOpen_ker_leviModulus B) hc)
    hfl.1 hfl.2.1 (hEl.comp hIl)
    (SmoothRep.PreservesFiniteLengthShortExact.comp hEl hEx hIx)).trans
      (SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _ hEl hEx hIl hIx _ _)

/-- The general Jacquet map on full exact K0 equals forward actual embedded-Levi
transport after the unchanged block Jacquet map. -/
theorem generalJacquetK0_eq (hc : GeneralLinearModulusCompatibility F T B) :
    letI := T.topology
    letI := generalLinear_isTopologicalRing F T
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    let hfl := generalLinearParabolicFiniteLength.{uF, uV} F T B hc
    Aubert.General.jacquetK0 B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F.Carrier) hfl.2.2.1 hfl.2.2.2 =
      (embeddedLeviK0Equiv B).toLinearMap.comp
        (normalizedJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  let := generalLinear_isTopologicalRing F T
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let hfl := generalLinearParabolicFiniteLength.{uF, uV} F T B hc
  let hJl := normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B
  let hJx := FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact
    F T B
  let hEl := SmoothRep.pullbackFunctor_preservesFiniteLength
    (B.leviEquivContinuous F.Carrier).symm
  let hEx := SmoothRep.pullbackFunctor_preservesShortExact
    (B.leviEquivContinuous F.Carrier).symm
  change SmoothRep.FiniteLengthGrothendieckGroup.map _ hfl.2.2.1 hfl.2.2.2 =
    (SmoothRep.FiniteLengthGrothendieckGroup.map (productToEmbeddedLevi B) hEl hEx).comp
      (SmoothRep.FiniteLengthGrothendieckGroup.map
        (B.normalizedJacquetFunctorOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)) hJl hJx)
  exact (SmoothRep.FiniteLengthGrothendieckGroup.map_eq_of_iso
    (B.generalJacquetIso (T.leviModulus B) (T.isOpen_ker_leviModulus B) hc).symm
    hfl.2.2.1 hfl.2.2.2 (SmoothRep.PreservesFiniteLength.comp hJl hEl)
    (SmoothRep.PreservesFiniteLengthShortExact.comp hJl hJx hEx)).trans
      (SmoothRep.FiniteLengthGrothendieckGroup.map_comp _ _ hJl hJx hEl hEx _ _)

/-- The general and existing block induction-after-Jacquet maps agree on every
class of the actual exact finite-length Grothendieck group. -/
theorem generalInductionJacquetK0_eq (hc : GeneralLinearModulusCompatibility F T B) :
    letI := T.topology
    letI := generalLinear_isTopologicalRing F T
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    let hfl := generalLinearParabolicFiniteLength.{uF, uV} F T B hc
    (Aubert.General.inductionK0 B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F.Carrier) hfl.1 hfl.2.1).comp
      (Aubert.General.jacquetK0 B.generalSemidirectDecomposition
        (B.isClosed_unipotentSubgroup F.Carrier) hfl.2.2.1 hfl.2.2.2) =
      (normalizedInductionK0.{uF, uV} F T B).comp
        (normalizedJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  let := generalLinear_isTopologicalRing F T
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  dsimp only
  rw [generalInductionK0_eq F T B hc, generalJacquetK0_eq F T B hc]
  apply LinearMap.ext
  intro x
  exact congrArg (normalizedInductionK0.{uF, uV} F T B)
    ((embeddedLeviK0Equiv B).symm_apply_apply (normalizedJacquetK0.{uF, uV} F T B x))

end Langlands.Parabolic


namespace Langlands.Aubert

universe uF uV

/-- The actual general unadjusted operator, specialized along the existing
Levi-root-subset equivalence, is the unchanged actual GL operator in every rank. -/
theorem generalAlternatingOperator_eq
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hc : ∀ B : GeneralLinear.BlockShape n, Parabolic.GeneralLinearModulusCompatibility F T B) :
    letI := T.topology
    letI := Parabolic.generalLinear_isTopologicalRing F T
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    General.alternatingOperator
      (fun I : Finset (Fin (n - 1)) =>
        ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I).parabolic F.Carrier)
      (fun I => ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I).leviSubgroup F.Carrier)
      (fun I => ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I).unipotentSubgroup F.Carrier)
      (fun I => ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I).generalSemidirectDecomposition)
      (fun I => ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I).isClosed_unipotentSubgroup
        F.Carrier)
      (fun I => Parabolic.generalLinearParabolicFiniteLength.{uF, uV} F T
        ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I) (hc _)) =
        alternatingOperator.{uF, uV} F T n := by
  let := T.topology
  let := Parabolic.generalLinear_isTopologicalRing F T
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  rw [General.alternatingOperator, alternatingOperator_eq_rootSubset_sum]
  apply Finset.sum_congr rfl
  intro I _
  exact congrArg (fun f => ((-1 : ℤ) ^ I.card) • f)
    (Parabolic.generalInductionJacquetK0_eq.{uF, uV} F T
      ((GeneralLinear.BlockShape.leviRootSubsetEquiv n).symm I) (hc _))

end Langlands.Aubert
