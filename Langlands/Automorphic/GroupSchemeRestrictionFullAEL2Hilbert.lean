import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2
import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Global.AdelicNormOneHaarRightInvariantProof

/-! # The Hilbert structure on the almost-everywhere cuspidal `L²` subspace of `[G]` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.QuotientIntegration
open Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)

include hG in
/-- For a connected reductive group, the published `normOneHaarRightInvariant` gives right
invariance of Haar measure on the norm-one adelic subgroup. -/
theorem normOneHaar_isMulRightInvariant_of_connectedReductive :
    (Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant :=
  AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace

section Canonical

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)

local notation "μ" => quotientHaarMeasure F G S j
local notation "Sq" => quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT

include hG h hi hc hT in
/-- For a connected reductive group, the canonical measure on the restriction quotient is right
invariant, with no separate norm-one hypothesis. -/
theorem quotientHaarMeasure_rightInvariant_of_connectedReductive :
    QuotientRightInvariant F G (quotientHaarMeasure F G S j) :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientHaarMeasure_rightInvariant F G hi h hc hT

include hG h hi hc hT in
/-- For a connected reductive group, the canonical measure on the restriction quotient is
positive on nonempty open sets, with no separate norm-one hypothesis. -/
theorem quotientHaarMeasure_isOpenPosMeasure_of_connectedReductive :
    (quotientHaarMeasure F G S j).IsOpenPosMeasure :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientHaarMeasure_isOpenPosMeasure F G hi h hc hT

/-- The cuspidal subspace of `L²([G])`, packaged with its closedness. -/
def quotientFullAEL2CuspidalClosedSubmodule : ClosedSubmodule ℂ (Lp ℂ 2 μ) where
  toSubmodule := Sq
  isClosed' :=
    haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
    isClosed_quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT

/-- The cuspidal Hilbert space of `[G]`: the cuspidal subspace with the norm, topology and inner
product inherited from `L²([G])`. -/
abbrev QuotientFullAEL2CuspidalHilbertSpace := Sq

/-- The cuspidal subspace is complete, being closed in the complete space `L²([G])`. -/
instance quotientFullAEL2Cuspidal_completeSpace : CompleteSpace Sq :=
  (quotientFullAEL2CuspidalClosedSubmodule F G hPD hG h hi hc hT).isClosed.completeSpace_coe

/-- The inclusion of the cuspidal subspace as a linear isometry. -/
def quotientFullAEL2CuspidalInclusionLI : Sq →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (Sq).subtypeₗᵢ

/-- The orthogonal projection of `L²([G])` onto the cuspidal subspace. -/
def quotientFullAEL2CuspidalOrthogonalProjection : Lp ℂ 2 μ →L[ℂ] Sq :=
  (Sq).orthogonalProjectionOnto

/-- The orthogonal projection onto the cuspidal subspace, with codomain `L²([G])`. -/
def quotientFullAEL2CuspidalAmbientProjection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Sq).starProjection

theorem norm_quotientFullAEL2CuspidalOrthogonalProjection_le :
    ‖quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT‖ ≤ 1 :=
  (Sq).orthogonalProjectionOnto_norm_le

@[simp]
theorem quotientFullAEL2CuspidalOrthogonalProjection_inclusion (φ : Sq) :
    quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ.val = φ :=
  (Sq).orthogonalProjectionOnto_mem_subspace_eq_self φ

theorem quotientFullAEL2CuspidalAmbientProjection_mem (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ ∈ Sq :=
  (Sq).starProjection_apply_mem φ

/-- The fixed vectors of the ambient projection are exactly the cuspidal locus. -/
theorem quotientFullAEL2CuspidalAmbientProjection_eq_self_iff (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ = φ ↔
      φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j μ :=
  (Sq).starProjection_eq_self_iff

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "ρ" => rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv'
local notation "ρc" => quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv'

/-- Each right translation is a surjective linear isometry of the cuspidal subspace. -/
def quotientFullAEL2CuspidalRightTranslate (a : AdelicGroupPoints F G) : Sq ≃ₗᵢ[ℂ] Sq where
  toLinearEquiv :=
    { toLinearMap := ρc a
      invFun := ρc a⁻¹
      left_inv := (ρc).inv_self_apply a
      right_inv := (ρc).self_inv_apply a }
  norm_map' := norm_quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv' a

@[simp]
theorem quotientFullAEL2CuspidalRightTranslate_apply (a : AdelicGroupPoints F G) (φ : Sq) :
    quotientFullAEL2CuspidalRightTranslate F G hPD hG h hi hc hT hInv' a φ = ρc a φ := rfl

@[simp]
theorem quotientFullAEL2CuspidalRightTranslate_symm_apply (a : AdelicGroupPoints F G) (φ : Sq) :
    (quotientFullAEL2CuspidalRightTranslate F G hPD hG h hi hc hT hInv' a).symm φ =
      ρc a⁻¹ φ := rfl

/-- Right translation maps the cuspidal subspace onto itself. -/
theorem map_quotientFullAEL2CuspidalSubmodule_rightTranslate (a : AdelicGroupPoints F G) :
    (Sq).map (rationalQuotientL2RightTranslate F G μ hInv' a).toLinearMap = Sq := by
  let W := quotientFullAEL2CuspidalSubrepresentation F G hPD hG h hi hc hT hInv'
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact W.apply_mem_toSubmodule a hψ
  · intro hφ
    exact ⟨ρ a⁻¹ φ, W.apply_mem_toSubmodule a⁻¹ hφ, (ρ).self_inv_apply a φ⟩

/-- The ambient orthogonal projection commutes with the right regular representation. -/
theorem quotientFullAEL2CuspidalAmbientProjection_rightAction (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT (ρ a φ) =
      ρ a (quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ) := by
  let f := rationalQuotientL2RightTranslate F G μ hInv' a
  have hm : (Sq).map f.toLinearMap = Sq :=
    map_quotientFullAEL2CuspidalSubmodule_rightTranslate F G hPD hG h hi hc hT hInv' a
  let : ((Sq).map f.toLinearMap).HasOrthogonalProjection := by rw [hm]; infer_instance
  have hf := f.map_starProjection (Sq) φ
  change (Sq).starProjection (f φ) = f ((Sq).starProjection φ)
  simpa only [hm] using hf.symm

/-- The orthogonal projection onto the cuspidal subspace intertwines the right actions. -/
theorem quotientFullAEL2CuspidalOrthogonalProjection_rightAction (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT (ρ a φ) =
      ρc a (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ) := by
  apply Subtype.ext
  exact quotientFullAEL2CuspidalAmbientProjection_rightAction F G hPD hG h hi hc hT hInv' a φ

/-- The orthogonal projection as an intertwining map of representations. -/
def quotientFullAEL2CuspidalProjectionIntertwiner : (ρ).IntertwiningMap (ρc) where
  toLinearMap := (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT).toLinearMap
  isIntertwining' a := by
    apply LinearMap.ext
    exact quotientFullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG h hi hc hT hInv' a

/-- The projection is a left inverse of the inclusion intertwiner. -/
theorem quotientFullAEL2CuspidalProjectionIntertwiner_comp_inclusion :
    (quotientFullAEL2CuspidalProjectionIntertwiner F G hPD hG h hi hc hT hInv').comp
      (quotientFullAEL2CuspidalToLp F G hPD hG h hi hc hT hInv') =
      Representation.IntertwiningMap.id (ρc) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  exact quotientFullAEL2CuspidalOrthogonalProjection_inclusion F G hPD hG h hi hc hT φ

end Canonical

section Comparison

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

/-- `quotientL2Equiv` maps the published positive-torus cuspidal subspace onto the cuspidal
subspace of `[G]`. -/
theorem map_fullAEL2CuspidalSubmodule_quotientL2Equiv :
    (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).map
        ((quotientL2Equiv F G h).toLinearEquiv : _ →ₗ[ℂ] Lp ℂ 2 (quotientHaarMeasure F G S j)) =
      quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩ := by
  ext φ
  rw [Submodule.mem_map_equiv]
  exact (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ).symm

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

set_option maxRecDepth 20000 in
/-- `quotientL2Equiv` conjugates the published positive-torus ambient cuspidal projection to the
ambient cuspidal projection of `[G]`. -/
theorem quotientFullAEL2CuspidalAmbientProjection_quotientL2Equiv
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩
        (quotientL2Equiv F G h φ) =
      quotientL2Equiv F G h (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ) := by
  have : CompleteSpace (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc
      ⟨I, inferInstance, ⟨e⟩⟩) :=
    quotientFullAEL2Cuspidal_completeSpace F G hPD hG h hi hc _
  have hm := map_fullAEL2CuspidalSubmodule_quotientL2Equiv F G hPD hG h hi I e hc
  have hf := Submodule.starProjection_map_apply (quotientL2Equiv F G h)
    (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) (quotientL2Equiv F G h φ)
  rw [LinearIsometryEquiv.symm_apply_apply] at hf
  unfold quotientFullAEL2CuspidalAmbientProjection fullAEL2CuspidalAmbientProjection
  rw [← hf]
  have key : ∀ (K₁ K₂ : Submodule ℂ (Lp ℂ 2 (quotientHaarMeasure F G S j)))
      [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection], K₁ = K₂ →
        K₁.starProjection = K₂.starProjection := by
    rintro K₁ K₂ _ _ rfl
    rfl
  rw [key _ _ hm.symm]

/-- The isometric isomorphism `fullAEL2CuspidalEquiv` intertwines the two orthogonal cuspidal
projections. -/
theorem quotientFullAEL2CuspidalOrthogonalProjection_quotientL2Equiv
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩
        (quotientL2Equiv F G h φ) =
      fullAEL2CuspidalEquiv F G hPD hG h hi I e hc
        (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ) := by
  apply Subtype.ext
  exact quotientFullAEL2CuspidalAmbientProjection_quotientL2Equiv F G hPD hG h hi I e hc φ

end Comparison

section SplitComponents

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

include hG hi hj hs in
/-- For split components and connected reductive `G`, the canonical measure on the restriction
quotient is right invariant, with no separate norm-one hypothesis. -/
theorem quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive :
    QuotientRightInvariant F G (quotientHaarMeasure F G S j) :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs

include hG hi hj hs in
/-- For split components and connected reductive `G`, the canonical measure on the restriction
quotient is positive on nonempty open sets, with no separate norm-one hypothesis. -/
theorem quotientHaarMeasure_isOpenPosMeasure_of_splitComponents_of_connectedReductive :
    (quotientHaarMeasure F G S j).IsOpenPosMeasure :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientHaarMeasure_isOpenPosMeasure_of_splitComponents F G hi hj hs

/-- For split components and connected reductive `G`, the right regular representation on
`L²([G])`, with no separate norm-one hypothesis. -/
def splitComponentReductiveL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (Lp ℂ 2 (quotientHaarMeasure F G S j)) :=
  rationalQuotientL2RightAction F G _
    (quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive F G hG hi hj hs)

/-- The split-component cuspidal subspace of `L²([G])` is closed. -/
theorem isClosed_splitComponentFullAEL2CuspidalSubmodule_of_connectedReductive :
    IsClosed (splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs :
      Set (Lp ℂ 2 (quotientHaarMeasure F G S j))) :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  isClosed_splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs

/-- For split components, the orthogonal projection of `L²([G])` onto the cuspidal subspace. -/
def splitComponentFullAEL2CuspidalOrthogonalProjection :
    Lp ℂ 2 (quotientHaarMeasure F G S j) →L[ℂ]
      splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs :=
  quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG
    (subgroup_eq_of_splitComponents F G hj hs) hi hs.1.2 hs.1.1.1

/-- For split components, the cuspidal subrepresentation of the right regular representation
on `L²([G])`, with no separate norm-one hypothesis. -/
def splitComponentReductiveFullAEL2CuspidalSubrepresentation :
    Subrepresentation (splitComponentReductiveL2RightAction F G hG hi hj hs) :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientFullAEL2CuspidalSubrepresentation F G hPD hG (subgroup_eq_of_splitComponents F G hj hs)
    hi hs.1.2 hs.1.1.1
    (quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive F G hG hi hj hs)

/-- For split components, the orthogonal cuspidal projection as an intertwining map, with no
separate norm-one hypothesis. -/
def splitComponentFullAEL2CuspidalProjectionIntertwiner :
    (splitComponentReductiveL2RightAction F G hG hi hj hs).IntertwiningMap
      (splitComponentReductiveFullAEL2CuspidalSubrepresentation F G hPD hG hi hj hs).toRepresentation :=
  haveI := normOneHaar_isMulRightInvariant_of_connectedReductive F G hG
  quotientFullAEL2CuspidalProjectionIntertwiner F G hPD hG
    (subgroup_eq_of_splitComponents F G hj hs) hi hs.1.2 hs.1.1.1
    (quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive F G hG hi hj hs)

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
