import Langlands.GroupScheme.IntegralModel.AffineFiberwiseOpen
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction

/-! # Affine neutral models over a Dedekind base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  [GeometricallyConnected G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of R))} {i : H ⟶ M.group}

/-- The relative identity component of a smooth model contains the entire generic fibre. -/
theorem generic_fiber_subset_range_relativeIdentityComponent (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) :
    M.group.X.hom ⁻¹' {⟨⊥, inferInstance⟩} ⊆ Set.range i.hom.hom.left := by
  let b := Spec.algebraMap R K
  let j := (GroupScheme.baseChange b).map i
  have he : IsIso j.hom.hom.left := by
    change IsIso (((GroupScheme.baseChange (Spec.algebraMap R K)).map i).hom.hom.left)
    rw [← M.neutralGenericIso_hom hM hi]
    exact (Grp.forget _ ⋙ Over.forget _).map_isIso (M.neutralGenericIso hM hi).hom
  have hr := RelativeIdentityComponent.range_of_isPullback
    (RelativeIdentityComponent.overPullback_isPullback b i.hom.hom)
  change Set.range j.hom.hom.left =
    (pullback.fst M.group.X.hom b) ⁻¹' Set.range i.hom.hom.left at hr
  intro x hx
  have hb : b (⟨⊥, inferInstance⟩ : PrimeSpectrum K) =
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  have hx' : x ∈ Set.range (pullback.fst M.group.X.hom b) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨⟨⊥, inferInstance⟩, hb.trans hx.symm⟩
  obtain ⟨y, rfl⟩ := hx'
  change y ∈ (pullback.fst M.group.X.hom b) ⁻¹' Set.range i.hom.hom.left
  rw [← hr]
  exact j.hom.hom.left.surjective y

/-- The relative identity component of an integral smooth affine Dedekind model is affine. -/
theorem isAffineHom_relativeIdentityComponent [IsIntegral G.X.left]
    (hM : M.IsSmooth) (hi : IsRelativeIdentityComponent M.group i) :
    IsAffineHom H.X.hom := by
  let : Smooth M.group.X.hom := hM
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let : IsIntegral M.group.X.left := M.isIntegral_of_generic
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let U : M.group.X.left.Opens := i.hom.hom.left.opensRange
  have hU : IsAffineOpen U := by
    apply Langlands.AlgebraicGeometry.AffineFiberwiseOpen.isAffineOpen_of_contains_generic_fiber
      R M.group.X.left M.group.X.hom U
    · exact M.generic_fiber_subset_range_relativeIdentityComponent hM hi
    · exact RelativeIdentityComponent.isClosed_fiber_preimage_range_inclusion M.group i hi
  let : IsAffine U := hU
  let : IsAffine H.X.left := IsAffine.of_isIso
    (IsOpenImmersion.isoOfRangeEq i.hom.hom.left U.ι (by simp [U])).hom
  infer_instance

/-- The actual relative identity component is an integral model of the same generic group. -/
def dedekindNeutralModel [IsIntegral G.X.left] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    IntegralModel R K G where
  group := H
  affine := M.isAffineHom_relativeIdentityComponent hM hi
  flat := inferInstance
  finiteType := inferInstance
  genericIso := M.neutralGenericIso hM hi ≪≫ M.genericIso

/-- The neutral-model inclusion extends the identity on the original generic group. -/
def dedekindNeutralInclusion [IsIntegral G.X.left] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    (M.dedekindNeutralModel hM hi hH).Hom M (𝟙 G) where
  hom := i
  generic_comm := by
    change _ = (M.neutralGenericIso hM hi ≪≫ M.genericIso).hom ≫ 𝟙 G
    rw [Iso.trans_hom, neutralGenericIso_hom, Category.comp_id]

/-- A smooth model of an integral geometrically connected group has an affine smooth
relative identity-component model with geometrically connected fibres. -/
theorem exists_dedekindNeutralModel [IsIntegral G.X.left] (hM : M.IsSmooth) :
    ∃ (N : IntegralModel R K G) (φ : N.Hom M (𝟙 G)),
      IsRelativeIdentityComponent M.group φ.hom ∧
        N.IsSmooth ∧ GeometricallyConnected N.group.X.hom := by
  obtain ⟨H, i, hi, hH, hgc⟩ := RelativeIdentityComponent.smoothExistence _ M.group hM
  exact ⟨M.dedekindNeutralModel hM hi hH,
    M.dedekindNeutralInclusion hM hi hH, hi, hH, hgc⟩

end Langlands.GroupScheme.IntegralModel
