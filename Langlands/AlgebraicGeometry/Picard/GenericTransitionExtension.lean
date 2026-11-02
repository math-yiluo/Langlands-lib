import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Localization.FractionRing

/-! # Extension from lifted generic transition units -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Picard

namespace CocycleGluing

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {ι : Type u} {T : ι → X.Opens}

/-- Sectionwise injectivity reflects the cocycle identity. -/
theorem isCocycle_of_pullback
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
    (hg : IsCocycle (pullbackCocycle q g)) : IsCocycle g := by
  intro i j k
  apply hinj (T i ⊓ T j ⊓ T k)
  rw [Scheme.Hom.app_eq_appLE, map_mul, appLE_res, appLE_res, appLE_res]
  have h := hg i j k
  rw [res_pullbackCocycle, res_pullbackCocycle, res_pullbackCocycle] at h
  exact h

/-- If total units pull back to the transitions of generic frames, they
already satisfy the total cocycle identity. -/
theorem isCocycle_of_transitionLift
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    {M : Y.Modules} {e : ∀ i, Γ(M, q ⁻¹ᵁ T i)}
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (q ⁻¹ᵁ T i))
    {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
    (htrans : IsTransition e (pullbackCocycle q g)) : IsCocycle g :=
  isCocycle_of_pullback q hinj (isCocycle_of_isTransition he htrans)

variable (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    (hT : (⨆ i, T i) = ⊤) (D : LineBundle Y)
    {e : ∀ i, Γ(D.obj, q ⁻¹ᵁ T i)}
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (q ⁻¹ᵁ T i))
    (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (htrans : IsTransition e (pullbackCocycle q g))

/-- The actual total line bundle constructed from lifted generic
transition units. No total cocycle identity is an input. -/
def lineBundleOfTransitionLift : LineBundle X :=
  ⟨glued g, isLocallyFreeRankOne_glued g hT
    (isCocycle_of_transitionLift q hinj he htrans)⟩

/-- The total bundle from lifted units pulls back to the original
line-bundle sheaf by an actual module-sheaf isomorphism. -/
def transitionLiftIso :
    ((LineBundle.pullback q).obj
      (lineBundleOfTransitionLift q hinj hT D he g htrans)).obj ≅ D.obj :=
  pullbackIso q g hT (isCocycle_of_transitionLift q hinj he htrans) ≪≫
    (frameIso he htrans (q.iSup_preimage_eq_top hT)).symm

include hinj hT in
/-- Individual total-unit lifts of the frame transitions suffice for an
actual extension; their cocycle identities follow from injectivity. -/
theorem exists_lineBundle_of_frameCocycle_lifts
    (hlift : ∀ i j, ∃ a : (Γ(X, T i ⊓ T j))ˣ,
      Units.map
        (q.appLE (T i ⊓ T j) (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) le_rfl).hom.toMonoidHom a =
        frameCocycle e he i j) :
    ∃ E : LineBundle X, Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj) := by
  choose g hg using hlift
  have hp : pullbackCocycle q g = frameCocycle e he := funext fun i ↦ funext fun j ↦ hg i j
  have ht : IsTransition e (pullbackCocycle q g) := by
    rw [hp]
    exact isTransition_frameCocycle he
  exact ⟨lineBundleOfTransitionLift q hinj hT D he g ht,
    ⟨transitionLiftIso q hinj hT D he g ht⟩⟩

end CocycleGluing

variable {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The spectrum map from any supplied fraction field is schematically
dominant, including when the base domain is already a field. -/
theorem fractionFieldSpec_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- The canonical generic projection of a flat scheme over a domain is
injective on sections over every total open. -/
theorem genericPullback_app_injective
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (U : X.Opens) :
    Function.Injective
      ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app U) := by
  have := fractionFieldSpec_isSchemeTheoreticallyDominant (R := R) K
  exact Scheme.Hom.app_injective _ U

end Langlands.AlgebraicGeometry.Picard
