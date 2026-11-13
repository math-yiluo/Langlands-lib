import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageStatement
import Langlands.GroupScheme.IntegralModel.SmoothHomExtension
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Galois.Local.SeparableValueArithmetic
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SeparableHenselian
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

/-! # Assembly of connected torus Iwahori models from focused inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- The extension criterion for smooth models, a smooth model of the maximal bounded
subgroup, the connected bound and a connected smooth model whose image is the Iwahori
subgroup together imply `UnramifiedTorusIwahoriModelStatement`. -/
def UnramifiedTorusIwahoriModelAssemblyStatement : Prop :=
  IntegralModel.SmoothHomExtensionStatement.{u} →
  UnramifiedTorusBoundedModelStatement.{u} →
  UnramifiedTorusConnectedBoundStatement.{u} →
  UnramifiedTorusIwahoriConnectedImageStatement.{u} →
  UnramifiedTorusIwahoriModelStatement.{u}

/-- A torus over a field that splits after a field extension has geometrically connected
structure morphism: the split base change is reductive, hence geometrically connected, and
geometric connectedness descends along the surjective base change. -/
theorem geometricallyConnected_of_isSplitTorus_baseChanged {k E : Type u} [Field k] [Field E]
    [Algebra k E] (G : GroupScheme (Spec (CommRingCat.of k)))
    (h : IsSplitTorus (baseChanged k E G)) : GeometricallyConnected G.X.hom := by
  have hE : GeometricallyConnected (pullback.snd G.X.hom (baseMap k E)) :=
    h.isReductive.geometricallyConnected
  have hs : Surjective (baseMap k E) := by
    constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of E)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩
  have := AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback G.X.hom (baseMap k E)).flip hs hE

section Neutral

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G S : GroupScheme (Spec (CommRingCat.of K))} [GeometricallyConnected G.X.hom]
  (M : IntegralModel R K G) (hM : M.IsSmooth)
  {H : GroupScheme (Spec (CommRingCat.of R))} {i : H ⟶ M.group}
  (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom)

/-- If a model homomorphism `φ : W → M` over `n` factors through the relative identity
component of `M`, then `n` carries the integral points of `W` into the integral points of the
neutral model. -/
theorem map_integralPoints_le_neutralModel {W : IntegralModel R K S} {n : S ⟶ G}
    (φ : W.Hom M n) {y : W.group ⟶ H} (hy : y ≫ i = φ.hom) :
    W.integralPoints.map (rationalPoints.map n) ≤
      (M.neutralModel hM hi hH).integralPoints := by
  rintro _ ⟨g, ⟨w, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map y w, ?_⟩
  have h1 := (M.neutralInclusion hM hi hH).integralPointMap_naturality
    (rationalPoints.map y w)
  have h2 := φ.integralPointMap_naturality w
  rw [IntegralModel.neutralInclusion_hom] at h1
  have h3 : rationalPoints.map i (rationalPoints.map y w) = rationalPoints.map φ.hom w := by
    rw [← hy]
    rfl
  have h4 : M.integralPointMap (rationalPoints.map i (rationalPoints.map y w)) =
      rationalPoints.map n (W.integralPointMap w) := by
    rw [h3, h2]
  have h5 := h1.symm.trans h4
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h5

/-- The neutral model of `M` has integral points inside those of `M`. -/
theorem neutralModel_integralPoints_le :
    (M.neutralModel hM hi hH).integralPoints ≤ M.integralPoints := by
  intro g hg
  have := (M.neutralInclusion hM hi hH).map_mem_integralPoints hg
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using this

end Neutral

/-- The maximal unramified integers form a Henselian discrete valuation ring with
algebraically closed, hence separably closed, residue field. -/
theorem fixedFieldIntegers_strictHenselian (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsDiscreteValuationRing (fixedFieldIntegers F) ∧ HenselianLocalRing (fixedFieldIntegers F) ∧
      IsSepClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  exact ⟨fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F),
    fixedFieldIntegersIsHenselian F, inferInstance⟩

/-- Over the maximal unramified integers, a homomorphism `n` whose image of the integral
points of a smooth model `W` is a subgroup `A` contained in the integral points of a model
`M` extends to a model homomorphism `W → M` (`SmoothHomExtensionStatement`). -/
theorem exists_hom_of_map_integralPoints_le
    (hExt : IntegralModel.SmoothHomExtensionStatement.{u}) (F : Type u) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    {W : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) S}
    {M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G} {n : S ⟶ G}
    (hW : W.IsSmooth) {A : Subgroup (rationalPoints G)}
    (hWA : W.integralPoints.map (rationalPoints.map n) = A) (hAM : A ≤ M.integralPoints) :
    Nonempty (W.Hom M n) := by
  obtain ⟨hdvr, hhens, hsep⟩ := fixedFieldIntegers_strictHenselian F
  refine hExt _ _ S G n W M hW fun g hg => hAM ?_
  rw [← hWA]
  exact Subgroup.mem_map_of_mem _ hg

set_option maxHeartbeats 1600000 in
/-- Proof of the assembly. Take the smooth model `M` of `T(K)^1` and its relative identity
component `M⁰`. The connected bound gives `M⁰(O) ⊆ T(K)^0`. The map `n` from the connected
model `W` carries `W(O)` onto `T(K)^0 ⊆ T(K)^1 = M(O)`, so it extends to a model
homomorphism `W → M`. Since `W` has geometrically connected fibres, that homomorphism factors
through `M⁰`, which gives `T(K)^0 ⊆ M⁰(O)`. -/
theorem unramifiedTorusIwahoriModelAssembly :
    UnramifiedTorusIwahoriModelAssemblyStatement.{u} := by
  intro hExt hBdd hConn hImg F _ _ _ _ T _ L _ _ hL
  obtain ⟨hdvr, hhens, hsep⟩ := fixedFieldIntegers_strictHenselian F
  have : GeometricallyConnected T.toGrp.X.hom :=
    geometricallyConnected_of_isSplitTorus_baseChanged T.toGrp hL
  -- The smooth model of `T(K)^1` and its relative identity component.
  obtain ⟨M, hM, hMpts⟩ := hBdd F T ⟨L, inferInstance, inferInstance, hL⟩
  obtain ⟨H, i, hi, hH, hgcH⟩ := RelativeIdentityComponent.smoothExistence _ M.group hM
  -- The connected model whose image is `T(K)^0`.
  obtain ⟨S, W, n, hW, hWgc, hWpts⟩ := hImg F T L hL
  have hle : W.integralPoints.map (rationalPoints.map n) ≤ M.integralPoints := by
    rw [hWpts, hMpts]
    exact torusNormIwahori_le_characterValuationKernel _ _
      (intermediateValuation_conjugate F L) T
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le hExt F hW rfl hle
  have : GeometricallyConnected W.group.X.hom := hWgc
  obtain ⟨y, hy⟩ := hi.exists_hom_lift φ.hom
  refine ⟨M.neutralModel hM hi hH, hH, hgcH, le_antisymm ?_ ?_⟩
  · exact hConn F T L hL _ hH hgcH
  · rw [← hWpts]
    exact map_integralPoints_le_neutralModel M hM hi hH φ hy

end Langlands.BruhatTits.IntegralModels
