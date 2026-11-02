import Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement
import Langlands.AlgebraicGeometry.Modules.ClosedPushforwardSupport
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialZeroDimensional
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Picard.EulerPositivityPreparationProof
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Sections of a line bundle twisted by the pullback of a rational point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibre

open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Scheme.Modules

local instance (X : Scheme.{u}) : (structureSheaf X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

variable {K : Type u} [Field K]

section FiniteScheme

variable {F : Scheme.{u}} (j : F ⟶ Spec (CommRingCat.of K)) [IsFinite j]

include j in
/-- A finite scheme over a field is discrete. -/
lemma discreteTopology_of_isFinite : DiscreteTopology F := by
  have : IsLocallyArtinian F := IsLocallyArtinian.of_locallyQuasiFinite j
  infer_instance

include j in
/-- A finite scheme over a field is noetherian. -/
lemma isNoetherian_of_isFinite : IsNoetherian F := by
  have : IsAffine F := isAffine_of_isAffineHom j
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian j
  exact {}

include j in
/-- Every module on a finite scheme over a field has support of dimension zero. -/
lemma hasSupportDimensionLT_one_of_isFinite (M : F.Modules) : HasSupportDimensionLT M 1 := by
  have := discreteTopology_of_isFinite j
  simpa using HasSupportDimensionLT.of_topologicalKrullDim_le (X := F) (d := 0)
    (by simpa using topologicalKrullDim_zero_of_discreteTopology F) M

include j in
/-- Every module on a finite scheme over a field has finite closed support. -/
lemma hasFiniteClosedSupport_of_isFinite (M : F.Modules) : HasFiniteClosedSupport M := by
  have := isNoetherian_of_isFinite j
  exact (hasSupportDimensionLT_one_of_isFinite j M).hasFiniteClosedSupport

/-- On a finite scheme over a field, the Euler characteristic of a module with finite
cohomology is the dimension of its global sections. -/
lemma eulerCharacteristic_eq_finrank_of_isFinite (M : F.Modules)
    (hM : HasFiniteCohomology j M) :
    eulerCharacteristic j M hM =
      (Module.finrank K ((relativeGlobalSections j).obj M) : ℤ) := by
  rw [Picard.eulerCharacteristic_eq_finrank_of_finiteClosedSupport j M hM
    (hasFiniteClosedSupport_of_isFinite j M)]
  exact congrArg _ ((relativeCohomologyZeroIso j).app M).toLinearEquiv.finrank_eq

/-- On a finite scheme over a field, a line bundle has as many global sections as the
structure sheaf. -/
theorem finrank_relativeGlobalSections_lineBundle (L : LineBundle F) :
    Module.finrank K ((relativeGlobalSections j).obj L.obj) =
      Module.finrank K ((relativeGlobalSections j).obj (structureSheaf F)) := by
  have := isNoetherian_of_isFinite j
  have : IsAffine F := isAffine_of_isAffineHom j
  let O := structureSheaf F
  have hO : HasFiniteAffineSections O := hasFiniteAffineSections_structureSheaf F
  have hD := hasVanishingEulerDifference_of_support j 1 O hO L
    (hasSupportDimensionLT_one_of_isFinite j O)
  have h10 : coherentEulerSequence j O hO L 1 = coherentEulerSequence j O hO L 0 := by
    have h := congrFun hD 0
    simp only [Function.iterate_one, fwdDiff, Pi.zero_apply, zero_add] at h
    exact sub_eq_zero.1 h
  have hL1 := Picard.tensorPow_isLocallyFreeRankOne F L 1
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle O _ hL1
  let e : tensorObj O (tensorPow L.obj 1) ≅ L.obj :=
    tensorMapIso (Iso.refl _) (tensorPowOneIso L.obj) ≪≫ tensorLeftUnitor L.obj
  have h1 : coherentEulerSequence j O hO L 1 =
      (Module.finrank K ((relativeGlobalSections j).obj L.obj) : ℚ) := by
    change ((coherentEulerCharacteristic j (tensorObj O (tensorPow L.obj 1))
      (hO.tensor_lineBundle hL1) : ℤ) : ℚ) = _
    unfold coherentEulerCharacteristic
    rw [eulerCharacteristic_eq_finrank_of_isFinite j]
    exact_mod_cast ((relativeGlobalSections j).mapIso e).toLinearEquiv.finrank_eq
  have h0 : coherentEulerSequence j O hO L 0 =
      (Module.finrank K ((relativeGlobalSections j).obj O) : ℚ) := by
    rw [coherentEulerSequence_eval_zero]
    unfold coherentEulerCharacteristic
    rw [eulerCharacteristic_eq_finrank_of_isFinite j]
    norm_cast
  exact_mod_cast h1.symm.trans (h10.trans h0)

/-- On a finite flat scheme over a field, the global sections of the structure sheaf have
dimension the native degree. -/
theorem finrank_relativeGlobalSections_structureSheaf [Flat j] (x : Spec (CommRingCat.of K)) :
    Module.finrank K ((relativeGlobalSections j).obj (structureSheaf F)) = j.finrank x := by
  rw [FiniteEtale.homFinrank_eq_coordinateFinrank j x]
  rfl

end FiniteScheme

section BaseChange

variable {Y D : Scheme.{u}}

/-- Flat base change in degree zero along a closed immersion `e : Spec K ⟶ D`: pulling
`e_* 𝒪` back along a flat `f` gives the pushforward of the structure sheaf of the fibre. -/
def pullbackPushforwardUnitIso (flat : FlatHigherDirectImageBaseChangeStatement.{u})
    (f : Y ⟶ D) (e : Spec (CommRingCat.of K) ⟶ D) [Flat f] [IsClosedImmersion e] :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K)))) ≅
      (Scheme.Modules.pushforward (pullback.snd e f)).obj (structureSheaf (pullback e f)) :=
  (Scheme.Modules.pullback f).mapIso ((higherDirectImageZeroIso e).app _).symm ≪≫
    (flat _ _ _ _ e f (pullback.snd e f) (pullback.fst e f) (IsPullback.of_hasPullback e f)
      inferInstance inferInstance ‹_› _ inferInstance 0).some ≪≫
    (higherDirectImageZeroIso _).app _ ≪≫
    (Scheme.Modules.pushforward _).mapIso (pullbackUnitIso _)

/-- Twisting by a line bundle commutes with pushing forward the structure sheaf of the fibre. -/
def tensorPullbackPushforwardUnitIso (flat : FlatHigherDirectImageBaseChangeStatement.{u})
    (f : Y ⟶ D) (e : Spec (CommRingCat.of K) ⟶ D) [Flat f] [IsClosedImmersion e]
    (N : LineBundle Y) :
    tensorObj N.obj ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K))))) ≅
      (Scheme.Modules.pushforward (pullback.snd e f)).obj
        ((Scheme.Modules.pullback (pullback.snd e f)).obj N.obj) :=
  tensorMapIso (Iso.refl _) (pullbackPushforwardUnitIso flat f e) ≪≫
    lineBundleProjectionIso (pullback.snd e f) N (structureSheaf _) ≪≫
    (Scheme.Modules.pushforward _).mapIso (tensorRightUnitor _)

/-- Relative global sections of a pushforward are relative global sections along the
composite. -/
def relativeGlobalSectionsPushforwardIso {F : Scheme.{u}} {R : CommRingCat.{u}}
    (i : F ⟶ Y) (π : Y ⟶ Spec R) (M : F.Modules) :
    (relativeGlobalSections π).obj ((Scheme.Modules.pushforward i).obj M) ≅
      (relativeGlobalSections (i ≫ π)).obj M :=
  moduleSpecΓFunctor.mapIso ((Scheme.Modules.pushforwardComp i π).app M)

/-- Step 6 of the dual-side Euler computation. For a finite flat map `f : Y ⟶ D` over a field
`K` and a `K`-point `e` of `D`, a line bundle `N` on `Y` twisted by `f^* e_* 𝒪` has global
sections of dimension the native degree of `f` at `e`. -/
theorem finrank_relativeGlobalSections_tensor_pullback_pushforward
    (flat : FlatHigherDirectImageBaseChangeStatement.{u})
    (πY : Y ⟶ Spec (CommRingCat.of K)) (πD : D ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ D) [IsFinite f] [Flat f] (hf : f ≫ πD = πY)
    (e : Spec (CommRingCat.of K) ⟶ D) (he : e ≫ πD = 𝟙 _) (N : LineBundle Y)
    (x : Spec (CommRingCat.of K)) :
    Module.finrank K ((relativeGlobalSections πY).obj
        (tensorObj N.obj ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K))))))) =
      f.finrank (e x) := by
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id πD e he
  have hij : pullback.snd e f ≫ πY = pullback.fst e f := by
    rw [← hf, ← pullback.condition_assoc, he, Category.comp_id]
  rw [((relativeGlobalSections πY).mapIso
      (tensorPullbackPushforwardUnitIso flat f e N)).toLinearEquiv.finrank_eq,
    (relativeGlobalSectionsPushforwardIso _ πY _).toLinearEquiv.finrank_eq]
  rw [hij]
  refine (finrank_relativeGlobalSections_lineBundle (pullback.fst e f)
    ((LineBundle.pullback (pullback.snd e f)).obj N)).trans ?_
  rw [finrank_relativeGlobalSections_structureSheaf (pullback.fst e f) x,
    Scheme.Hom.finrank_pullback_fst (f := f) (g := e)]

/-- The twist of a line bundle by `f^* e_* 𝒪` has finite closed support. -/
theorem hasFiniteClosedSupport_tensor_pullback_pushforward
    (flat : FlatHigherDirectImageBaseChangeStatement.{u})
    (πD : D ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ D) [IsFinite f] [Flat f]
    (e : Spec (CommRingCat.of K) ⟶ D) (he : e ≫ πD = 𝟙 _) (N : LineBundle Y) :
    HasFiniteClosedSupport (tensorObj N.obj ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K)))))) := by
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id πD e he
  rw [hasFiniteClosedSupport_iff_of_iso (tensorPullbackPushforwardUnitIso flat f e N)]
  have hfin := hasFiniteClosedSupport_of_isFinite (pullback.fst e f)
    ((Scheme.Modules.pullback (pullback.snd e f)).obj N.obj)
  let i := pullback.snd e f
  have hi : Topology.IsClosedEmbedding i := i.isClosedEmbedding
  rw [HasFiniteClosedSupport, stalkSupport_pushforward i hi]
  exact ⟨hfin.1.image _, fun y ⟨z, hz, hzy⟩ =>
    hzy ▸ by simpa using hi.isClosedMap _ (hfin.2 z hz)⟩

end BaseChange

/-- Given flat base change for higher direct images, for a finite flat map `f : Y ⟶ D` of
schemes over a field `K`, a `K`-point `e` of `D` and a line bundle `N` on `Y`, the module
`N ⊗ f^* e_* 𝒪` has finite closed support and its global sections over `K` have dimension
the native degree of `f` at `e`. -/
def FiniteFlatPointFibreSectionsStatement : Prop :=
  FlatHigherDirectImageBaseChangeStatement.{u} →
    ∀ (K : Type u) [Field K] (Y D : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of K))
      (πD : D ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ D), IsFinite f → Flat f → f ≫ πD = πY →
    ∀ (e : Spec (CommRingCat.of K) ⟶ D), e ≫ πD = 𝟙 _ → ∀ (N : LineBundle Y),
      HasFiniteClosedSupport (tensorObj N.obj ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K)))))) ∧
        ∀ x : Spec (CommRingCat.of K),
          Module.finrank K ((relativeGlobalSections πY).obj
            (tensorObj N.obj ((Scheme.Modules.pullback f).obj
              ((Scheme.Modules.pushforward e).obj
                (structureSheaf (Spec (CommRingCat.of K))))))) = f.finrank (e x)

/-- The anchor statement holds. -/
theorem finiteFlatPointFibreSections : FiniteFlatPointFibreSectionsStatement.{u} := by
  intro flat K _ Y D πY πD f _ _ hf e he N
  exact ⟨hasFiniteClosedSupport_tensor_pullback_pushforward flat πD f e he N,
    finrank_relativeGlobalSections_tensor_pullback_pushforward flat πY πD f hf e he N⟩

end Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibre
