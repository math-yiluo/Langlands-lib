/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import all WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicLisseFixed
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy

/-! # Finite constant module sheaves on a slice

Source: Stacks Project, proetale.tex, Tags 099R, 099Y and 09AL
(blueprint: lem-weil-pbc-finite-coefficient-slice-heart-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private def scalarCancelIso {C : Type (t + 1)} [Category.{t} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{t + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def extensionCancel (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ]
    (M : SheafOfModules.{t + 1} ((adicLisseForget X).obj R)) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map φ)).obj
      ((completedAdicChange X φ).obj M) ≅ M := by
  let e := (adicLisseForget X).mapIso (asIso φ)
  let E := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{t + 1} e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (scalarCancelIso e.inv e.hom e.inv_hom_id).symm
    (scalarCancelIso e.hom e.inv e.hom_inv_id)
  exact E.functor.mapIso (((pbcScalarAdjunction φ).leftAdjointUniq
    E.symm.toAdjunction).app M) ≪≫ E.counitIso.app M

private def fixedConstantIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    (N : ModuleCat.{t + 1} (ULift.{t + 1} B)) :
    (proEtaleModuleRestriction X B).obj ((koszulConstantFunctor X B).obj N) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have := ConstantScalarComparison.constantComparisonHom_isIso
    (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
      (koszulConstantUnit X B) N
  exact (asIso (ConstantScalarComparison.constantComparisonHom
    (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
      (koszulConstantUnit X B) N)).symm

private def sliceModelIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) [IsIso φ]
    (M : SheafOfModules.{t + 1} ((adicLisseForget X).obj R))
    (Z : X.Etale) (N : ModuleCat.{t + 1} (ULift.{t + 1} B))
    (e : M.over ((toProEt X).obj Z) ≅
      (((completedAdicChange X φ).obj ((koszulConstantFunctor X B).obj N)).over
        ((toProEt X).obj Z))) :
    (((SheafOfModules.restrictScalars ((adicLisseForget X).map φ) ⋙
      proEtaleModuleRestriction X B).obj M).over ((toProEt X).obj Z)) ≅
        (constantSheaf ((ProEt.topology X).over ((toProEt X).obj Z))
          (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N := by
  let U := (toProEt X).obj Z
  let R₀ := (adicLisseForget X).obj R
  let a := Functor.whiskerLeft (Over.forget U).op
    (proEtaleModuleScalarUnit X B ≫ ((adicLisseForget X).map φ).hom)
  let E := ConstantScalarComparison.restriction ((ProEt.topology X).over U)
    (ULift.{t + 1} B) (R₀.over U) a
  let K := (koszulConstantFunctor X B).obj N
  let E₀ := ConstantScalarComparison.restriction ((ProEt.topology X).over U)
    (ULift.{t + 1} B) ((adicModuleRing X B).over U)
    (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B))
  exact E.mapIso e ≪≫
    E₀.mapIso ((SheafOfModules.overFunctor _ U).mapIso (extensionCancel X φ K)) ≪≫
    ((ProEt.topology X).overPullback (ModuleCat.{t + 1} (ULift.{t + 1} B)) U).mapIso
      (fixedConstantIso X B N) ≪≫
    (constantSheafOverIso (ProEt.topology X) _ U N).symm

private def localizedModelIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} B)))
    (Z : X.Etale) (N : ModuleCat.{t + 1} (ULift.{t + 1} B))
    (e : F.over ((toProEt X).obj Z) ≅
      (constantSheaf ((ProEt.topology X).over ((toProEt X).obj Z))
        (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N) :
    (localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B))
      Z.hom inferInstance).obj F ≅
      (constantSheaf (ProEt.topology Z.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N := by
  let U := (toProEt X).obj Z
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology Z.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let E := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology Z.left) D
  let r : E.functor.obj (F.over U) ≅
      (localizationRestriction D Z.hom inferInstance).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  exact r.symm ≪≫ E.functor.mapIso e ≪≫
    ((ProEt.sliceEquiv X U).constantSheafSheafCongrIso
      ((ProEt.topology X).over U) (ProEt.topology Z.left) D
        (Over.mkIdTerminal (X := U))).app N

set_option linter.unusedVariables false in
/-- Finite etale-local constant models of a single module sheaf descend on a chart.
This is a statement in the abelian hearts; it has no complex or truncation bound.

Source: Stacks Project, proetale.tex, lemma-compare-locally-constant (099Y),
with small-site localization (099R).
(blueprint: lem-weil-pbc-finite-coefficient-slice-heart-origin).

Proof: restrict the action along phi and then along the constant-section map.
These operations retain the underlying additive sheaf. Identify the slice site
at V with the pro-etale site of V.left. Local finite models become constant
ULift(B)-module sheaves on that site: scalar extension along the isomorphism phi
cancels scalar restriction, and module sheafification of a constant module
restricts to the corresponding constant module-valued sheaf. Etale covers over
V transport to etale covers of V.left under the etale slice equivalence.
Apply finite locally constant descent (099Y). The descended sheaf can be taken
to be comparisonLowerStar of the fixed-coefficient restriction of M; its counit
is invertible on the supplied local constant models and hence globally.
Restrict the descended trivializations to every smaller etale chart to obtain
the displayed covering families. The comparison counit supplies the marking.
Empty charts admit the empty cover; zero modules and the zero ring cause no
exception. No derived object or connecting morphism is chosen. -/
theorem finiteCoefficient_slice_heart_origin
    (X : Scheme.{t})
    (B : Type t) [CommRing B] [Finite B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ)
    (M : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (V : X.Etale)
    (hloc : let R₀ := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R);
      ∀ (W : X.Etale) (g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  M ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X φ).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                  koszulConstantFunctor X B).obj N)))) :
    ∃ G : Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B)),
      (∀ W : V.left.Etale,
        ∃ (I : Type (t + 1)) (U : I → V.left.Etale) (f : ∀ i, U i ⟶ W),
          Sieve.ofArrows U f ∈ V.left.smallEtaleTopology W ∧
          ∀ i, ∃ N : ModuleCat.{t + 1} (ULift.{t + 1} B),
            Module.Finite (ULift.{t + 1} B) N ∧ Nonempty
              (G.over (U i) ≅
                (constantSheaf (V.left.smallEtaleTopology.over (U i))
                  (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N)) ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.left).obj G ≅
        (finiteCoefficientSliceRestriction X B R φ V).obj M) := by
  classical
  have := hφ
  let A := ULift.{t + 1} B
  let D := ModuleCat.{t + 1} A
  let F := (SheafOfModules.restrictScalars ((adicLisseForget X).map φ) ⋙
    proEtaleModuleRestriction X B).obj M
  obtain ⟨S, hS, hs⟩ := hloc V (𝟙 V)
  have hx := (mem_smallEtaleTopology_iff S).mp hS
  choose Z g hg hz using hx
  have hmodel (x : V.left) : ∃ N : ModuleCat.{t + 1} A, Finite N ∧
      Nonempty (F.over ((toProEt X).obj (Z x)) ≅
        (constantSheaf ((ProEt.topology X).over ((toProEt X).obj (Z x))) D).obj N) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := hs (Z x) (g x) (hg x)
    have := hN
    let N' := (ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).obj N
    have : Finite N := Module.finite_of_finite B
    have : Finite N' := inferInstanceAs (Finite (ULift.{t + 1} N))
    exact ⟨N', inferInstance, ⟨sliceModelIso X B R φ M (Z x) N' e⟩⟩
  let I := ULift.{t + 1} V.left
  let W (i : I) := (Z i.down).left
  let f (i : I) : W i ⟶ V.left := (g i.down).left
  have hf : Presieve.ofArrows W f ∈ proetalePrecoverage V.left := by
    apply etalePrecoverage_le_proetalePrecoverage
    exact (ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨⟨x⟩, hz x⟩, fun _ ↦ inferInstance⟩
  let Fᵥ := (localizationRestriction D V.hom inferInstance).obj F
  have hmodels (i : I) : ∃ N : ModuleCat.{t + 1} A, Finite N ∧
      Nonempty ((upperStar D (f i)).obj Fᵥ ≅
        (constantSheaf (ProEt.topology (W i)) D).obj N) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := hmodel i.down
    refine ⟨N, hN, ⟨?_⟩⟩
    exact (upperStar D (f i)).mapIso
        ((upperStarIsoLocalizationRestriction D V.hom inferInstance).app F).symm ≪≫
      ((upperStarComp D (f i) V.hom).app F).symm ≪≫
      (upperStarCongr D (MorphismProperty.Over.w (g i.down))).app F ≪≫
      (upperStarIsoLocalizationRestriction D (Z i.down).hom inferInstance).app F ≪≫
      localizedModelIso X B F (Z i.down) N e
  obtain ⟨G, hG, eG⟩ := etale_origin_of_finite_models V.left A Fᵥ ⟨I, W, f, hf, hmodels⟩
  refine ⟨G, ?_, eG⟩
  exact fun W ↦ AlgebraicGeometry.Etale.local_finite_module_models V.left A G hG W

end AlgebraicGeometry.Scheme
