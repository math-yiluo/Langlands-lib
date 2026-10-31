import Langlands.AlgebraicGeometry.Modules.BaseChangeResolution
import Langlands.Cohomology.ExactAdjunctionHomology
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Canonical base change and scalar extension of cochain sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex X'.Modules ℕ}

/-- The actual scalar-linear cochain adjunct of the sections base-change map. -/
def scalarResolutionSectionsBaseChangeMap
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj
        (((relativeGlobalSections f).mapHomologicalComplex _).obj K) ⟶
      ((relativeGlobalSections f').mapHomologicalComplex _).obj L :=
  ((extendRestrictScalarsComplexAdjunction (ComplexShape.up ℕ) φ.hom).homEquiv _ _).symm
    (resolutionSectionsBaseChangeMap φ f f' g w t)

/-- Each component is the scalar adjunct of the specified sections component. -/
@[simp]
lemma scalarResolutionSectionsBaseChangeMap_f
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) (q : ℕ) :
    (scalarResolutionSectionsBaseChangeMap φ f f' g w t).f q =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
        ((resolutionSectionsBaseChangeMap φ f f' g w t).f q) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar cochain map sends each tensor generator to the specified
semilinear sections component. -/
lemma scalarResolutionSectionsBaseChangeMap_one_tmul
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
    (q : ℕ) (x : (relativeGlobalSections f).obj (K.X q)) :
    (scalarResolutionSectionsBaseChangeMap φ f f' g w t).f q
        ((1 : R') ⊗ₜ[R,φ.hom] x) =
      (resolutionSectionsBaseChangeMap φ f f' g w t).f q x := by
  rw [scalarResolutionSectionsBaseChangeMap_f]
  have h := congrArg (fun k => k x)
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).apply_symm_apply
      ((resolutionSectionsBaseChangeMap φ f f' g w t).f q))
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using! h

/-- The scalar cochain map respects compatible squares on the two complexes. -/
@[reassoc]
lemma scalarResolutionSectionsBaseChangeMap_naturality
    {K' : CochainComplex X.Modules ℕ} {L' : CochainComplex X'.Modules ℕ}
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
    (t' : K' ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L')
    (a : K ⟶ K') (b : L ⟶ L')
    (ht : a ≫ t' = t ≫ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).map b) :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).map
        (((relativeGlobalSections f).mapHomologicalComplex _).map a) ≫
        scalarResolutionSectionsBaseChangeMap φ f f' g w t' =
      scalarResolutionSectionsBaseChangeMap φ f f' g w t ≫
        ((relativeGlobalSections f').mapHomologicalComplex _).map b :=
  (extendRestrictScalarsComplexAdjunction (ComplexShape.up ℕ) φ.hom).homEquiv_naturality_right_square
    _ _ _ _ (resolutionSectionsBaseChangeMap_naturality φ f f' g w t t' a b ht)

/-- For flat scalar extension, the cohomological scalar adjunct is cohomology
of the actual scalar cochain map through the canonical exactness comparison. -/
lemma scalarResolutionCohomologyMap_eq_homology
    (hφ : φ.hom.Flat)
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) (n : ℕ) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
    scalarResolutionCohomologyMap φ f f' g w t n =
      (DerivedComparison.mapHomologyIso (ModuleCat.extendScalars φ.hom)
        (((relativeGlobalSections f).mapHomologicalComplex _).obj K) n).inv ≫
        (homologyFunctor (ModuleCat R') _ n).map
          (scalarResolutionSectionsBaseChangeMap φ f f' g w t) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact ExactAdjunction.homologyAdjunct_eq (ModuleCat.extendRestrictScalarsAdj φ.hom)
    (resolutionSectionsBaseChangeMap φ f f' g w t) n

variable {M : X.Modules}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ X'.Modules).obj ((Scheme.Modules.pullback g).obj M) ⟶ L)
  [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t =
    (CochainComplex.single₀ X.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- Compute the specified canonical scalar base-change map using cohomology of
the actual scalar cochain adjunct when the base ring map is flat. -/
@[reassoc]
theorem resolutionComparison_scalarBaseChangeMap_homology
    (hφ : φ.hom.Flat)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
    (ModuleCat.extendScalars φ.hom).map
        (resolutionComparison (relativeGlobalSections f) ε n) ≫
        scalarBaseChangeMap φ f f' g w M hM n =
      (DerivedComparison.mapHomologyIso (ModuleCat.extendScalars φ.hom)
        (((relativeGlobalSections f).mapHomologicalComplex _).obj K) n).inv ≫
        (homologyFunctor (ModuleCat R') _ n).map
          (scalarResolutionSectionsBaseChangeMap φ f f' g w t) ≫
        resolutionComparison (relativeGlobalSections f') η n := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  rw [resolutionComparison_scalarBaseChangeMap φ f f' g w ε η t ht hM n,
    scalarResolutionCohomologyMap_eq_homology φ f f' g w hφ t n, Category.assoc]

include ht in
/-- A quasi-isomorphism of scalar sections complexes of acyclic resolutions
makes the specified canonical scalar base-change map invertible. -/
theorem isIso_scalarBaseChangeMap_of_acyclicResolutions
    (hφ : φ.hom.Flat)
    (hK : ∀ i q : ℕ, IsZero ((relativeCohomology f (q + 1)).obj (K.X i)))
    (hL : ∀ i q : ℕ, IsZero ((relativeCohomology f' (q + 1)).obj (L.X i)))
    [QuasiIso (scalarResolutionSectionsBaseChangeMap φ f f' g w t)]
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) : IsIso (scalarBaseChangeMap φ f f' g w M hM n) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have hsource : IsIso (resolutionComparison (relativeGlobalSections f) ε n) :=
    (acyclicResolutionComparisonStatement X.Modules (ModuleCat R)
      (relativeGlobalSections f) M K ε inferInstance hK (injectiveResolution M) _
      (comp_lift_id ε _)).2 n
  have htarget : IsIso (resolutionComparison (relativeGlobalSections f') η n) :=
    (acyclicResolutionComparisonStatement X'.Modules (ModuleCat R')
      (relativeGlobalSections f') ((Scheme.Modules.pullback g).obj M) L η
      inferInstance hL (injectiveResolution ((Scheme.Modules.pullback g).obj M)) _
      (comp_lift_id η _)).2 n
  have hcochain : IsIso ((homologyFunctor (ModuleCat R') _ n).map
      (scalarResolutionSectionsBaseChangeMap φ f f' g w t)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  have h := resolutionComparison_scalarBaseChangeMap_homology φ f f' g w ε η t ht hφ hM n
  have : IsIso ((ModuleCat.extendScalars φ.hom).map
      (resolutionComparison (relativeGlobalSections f) ε n) ≫
      scalarBaseChangeMap φ f f' g w M hM n) := by
    rw [h]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hcochain htarget)
  exact IsIso.of_isIso_comp_left
    ((ModuleCat.extendScalars φ.hom).map (resolutionComparison (relativeGlobalSections f) ε n))
    (scalarBaseChangeMap φ f f' g w M hM n)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
