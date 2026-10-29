import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Langlands.Cohomology.DerivedComparison

/-!
# Derived sections and higher direct images of actual scheme modules

For a scheme `X`, Mathlib's category `X.Modules` of sheaves of modules over
the structure sheaf is Grothendieck abelian, so it has enough injectives and
chosen injective resolutions. This file applies Mathlib's right-derived
functor construction to global sections, to global sections over an affine
base `Spec R`, and to the existing pushforward `Scheme.Modules.pushforward`.

For each of the three functors it records the right-derived functor in the
homotopy category, the right-derived functors `n ↦ (·).rightDerived n`, the
degree-zero identification with the original functor, the representing
cochain complex obtained from Mathlib's chosen injective resolution, and the
identification of the derived functors with the homology of the image of any
injective resolution.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}}

example : HasInjectiveResolutions X.Modules := inferInstance

section Global

variable (X)

/-- Global sections of an actual `𝒪_X`-module, as a module over `Γ(X, ⊤)`. -/
def globalSections : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

instance : (globalSections X).Additive :=
  inferInstanceAs (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).Additive

instance : PreservesFiniteLimits (globalSections X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))

/-- The right-derived global sections in the homotopy category. -/
def homotopyFunctor :
    X.Modules ⥤ HomotopyCategory (ModuleCat.{u} Γ(X, ⊤)) (ComplexShape.up ℕ) :=
  (globalSections X).rightDerivedToHomotopyCategory

/-- Sheaf cohomology `Hⁿ(X, -)` of actual `𝒪_X`-modules as `Γ(X, ⊤)`-modules. -/
def cohomology (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (globalSections X).rightDerived n

/-- Zeroth cohomology is global sections. -/
def cohomologyZeroIso : cohomology X 0 ≅ globalSections X :=
  (globalSections X).rightDerivedZeroIsoSelf

variable {X}

/-- Global sections applied to Mathlib's chosen injective resolution. -/
def complex (M : X.Modules) : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ :=
  ((globalSections X).mapHomologicalComplex _).obj (injectiveResolution M).cocomplex

/-- The derived global sections are represented by `complex M`. -/
def complexIso (M : X.Modules) :
    (homotopyFunctor X).obj M ≅ (HomotopyCategory.quotient _ _).obj (complex M) :=
  (injectiveResolution M).isoRightDerivedToHomotopyCategoryObj _

/-- `Hⁿ(X, M)` is the `n`-th homology of `complex M`. -/
def cohomologyIso (M : X.Modules) (n : ℕ) :
    (cohomology X n).obj M ≅ (complex M).homology n :=
  (injectiveResolution M).isoRightDerivedObj _ n

/-- `Hⁿ(X, M)` is computed by the global sections of any injective resolution. -/
def cohomologyIsoOfResolution {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    (cohomology X n).obj M ≅
      (((globalSections X).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj _ n

end Global

section Affine

variable {R : CommRingCat.{u}} (f : X ⟶ Spec R)

instance : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
instance : (moduleSpecΓFunctor (R := R)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- Global sections over the affine base `Spec R`, as an `R`-module:
the composite `Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`. -/
def relativeGlobalSections : X.Modules ⥤ ModuleCat.{u} R :=
  Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor

instance : (relativeGlobalSections f).Additive :=
  inferInstanceAs (Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor).Additive

instance : PreservesFiniteLimits (relativeGlobalSections f) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor))

/-- The ring map `R → Γ(X, ⊤)` given by `f : X ⟶ Spec R`. -/
def structureRingHom : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- The `R`-module global sections are the `Γ(X, ⊤)`-module global sections
with scalars restricted along `structureRingHom f`. -/
def relativeGlobalSectionsIso :
    globalSections X ⋙ ModuleCat.restrictScalars (structureRingHom f).hom ≅
      relativeGlobalSections f :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The right-derived `R`-module global sections in the homotopy category. -/
def relativeHomotopyFunctor :
    X.Modules ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℕ) :=
  (relativeGlobalSections f).rightDerivedToHomotopyCategory

/-- Cohomology `Hⁿ(X, -)` of actual `𝒪_X`-modules as `R`-modules. -/
def relativeCohomology (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R :=
  (relativeGlobalSections f).rightDerived n

/-- Zeroth `R`-module cohomology is `R`-module global sections. -/
def relativeCohomologyZeroIso : relativeCohomology f 0 ≅ relativeGlobalSections f :=
  (relativeGlobalSections f).rightDerivedZeroIsoSelf

/-- `R`-module global sections applied to Mathlib's chosen injective resolution. -/
def relativeComplex (M : X.Modules) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((relativeGlobalSections f).mapHomologicalComplex _).obj (injectiveResolution M).cocomplex

/-- The derived `R`-module global sections are represented by `relativeComplex f M`. -/
def relativeComplexIso (M : X.Modules) :
    (relativeHomotopyFunctor f).obj M ≅
      (HomotopyCategory.quotient _ _).obj (relativeComplex f M) :=
  (injectiveResolution M).isoRightDerivedToHomotopyCategoryObj _

/-- The `R`-module `Hⁿ(X, M)` is the `n`-th homology of `relativeComplex f M`. -/
def relativeCohomologyIso (M : X.Modules) (n : ℕ) :
    (relativeCohomology f n).obj M ≅ (relativeComplex f M).homology n :=
  (injectiveResolution M).isoRightDerivedObj _ n

/-- The `R`-module `Hⁿ(X, M)` is computed by any injective resolution. -/
def relativeCohomologyIsoOfResolution {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    (relativeCohomology f n).obj M ≅
      (((relativeGlobalSections f).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj _ n

/-- The `R`-module cohomology is the `Γ(X, ⊤)`-module cohomology with scalars
restricted along `structureRingHom f`. -/
def relativeCohomologyRestrictScalarsIso (n : ℕ) :
    cohomology X n ⋙ ModuleCat.restrictScalars (structureRingHom f).hom ≅
      relativeCohomology f n :=
  Langlands.Cohomology.DerivedComparison.rightDerivedCompIso (globalSections X)
      (ModuleCat.restrictScalars (structureRingHom f).hom) (𝟭 _) (relativeGlobalSections f)
      (relativeGlobalSectionsIso f ≪≫ (Functor.leftUnitor _).symm) n ≪≫
    Functor.leftUnitor _

end Affine

section DirectImage

variable (f : X ⟶ Y)

instance : PreservesFiniteLimits (Scheme.Modules.pushforward f) := inferInstance

/-- The right-derived pushforward in the homotopy category of `Y.Modules`. -/
def directImageHomotopyFunctor :
    X.Modules ⥤ HomotopyCategory Y.Modules (ComplexShape.up ℕ) :=
  (Scheme.Modules.pushforward f).rightDerivedToHomotopyCategory

/-- The higher direct image `Rⁿ f_*` of actual `𝒪_X`-modules. -/
def higherDirectImage (n : ℕ) : X.Modules ⥤ Y.Modules :=
  (Scheme.Modules.pushforward f).rightDerived n

/-- The zeroth higher direct image is the pushforward. -/
def higherDirectImageZeroIso : higherDirectImage f 0 ≅ Scheme.Modules.pushforward f :=
  (Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf

/-- The pushforward applied to Mathlib's chosen injective resolution. -/
def directImageComplex (M : X.Modules) : CochainComplex Y.Modules ℕ :=
  ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj (injectiveResolution M).cocomplex

/-- The derived pushforward is represented by `directImageComplex f M`. -/
def directImageComplexIso (M : X.Modules) :
    (directImageHomotopyFunctor f).obj M ≅
      (HomotopyCategory.quotient _ _).obj (directImageComplex f M) :=
  (injectiveResolution M).isoRightDerivedToHomotopyCategoryObj _

/-- `Rⁿ f_* M` is the `n`-th homology of `directImageComplex f M`. -/
def higherDirectImageIso (M : X.Modules) (n : ℕ) :
    (higherDirectImage f n).obj M ≅ (directImageComplex f M).homology n :=
  (injectiveResolution M).isoRightDerivedObj _ n

/-- `Rⁿ f_* M` is computed by the pushforward of any injective resolution. -/
def higherDirectImageIsoOfResolution {M : X.Modules} (I : InjectiveResolution M) (n : ℕ) :
    (higherDirectImage f n).obj M ≅
      (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj _ n

end DirectImage

end Langlands.AlgebraicGeometry.Modules.DerivedSections
