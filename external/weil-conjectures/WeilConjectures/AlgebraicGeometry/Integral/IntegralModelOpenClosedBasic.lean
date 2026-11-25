/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Concrete continuous-coefficient functors for open and closed immersions

## References

* Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.13
* Stacks Project, Tags 09BN and 00XZ, and the localization used in Tag 03DI
* Stacks Project, Tags 09AA and 03D6
* Bhatt--Scholze, Definition 6.8.1
* Bhatt--Scholze, Lemma 6.8.13
* Stacks Project, Tag 03EK
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Regard a module on the open scheme as a module on the slice site. The concrete
site equivalence retains the underlying schemes and maps, so the coefficient map is
sectionwise the identity on continuous functions. Only the site presentation changes. -/
def openSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ⥤
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  letI := Scheme.ProEt.sliceDense X U
  letI : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforward (F := (Scheme.ProEt.sliceEquiv X U).functor)
    (J := (Scheme.ProEt.topology X).over U) (K := Scheme.ProEt.topology U.left)
    (S := (latticeModuleRing X T).over U) (R := latticeModuleRing U.left T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Direct image with the continuous coefficient action. First restrict scalars along
the canonical coefficient inverse-image map, then apply the ringed direct
image. Its action is through the adjoint continuous-function pullback map. -/
def continuousModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y T) :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousCoefficientInverseImageMap f T)) ⋙
    Scheme.proEtaleRingedDirectImage f (latticeCoefficientSheaf Y T)

/-- Extension by zero with continuous coefficients: use the concrete slice-site
transport, followed by the direct-sum presheaf extension and sheafification. -/
def continuousModuleExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :=
  openSliceModules U T ⋙ Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T)

/-- Ordinary rationalization `E_X ⊗_{A_X} M`, as the sheafified
sectionwise change of rings along the continuous integral inclusion. -/
def integralModelRationalize (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M

end AlgebraicGeometry.ProEtale
