import Langlands.Representation.CuspidalSupport.RationalBlockCenterReduction
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Transport of a complex algebra center to its categorical center, with actions. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uΓ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalBlockCenterActionTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
  (X : RationalInertiaBlock G π)

/-- A faithful actual Hom functor detects equality of ambient block morphisms. -/
theorem rationalInertiaBlock_hom_ext
    [(preadditiveCoyonedaObj X).Faithful]
    {Y Z : RationalInertiaBlock G π} (f g : Y.obj ⟶ Z.obj)
    (h : ∀ φ : X.obj ⟶ Y.obj, φ ≫ f = φ ≫ g) : f = g := by
  have hh : (ObjectProperty.homMk f : Y ⟶ Z) = ObjectProperty.homMk g := by
    apply (preadditiveCoyonedaObj X).map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    let φ' : X ⟶ Y := φ
    change φ' ≫ ObjectProperty.homMk f = φ' ≫ ObjectProperty.homMk g
    exact ObjectProperty.hom_ext _ (h φ'.hom)
  exact congrArg (fun k => k.hom) hh

variable [(preadditiveCoyonedaObj X).Full] [(preadditiveCoyonedaObj X).Faithful]
  {Γ : Type uΓ} [Monoid Γ]
  (a : MonoidAlgebra ℂ Γ ≃ₐ[ℂ] Subalgebra.center ℂ (End X.obj))

/-- Transfer an algebra-center parametrization to the actual categorical center. -/
def rationalInertiaBlockCenterFromEnd :
    MonoidAlgebra ℂ Γ ≃+* CatCenter (RationalInertiaBlock G π) :=
  a.toRingEquiv.trans (rationalInertiaBlockCenterEquiv G π X).symm

@[simp]
theorem rationalInertiaBlockCenterFromEnd_app_generator (f : MonoidAlgebra ℂ Γ) :
    ((rationalInertiaBlockCenterFromEnd G π X a f).app X).hom = (a f : End X.obj) := by
  change (rationalInertiaBlockCenterEquiv G π X
    ((rationalInertiaBlockCenterEquiv G π X).symm (a f)) : End X.obj) = _
  rw [RingEquiv.apply_symm_apply]

/-- The action on Hom modules is precomposition by the given central element. -/
theorem rationalInertiaBlockCenterFromEnd_comp
    (f : MonoidAlgebra ℂ Γ) (Y : RationalInertiaBlock G π) (φ : X.obj ⟶ Y.obj) :
    φ ≫ ((rationalInertiaBlockCenterFromEnd G π X a f).app Y).hom =
      (a f : End X.obj) ≫ φ := by
  have h := congrArg (fun k => k.hom)
    (CatCenter.naturality (rationalInertiaBlockCenterFromEnd G π X a f)
      (ObjectProperty.homMk φ : X ⟶ Y))
  change φ ≫ ((rationalInertiaBlockCenterFromEnd G π X a f).app Y).hom =
    ((rationalInertiaBlockCenterFromEnd G π X a f).app X).hom ≫ φ at h
  simpa only [rationalInertiaBlockCenterFromEnd_app_generator] using h

/-- Any scalar action on the Hom module is the same scalar action on the object. -/
theorem rationalInertiaBlockCenterFromEnd_scalar_action
    (f : MonoidAlgebra ℂ Γ) (Y : RationalInertiaBlock G π) (c : ℂ)
    (h : ∀ φ : X.obj ⟶ Y.obj, (a f : End X.obj) ≫ φ = c • φ) :
    ((rationalInertiaBlockCenterFromEnd G π X a f).app Y).hom = c • 𝟙 Y.obj := by
  apply rationalInertiaBlock_hom_ext G π X
  intro φ
  rw [rationalInertiaBlockCenterFromEnd_comp, h]
  simp

/-- Because the input parametrization is a complex algebra isomorphism,
its transferred categorical-center map acts on every object by the given scalars. -/
theorem rationalInertiaBlockCenterFromEnd_scalar
    (c : ℂ) (Y : RationalInertiaBlock G π) :
    ((rationalInertiaBlockCenterFromEnd G π X a (MonoidAlgebra.single 1 c)).app Y).hom =
      c • 𝟙 Y.obj := by
  apply rationalInertiaBlockCenterFromEnd_scalar_action G π X a _ Y c
  intro φ
  have hc : (a (MonoidAlgebra.single 1 c) : End X.obj) = c • 𝟙 X.obj := by
    change (a (algebraMap ℂ (MonoidAlgebra ℂ Γ) c) : End X.obj) = _
    rw [a.commutes]
    change algebraMap ℂ (End X.obj) c = _
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hc]
  simp

end Langlands.CuspidalSupport
