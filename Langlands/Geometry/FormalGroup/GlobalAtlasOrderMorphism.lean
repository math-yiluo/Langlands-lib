import Langlands.Geometry.FormalGroup.AtlasOrderMorphism
import Langlands.Geometry.FormalGroup.GlobalAtlasMorphism
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction

/-! # Global order-linear formal maps and their atlas restrictions -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace OrderAction

variable {E : OrderAction D M} {E' : OrderAction D N} {E'' : OrderAction D P}

namespace Hom

/-- Evaluate the actual extended order-linear formal map on algebra points. -/
def onAlgebraPoints (f : Hom E E') (A : CommAlgCat.{v} R) :
    E.AlgebraPoint A →ₗ[D] E'.AlgebraPoint A :=
  (f.map (IsScalarTower.toAlgHom O R A)).onPoints

/-- These D-linear evaluations commute with changes of coefficient algebra. -/
theorem onAlgebraPoints_natural (f : Hom E E') {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : E.AlgebraPoint A) :
    E'.algebraMapPoints φ (f.onAlgebraPoints A x) =
      f.onAlgebraPoints B (E.algebraMapPoints φ x) :=
  f.val.onAlgebraPoints_natural φ.hom x

/-- The original order-linear formal map induces a D-module natural map. -/
def algebraPointNatTrans (f : Hom E E') :
    E.algebraPointFunctor ⟶ E'.algebraPointFunctor where
  app A := ModuleCat.ofHom (f.onAlgebraPoints A)
  naturality _ _ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.onAlgebraPoints_natural φ x).symm

/-- Restrict the actual natural map to Nilp. -/
def nilpAlgebraPointNatTrans (f : Hom E E') (π : R) :
    E.nilpAlgebraPointFunctor π ⟶ E'.nilpAlgebraPointFunctor π :=
  Functor.whiskerLeft (Nilp.forget R π) f.algebraPointNatTrans

@[simp]
theorem onAlgebraPoints_id (E : OrderAction D M) (A : CommAlgCat.{v} R)
    (x : E.AlgebraPoint A) : (id E).onAlgebraPoints A x = x := by
  simp only [onAlgebraPoints, map_id, onPoints_id]

@[simp]
theorem onAlgebraPoints_comp (g : Hom E' E'') (f : Hom E E')
    (A : CommAlgCat.{v} R) (x : E.AlgebraPoint A) :
    (g.comp f).onAlgebraPoints A x = g.onAlgebraPoints A (f.onAlgebraPoints A x) := by
  simp only [onAlgebraPoints, map_comp, onPoints_comp]

end Hom

namespace Iso

/-- Actual inverse order-linear formal maps give equivalences of algebra points. -/
def onAlgebraPoints (f : Iso E E') (A : CommAlgCat.{v} R) :
    E.AlgebraPoint A ≃ₗ[D] E'.AlgebraPoint A :=
  (f.map (IsScalarTower.toAlgHom O R A)).onPoints

/-- The evaluated actual inverse maps form a natural isomorphism. -/
def algebraPointNatIso (f : Iso E E') :
    E.algebraPointFunctor ≅ E'.algebraPointFunctor :=
  NatIso.ofComponents (fun A => (f.onAlgebraPoints A).toModuleIso) (by
    intro A B φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.hom.onAlgebraPoints_natural φ x).symm)

/-- Restrict the constructed natural isomorphism to Nilp. -/
def nilpAlgebraPointNatIso (f : Iso E E') (π : R) :
    E.nilpAlgebraPointFunctor π ≅ E'.nilpAlgebraPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) f.algebraPointNatIso

end Iso

end OrderAction

namespace BasicAtlas

variable {E : ModuleLaw.OrderAction D M} {E' : ModuleLaw.OrderAction D N}
variable {E'' : ModuleLaw.OrderAction D P}

/-- Restrict the original map through the actual order-linear chart comparisons. -/
def globalOrderChartHom (f : ModuleLaw.OrderAction.Hom E E') (a : R)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a)) :
    ModuleLaw.OrderAction.Hom
      ((E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha))
      ((E'.map (IsScalarTower.toAlgHom O R (Localization.Away a))).map
        (coefficientLift (O := O) a A ha)) :=
  (globalOrderChartIso E' a A ha).inv.comp
    ((f.map (IsScalarTower.toAlgHom O R A)).comp (globalOrderChartIso E a A ha).hom)

@[simp]
theorem globalOrderChartHom_val (f : ModuleLaw.OrderAction.Hom E E') (a : R)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a)) :
    (globalOrderChartHom f a A ha).val = globalChartHom f.val a A ha := rfl

/-- Global order-linear formal maps induce actual same-cover order-linear atlas maps. -/
def ofGlobalOrderHom (f : ModuleLaw.OrderAction.Hom E E') (s : Set R)
    (hs : Ideal.span s = ⊤) :
    OrderAction.Hom (ofGlobalCoverOrderAction E s hs)
      (ofGlobalCoverOrderAction E' s hs) rfl :=
  ⟨ofGlobalHom f.val s hs, by
    intro A b hb d
    exact (globalOrderChartHom f b.val A hb).commutes d⟩

@[simp]
theorem ofGlobalOrderHom_id (E : ModuleLaw.OrderAction D M) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalOrderHom (ModuleLaw.OrderAction.Hom.id E) s hs =
      OrderAction.Hom.id (ofGlobalCoverOrderAction E s hs) := by
  apply Subtype.ext
  exact ofGlobalHom_id M s hs

@[simp]
theorem ofGlobalOrderHom_comp (g : ModuleLaw.OrderAction.Hom E' E'')
    (f : ModuleLaw.OrderAction.Hom E E') (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalOrderHom (g.comp f) s hs =
      (ofGlobalOrderHom g s hs).comp (ofGlobalOrderHom f s hs) := by
  apply Subtype.ext
  exact ofGlobalHom_comp g.val f.val s hs

/-- Restrict both actual formal inverse maps to a supplied common cover. -/
def ofGlobalOrderIso (f : ModuleLaw.OrderAction.Iso E E') (s : Set R)
    (hs : Ideal.span s = ⊤) :
    OrderAction.Iso (ofGlobalCoverOrderAction E s hs)
      (ofGlobalCoverOrderAction E' s hs) rfl where
  hom := ofGlobalOrderHom f.hom s hs
  inv := ofGlobalOrderHom f.inv s hs
  inv_hom := by rw [← ofGlobalOrderHom_comp, f.inv_hom, ofGlobalOrderHom_id]
  hom_inv := by rw [← ofGlobalOrderHom_comp, f.hom_inv, ofGlobalOrderHom_id]

/-- The singleton D-linear comparison intertwines the actual original map. -/
theorem globalOrderPointEquiv_ofGlobalOrderHom (f : ModuleLaw.OrderAction.Hom E E')
    (A : CommAlgCat.{v} R) (x : (ofGlobalOrderAction E).Point A) :
    globalOrderPointEquiv E' A ((ofGlobalOrderHom f {1} (by simp)).onPoints A x) =
      f.onAlgebraPoints A (globalOrderPointEquiv E A x) := by
  exact globalPointEquiv_ofGlobalHom f.val A x

/-- The singleton functor comparison is natural in actual global order-linear maps. -/
theorem globalOrderPointFunctorIso_natural (f : ModuleLaw.OrderAction.Hom E E') :
    (ofGlobalOrderHom f {1} (by simp)).pointNatTrans ≫ (globalOrderPointFunctorIso E').hom =
      (globalOrderPointFunctorIso E).hom ≫
        Functor.whiskerRight f.algebraPointNatTrans (ModuleCat.uliftFunctor.{v + 1, v} D) := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ULift.up
    (globalOrderPointEquiv E' A ((ofGlobalOrderHom f {1} (by simp)).onPoints A x)) =
      ULift.up (f.onAlgebraPoints A (globalOrderPointEquiv E A x))
  exact congrArg ULift.up (globalOrderPointEquiv_ofGlobalOrderHom f A x)

/-- The same naturality square over the nilpotent coefficient category. -/
theorem globalOrderNilpPointFunctorIso_natural (f : ModuleLaw.OrderAction.Hom E E')
    (π : R) :
    (ofGlobalOrderHom f {1} (by simp)).nilpPointNatTrans π ≫
        (globalOrderNilpPointFunctorIso E' π).hom =
      (globalOrderNilpPointFunctorIso E π).hom ≫
        Functor.whiskerRight (f.nilpAlgebraPointNatTrans π)
          (ModuleCat.uliftFunctor.{v + 1, v} D) := by
  apply NatTrans.ext
  funext A
  exact congrArg (fun η => η.app A.obj) (globalOrderPointFunctorIso_natural f)

end BasicAtlas

end Langlands.FormalGroup.ModuleLaw
