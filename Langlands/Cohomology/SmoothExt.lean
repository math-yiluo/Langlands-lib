import Langlands.Cohomology.SmoothHomComplex
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Ext in the category of smooth representations

`Ext^n(V, -)` is the `n`-th right derived functor of equivariant Hom out of a
smooth representation `V`, computed with injective resolutions in the abelian
smooth category, which has enough injectives.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothExt

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- On underlying sets, equivariant Hom out of `V` is the ordinary coyoneda functor. -/
def homFunctorForgetIso (V : SmoothRep.{u, u, u} R G) :
    SmoothHomComplex.homFunctor R G V ⋙ forget (ModuleCat.{u} R) ≅ coyoneda.obj (op V) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Equivariant Hom out of a fixed smooth representation is left exact. -/
instance homFunctor_preservesFiniteLimits (V : SmoothRep.{u, u, u} R G) :
    PreservesFiniteLimits (SmoothHomComplex.homFunctor R G V) := by
  have : PreservesFiniteLimits
      (SmoothHomComplex.homFunctor R G V ⋙ forget (ModuleCat.{u} R)) :=
    preservesFiniteLimits_of_natIso (homFunctorForgetIso R G V).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- `Ext^n(V, -)`, the right derived functors of equivariant Hom out of `V`. -/
def ext (V : SmoothRep.{u, u, u} R G) (n : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  (SmoothHomComplex.homFunctor R G V).rightDerived n

/-- A map of first arguments induces natural maps of Ext, contravariantly. -/
def extMap {V W : SmoothRep.{u, u, u} R G} (f : V ⟶ W) (n : ℕ) :
    ext R G W n ⟶ ext R G V n :=
  NatTrans.rightDerived ((linearCoyoneda R (SmoothRep.{u, u, u} R G)).map f.op) n

theorem extMap_id (V : SmoothRep.{u, u, u} R G) (n : ℕ) :
    extMap R G (𝟙 V) n = 𝟙 (ext R G V n) := by
  rw [extMap, op_id, CategoryTheory.Functor.map_id]
  exact NatTrans.rightDerived_id _ n

theorem extMap_comp {U V W : SmoothRep.{u, u, u} R G} (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    extMap R G (f ≫ g) n = extMap R G g n ≫ extMap R G f n := by
  rw [extMap, extMap, extMap, op_comp, CategoryTheory.Functor.map_comp]
  exact NatTrans.rightDerived_comp _ _ n

/-- The degree `n` Ext bifunctor on smooth representations. -/
def bifunctor (n : ℕ) :
    (SmoothRep.{u, u, u} R G)ᵒᵖ ⥤ SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R where
  obj V := ext R G V.unop n
  map f := extMap R G f.unop n
  map_id V := extMap_id R G V.unop n
  map_comp f g := extMap_comp R G g.unop f.unop n

/-- Ext is the cohomology of equivariant Hom into any injective resolution of the
second argument. -/
def isoHomologyOfInjectiveResolution (V : SmoothRep.{u, u, u} R G)
    {W : SmoothRep.{u, u, u} R G} (I : InjectiveResolution W) (n : ℕ) :
    (ext R G V n).obj W ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).obj
        (((SmoothHomComplex.homFunctor R G V).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (SmoothHomComplex.homFunctor R G V) n

/-- In degree zero, Ext is equivariant Hom. -/
def extZeroIso (V : SmoothRep.{u, u, u} R G) :
    ext R G V 0 ≅ SmoothHomComplex.homFunctor R G V :=
  (SmoothHomComplex.homFunctor R G V).rightDerivedZeroIsoSelf

/-- Ext vanishes in positive degrees on injective smooth representations. -/
theorem isZero_ext_succ_of_injective (V W : SmoothRep.{u, u, u} R G) [Injective W]
    (n : ℕ) : Limits.IsZero ((ext R G V (n + 1)).obj W) :=
  (SmoothHomComplex.homFunctor R G V).isZero_rightDerived_obj_injective_succ n W

end Langlands.Cohomology.SmoothExt
