import Langlands.Sheaf.Equivariant.Godement.Zero
import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Cohomology.CokernelComplex
import Mathlib.Topology.Sheaves.Abelian

/-!
# The equivariant Godement cokernel complex

Iterating the degree-zero equivariant Godement functor on successive cokernels
in the abelian category of equivariant module sheaves gives a cochain complex,
functorial in the sheaf, with the stalk-family coaugmentation in degree zero.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

omit [ContinuousConstSMul G X] in
/-- The induced map on a stalk is additive in the morphism of transport presheaves. -/
theorem stalkFunctor_map_add {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f g : F ⟶ F') (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
        ((underlyingPresheaf G X (ModuleCat.{u} R)).map (f + g)) =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
          ((underlyingPresheaf G X (ModuleCat.{u} R)).map f) +
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
          ((underlyingPresheaf G X (ModuleCat.{u} R)).map g) := by
  have h : (underlyingPresheaf G X (ModuleCat.{u} R)).map (f + g) =
      (underlyingPresheaf G X (ModuleCat.{u} R)).map f +
        (underlyingPresheaf G X (ModuleCat.{u} R)).map g := rfl
  rw [h, Functor.map_add]

/-- The degree-zero equivariant Godement functor is additive. -/
instance zeroFunctor_additive : (zeroFunctor R G X).Additive where
  map_add {F F' f g} := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    exact congrArg (fun a => a (s x)) (stalkFunctor_map_add R G X f.hom g.hom x.1)

/-- The equivariant Godement cokernel complex, functorial in the equivariant sheaf. -/
def complexFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤
      CochainComplex (TopologicalSheaf G X (ModuleCat.{u} R)) ℕ :=
  Langlands.Cohomology.CokernelComplex.functor (zeroFunctor R G X) (coaugmentation R G X)

/-- The equivariant Godement complex of one equivariant sheaf. -/
abbrev complex (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    CochainComplex (TopologicalSheaf G X (ModuleCat.{u} R)) ℕ :=
  (complexFunctor R G X).obj F

/-- Degree zero is the equivariant sheaf of stalk families. -/
theorem complex_X_zero (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (complex R G X F).X 0 = zeroSheaf F.obj :=
  rfl

/-- The coaugmentation from the sheaf into degree zero. -/
def augmentation (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    F ⟶ (complex R G X F).X 0 :=
  Langlands.Cohomology.CokernelComplex.augmentation
    (zeroFunctor R G X) (coaugmentation R G X) F

theorem augmentation_eq (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    augmentation R G X F = (coaugmentation R G X).app F :=
  rfl

@[reassoc (attr := simp)]
theorem augmentation_d (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    augmentation R G X F ≫ (complex R G X F).d 0 1 = 0 :=
  Langlands.Cohomology.CokernelComplex.augmentation_d _ _ F

instance (F : TopologicalSheaf G X (ModuleCat.{u} R)) : Mono (augmentation R G X F) :=
  mono_coaugmentation F

end Langlands.Sheaf.Equivariant.Godement
