import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Sheaf.Equivariant.Limits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exactness of forgetting equivariance

Forgetting the group-labelled transport arrows sends an equivariant module
sheaf to its underlying ordinary sheaf. This functor is additive. A covering
sieve of the transport topology covers through its label-one inclusions, so
transport local surjectivity gives ordinary local surjectivity. Hence the
functor preserves epimorphisms. With the published left exactness, it is
exact: it also preserves finite colimits.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u w' uX uG uA vA

section Additive

variable (G : Type uG) [Group G] (X : Type uX) [TopologicalSpace X] [MulAction G X]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) A]

/-- Forgetting equivariance is additive: morphisms are added on each open. -/
instance toSheaf_additive : (toSheaf G X A).Additive where
  map_add := rfl

end Additive

section LocallySurjective

variable {G : Type uG} [Group G] {X : Type uX} [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]
variable {A : Type uA} [Category.{vA} A] {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

/-- A transport-locally surjective morphism is locally surjective on ordinary opens. -/
theorem isLocallySurjective_underlyingPresheaf_map {P Q : (ActionOpens G X)ᵒᵖ ⥤ A}
    (φ : P ⟶ Q) [h : Presheaf.IsLocallySurjective (transportTopology G X) φ] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((underlyingPresheaf G X A).map φ) where
  imageSieve_mem {U} s := h.imageSieve_mem (U := (ActionOpens.inclusion G X).obj U) s

end LocallySurjective

section Module

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Forgetting equivariance preserves epimorphisms of equivariant module sheaves. -/
instance toSheaf_preservesEpimorphisms :
    (toSheaf G X (ModuleCat.{u} R)).PreservesEpimorphisms where
  preserves {F F'} f hf := by
    have hE : Epi ((sheafEquivalence G X (ModuleCat.{u} R)).functor.map f) := inferInstance
    have hS : Sheaf.IsLocallySurjective
        ((sheafEquivalence G X (ModuleCat.{u} R)).functor.map f) :=
      (Sheaf.isLocallySurjective_iff_epi'
        (φ := (sheafEquivalence G X (ModuleCat.{u} R)).functor.map f)).2 hE
    have hP : Presheaf.IsLocallySurjective (transportTopology G X) f.hom := hS
    have hU : Sheaf.IsLocallySurjective ((toSheaf G X (ModuleCat.{u} R)).map f) :=
      isLocallySurjective_underlyingPresheaf_map f.hom
    exact (Sheaf.isLocallySurjective_iff_epi'
      (φ := (toSheaf G X (ModuleCat.{u} R)).map f)).1 hU

/-- Forgetting equivariance preserves kernels, cokernels and homology. -/
instance toSheaf_preservesHomology :
    (toSheaf G X (ModuleCat.{u} R)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Forgetting equivariance is right exact. -/
instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (toSheaf G X (ModuleCat.{u} R)) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Forgetting equivariance, bundled as an exact functor between the abelian
categories of equivariant and ordinary module sheaves. -/
def toSheafExactFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ₑ TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) :=
  ExactFunctor.of (toSheaf G X (ModuleCat.{u} R))

@[simp]
theorem toSheafExactFunctor_obj :
    (toSheafExactFunctor R G X).obj = toSheaf G X (ModuleCat.{u} R) :=
  rfl

end Module

end Langlands.Sheaf.Equivariant
