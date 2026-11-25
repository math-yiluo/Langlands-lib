/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-!+# Normalized finite-free cokernel resolutions on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 06YQ; Homology, Tag 0115;
Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat).

The cone of the degree-zero map represents the two-term complex with differential `+u`.
Its augmentation uses the specified cokernel projection, without choosing another map.
-/

@[expose] public section

set_option autoImplicit false

universe a b u v r

open CategoryTheory CategoryTheory.Limits

private lemma flat_finite_coproduct
    {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] {I : Type} [Finite I]
    (F : I → D) (hF : ∀ i, ObjectProperty.flat (F i)) :
    ObjectProperty.flat (∐ F) := by
  have : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  have (i : I) : PreservesFiniteLimits (MonoidalCategory.tensorLeft (F i)) := (hF i).1.1
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesColimit (Discrete.functor F) (MonoidalCategory.curriedTensor D) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  have e : MonoidalCategory.tensorLeft (∐ F) ≅
      (Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip ⋙ colim :=
    preservesColimitIso (MonoidalCategory.curriedTensor D) (Discrete.functor F) ≪≫
      colimitIsoFlipCompColim _
  have : PreservesFiniteLimits
      ((Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (MonoidalCategory.tensorLeft (F j.as))))
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := D)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  have := comp_preservesFiniteLimits
    ((Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip)
    (colim (J := Discrete I) (C := D))
  exact preservesFiniteLimits_of_natIso e.symm

namespace CochainComplex

section Construction

variable {A : Type a} [Category.{b} A] [Abelian A]

/-- The two-term complex of a morphism, represented by the canonical cone on its
degree-zero single complex. Under the canonical identifications its terms are `P` in
degree `-1`, `Q` in degree `0`, and zero elsewhere; its differential is `+u`.
Source: Stacks Project, Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelComplex {P Q : A} (u : P ⟶ Q) : CochainComplex A ℤ :=
  mappingCone ((singleFunctor A 0).map u)

/-- The specified quotient augmentation: zero on the shifted source summand and the
given projection on the unshifted target summand. `S.zero` is exactly the condition
that the projection kills the differential; no exactness is needed to construct it.
Source: Stacks Project, Derived Categories, discussion before Tag 0152
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelAugmentation (S : ShortComplex A) :
    monoCokernelComplex S.f ⟶ (singleFunctor A 0).obj S.X₃ :=
  mappingCone.descShortComplex (S.map (singleFunctor A 0))

end Construction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

end CochainComplex
