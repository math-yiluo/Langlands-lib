/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance

set_option linter.privateModule false

/-!
# Common-degree twists on a quasi-compact Proj open

The statement records the open `W_e` by its equivalent union of standard opens and records
the canonical multiplication maps by their action on all local pure tensors. They multiply
homogeneous fractions on the standard-open cover.

## References

* Stacks Project, Constructions, Tags 01MU and 01MW, the characterization of the invertibility locus
  and the proof after the finite standard-open cover
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

open ProjectiveSpectrum.Twist HomogeneousLocalization Opposite MonoidalCategory
open Scheme.Modules

attribute [local instance] SheafOfModules.monoidalCategory

private def mulSections (a b c : ℤ) (h : a + b = c)
    (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)) :
    Γ(twist 𝒜 c, U) :=
  ⟨fun x ↦ ⟨s.val x * t.val x, h ▸ mul_mem_degreePart (s.val x).property
    (t.val x).property⟩, isLocallyFraction_mul h s.property t.property⟩

private def mulBilinear (a b c : ℤ) (h : a + b = c) (U : (Proj 𝒜).Opens) :
    Γ(twist 𝒜 a, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twist 𝒜 b, U) →ₗ[Γ(Proj 𝒜, U)]
      Γ(twist 𝒜 c, U) :=
  LinearMap.mk₂ Γ(Proj 𝒜, U) (mulSections 𝒜 a b c h U)
    (by
      intro s s' t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact add_mul _ _ _)
    (by
      intro r s t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_assoc _ _ _)
    (by
      intro s t t'
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_add _ _ _)
    (by
      intro r s t
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact mul_left_comm _ _ _)

private theorem mulBilinear_natural (a b c : ℤ) (h : a + b = c)
    {U T : (Proj 𝒜).Opensᵒᵖ} (i : U ⟶ T)
    (s : (twist 𝒜 a).val.obj U) (t : (twist 𝒜 b).val.obj U) :
    mulBilinear 𝒜 a b c h T.unop ((twist 𝒜 a).val.map i s)
        ((twist 𝒜 b).val.map i t) =
      (twist 𝒜 c).val.map i (mulBilinear 𝒜 a b c h U.unop s t) := rfl

@[irreducible] private def tensorLift {X : Scheme.{u}} (F G H : X.Modules)
    (β : ∀ U : X.Opensᵒᵖ,
      F.val.obj U →ₗ[X.sheaf.obj.obj U] G.val.obj U →ₗ[X.sheaf.obj.obj U] H.val.obj U)
    (hβ : ∀ {U T : X.Opensᵒᵖ} (i : U ⟶ T) (s : F.val.obj U) (t : G.val.obj U),
      β T (F.val.map i s) (G.val.map i t) = H.val.map i (β U s t)) :
    F ⊗ G ⟶ H :=
  (SheafOfModules.tensor_bilinear_universal X.sheaf F G H β hβ).choose

@[irreducible] private def ambientMultiplication (a b c : ℤ) (h : a + b = c) :
    twist 𝒜 a ⊗ twist 𝒜 b ⟶ twist 𝒜 c :=
  tensorLift (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)
    (fun U ↦ mulBilinear 𝒜 a b c h U.unop) (mulBilinear_natural 𝒜 a b c h)

@[irreducible] private def restrictTensorHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G H : X.Modules) (φ : F ⊗ G ⟶ H) :
    F.restrict j ⊗ G.restrict j ⟶ H.restrict j :=
  (exists_restriction_tensor_comparison j F G).choose.inv ≫ (restrictFunctor j).map φ

@[irreducible] private def multiplication (V : (Proj 𝒜).Opens) (a b c : ℤ)
    (h : a + b = c) :
    Scheme.Modules.tensorObj ((twist 𝒜 a).restrict V.ι) ((twist 𝒜 b).restrict V.ι) ⟶
      (twist 𝒜 c).restrict V.ι :=
  restrictTensorHom V.ι (twist 𝒜 a) (twist 𝒜 b) (twist 𝒜 c)
    (ambientMultiplication 𝒜 a b c h)

end AlgebraicGeometry.Proj
