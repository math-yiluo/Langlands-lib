/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # The kernel construction for local subobjects

Source: Stacks Project, Sites, Tag 04TR, expressed using kernels and pushforwards.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
variable (X : Scheme.{u}) (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
  (L : ∀ i, Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
  (q : ∀ i, L i ⟶ (upperStar Ab.{u + 1} (U.f i)).obj Q)

/-- The simultaneous local quotient map: adjoint each local cokernel map and
assemble the resulting maps to pushforwards into a product.
(auxiliary; not a blueprint node). -/
noncomputable def localSubobjectQuotientMap : Q ⟶
    ∏ᶜ fun i => (lowerStar Ab.{u + 1} (U.f i)).obj (cokernel (q i)) :=
  Pi.lift fun i => (upperStarLowerStarAdjunction Ab.{u + 1} (U.f i)).homEquiv _ _
    (cokernel.π (q i))

/-- The global subobject cut out by membership in every local subobject.
It is an actual kernel construction, with no choice from a descent theorem.
(auxiliary; not a blueprint node). -/
noncomputable def localSubobjectKernel : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  kernel (localSubobjectQuotientMap X Q U L q)

/-- Inclusion of the kernel subobject in the ambient sheaf. -/
noncomputable def localSubobjectKernelι : localSubobjectKernel X Q U L q ⟶ Q :=
  kernel.ι (localSubobjectQuotientMap X Q U L q)

instance : Mono (localSubobjectKernelι X Q U L q) := by
  unfold localSubobjectKernelι
  infer_instance

/-- The kernel inclusion vanishes in each local quotient. -/
theorem localSubobjectKernel_local_zero (i : U.I₀) :
    (upperStar Ab.{u + 1} (U.f i)).map (localSubobjectKernelι X Q U L q) ≫
      cokernel.π (q i) = 0 := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (U.f i)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homAddEquiv_zero]
  have h := congrArg (fun t => t ≫ Pi.π _ i)
    (kernel.condition (localSubobjectQuotientMap X Q U L q))
  simpa only [Category.assoc, localSubobjectKernel, localSubobjectKernelι,
    localSubobjectQuotientMap, Pi.lift_comp_π, zero_comp] using h

/-- The canonical local comparison, obtained by the kernel property of a
monomorphism in the abelian category of sheaves. -/
noncomputable def localSubobjectKernelComparison (hq : ∀ i, Mono (q i)) (i : U.I₀) :
    (upperStar Ab.{u + 1} (U.f i)).obj (localSubobjectKernel X Q U L q) ⟶ L i := by
  have := hq i
  exact Abelian.monoLift (q i)
    ((upperStar Ab.{u + 1} (U.f i)).map (localSubobjectKernelι X Q U L q))
    (localSubobjectKernel_local_zero X Q U L q i)

/-- The canonical comparison commutes with the inclusions. -/
theorem localSubobjectKernelComparison_comp (hq : ∀ i, Mono (q i)) (i : U.I₀) :
    localSubobjectKernelComparison X Q U L q hq i ≫ q i =
      (upperStar Ab.{u + 1} (U.f i)).map (localSubobjectKernelι X Q U L q) := by
  have := hq i
  exact Abelian.monoLift_comp _ _ _

instance (hq : ∀ i, Mono (q i)) (i : U.I₀) :
    Mono (localSubobjectKernelComparison X Q U L q hq i) := by
  have : Mono ((upperStar Ab.{u + 1} (U.f i)).map
      (localSubobjectKernelι X Q U L q)) := inferInstance
  have : Mono (localSubobjectKernelComparison X Q U L q hq i ≫ q i) := by
    rw [localSubobjectKernelComparison_comp]
    infer_instance
  exact mono_of_mono (localSubobjectKernelComparison X Q U L q hq i) (q i)

/-- The opposite inclusion suffices for effectivity: it factors through the
restricted kernel, and monicity proves that the two comparisons are inverse. -/
theorem isIso_localSubobjectKernelComparison_of_zero (hq : ∀ i, Mono (q i))
    (i : U.I₀)
    (hzero : q i ≫ (upperStar Ab.{u + 1} (U.f i)).map
      (localSubobjectQuotientMap X Q U L q) = 0) :
    IsIso (localSubobjectKernelComparison X Q U L q hq i) := by
  let B := upperStar Ab.{u + 1} (U.f i)
  have hw : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ (.mk i)
  have : PreservesLimitsOfShape WalkingParallelPair
      (localizationRestriction Ab.{u + 1} (U.f i) hw) := by
    unfold localizationRestriction
    infer_instance
  have : PreservesLimitsOfShape WalkingParallelPair B := by
    exact preservesLimitsOfShape_of_natIso
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (U.f i) hw).symm
  let t : L i ⟶ B.obj (localSubobjectKernel X Q U L q) :=
    kernel.lift (B.map (localSubobjectQuotientMap X Q U L q)) (q i) hzero ≫
      (PreservesKernel.iso B (localSubobjectQuotientMap X Q U L q)).inv
  have ht : t ≫ B.map (localSubobjectKernelι X Q U L q) = q i := by
    simp only [t, localSubobjectKernelι, Category.assoc,
      PreservesKernel.iso_inv_ι, kernel.lift_ι]
  have := hq i
  exact ⟨⟨t, by
    apply (cancel_mono (B.map (localSubobjectKernelι X Q U L q))).mp
    rw [Category.assoc, ht, localSubobjectKernelComparison_comp, Category.id_comp]
  , by
    apply (cancel_mono (q i)).mp
    rw [Category.assoc, localSubobjectKernelComparison_comp, ht, Category.id_comp]⟩⟩

/-- Any morphism locally factoring through all the prescribed subobjects factors
through the constructed kernel. This uses only the adjunction and kernel API. -/
theorem localSubobjectKernel_lift
    (Z : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (m : Z ⟶ Q)
    (h : ∀ i, ∃ t : (upperStar Ab.{u + 1} (U.f i)).obj Z ⟶ L i,
      t ≫ q i = (upperStar Ab.{u + 1} (U.f i)).map m) :
    ∃ t : Z ⟶ localSubobjectKernel X Q U L q,
      t ≫ localSubobjectKernelι X Q U L q = m := by
  have hm : m ≫ localSubobjectQuotientMap X Q U L q = 0 := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, localSubobjectQuotientMap, Pi.lift_comp_π, zero_comp]
    rw [← Adjunction.homEquiv_naturality_left]
    obtain ⟨t, ht⟩ := h i
    rw [← ht, Category.assoc, cokernel.condition, comp_zero]
    exact (upperStarLowerStarAdjunction Ab.{u + 1} (U.f i)).homAddEquiv_zero _ _
  exact ⟨kernel.lift _ m hm, kernel.lift_ι _ m hm⟩
end AlgebraicGeometry.ProEtale
