/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.OpcyclesTorKernelIso
import WeilConjectures.CategoryTheory.TensorHomologyImageKernelEpi

/-!
# Tor of an opcycle cokernel

Source: Stacks Project, More on Algebra, Lemma 15.59.2 (Tag 0653), Tor argument
(blueprint: lem-pc-module-opcycles-tor-surjection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- (blueprint: lem-pc-module-opcycles-tor-surjection) For a complex of flat modules,
the cohomology one degree before an opcycle cokernel surjects naturally onto its first Tor.
Source: Stacks Project, More on Algebra, Tag 0653 (`lemma-last-one-flat`), Tor argument.

Step 1. Put `K = im(d^(a-1))` and factor the differential as a surjection `π` onto `K`
followed by its inclusion `ι` into `P^a`. The low-degree Tor sequence for
`0 -> K -> P^a -> P.opcycles a -> 0` (lem-weil-pbc-tor-long-exact-first-variable)
identifies `Tor_1(P.opcycles a, N)` with `ker(ι tensor 1)`. Indeed,
`Tor_1(P^a, N) = 0`: use Tor symmetry (lem-weil-pbc-tor-symmetry) and a free resolution
of `N` (def-weil-pbc-tor-modules). Tensoring its image sequence with the flat module
`P^a` is exact by flatness (def-weil-pbc-flat-ring-map) and tensor right exactness
(lem-weil-pbc-tensor-right-exact), so its first homology vanishes.

Step 2. Place `N` in degree zero (def-pc-tensor-complex-sheaves). The differential is
`(ι tensor 1) ∘ (π tensor 1)`, and `π tensor 1` is surjective by tensor right exactness.
It maps cycles into `ker(ι tensor 1)` and boundaries to zero: `π ∘ d^(a-2) = 0`
because its composite with the injective `ι` is `d^(a-1) ∘ d^(a-2) = 0`.
It therefore descends to cohomology (def-pc-acyclic-complex-modules).

Step 3. Given an element `y` of `ker(ι tensor 1)`, lift it along `π tensor 1` to `x`.
The factorization of the differential shows that `x` is a cycle, so its cohomology
class maps to `y`. Thus the descended map is surjective.

Step 4. Compose this surjection with the inverse of the Tor boundary isomorphism of
Step 1. Both the Tor boundary map (lem-weil-pbc-tor-long-exact-first-variable) and
`π tensor 1` commute with every module map `N -> N'`, giving naturality in `N`. -/
theorem exists_epi_homology_tensor_to_tor_opcycles
    (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ℤ) (hflat : ∀ i : ℤ, Module.Flat A (P.X i)) :
    ∃ τ : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj P ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) (a - 1)) ⟶
        (Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a),
      ∀ N : ModuleCat.{u} A, Epi (τ.app N) := by
  obtain ⟨e⟩ := nonempty_tor_opcycles_tensor_image_kernel_iso A P a (hflat a)
  obtain ⟨σ, hσ⟩ := exists_epi_tensor_homology_to_image_kernel A P a
  refine ⟨σ ≫ e.inv, fun N ↦ ?_⟩
  have : Epi (σ.app N) := hσ N
  change Epi (σ.app N ≫ e.inv.app N)
  infer_instance

end CategoryTheory
