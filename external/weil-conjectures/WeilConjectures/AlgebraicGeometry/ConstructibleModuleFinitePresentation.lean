/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Finite presentations of constructible etale module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 59.73.6, Tag 095N
(blueprint: lem-weil-pbc-constructible-module-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A constructible module sheaf on a qcqs scheme has a presentation by finite sums of
extensions by zero from affine etale objects. We use the project's `ModuleCat Λ` encoding
of modules over the constant ring sheaf. In this encoding `P W` is the sheafification of
`V ↦ Λ[Hom(V,W)]`, with restriction by precomposition; it is `j_{W!} Λ_W`. Sheafifying
with constant coefficients or first extending scalars to the constant ring sheaf gives
the same free sheaf, by the free-Yoneda and sheafification adjunctions.

Proof, following Stacks Project, Etale Cohomology, Lemma 59.73.6 (Tag 095N):
1. An affine etale object's extension by zero is constructible
   (`lem-weil-pbc-etale-free-sheaf-constructible`); finite sums are constructible by
   `thm-constructible-serre`, including the empty sum.
2. The free-Yoneda bijection (`lem-weil-pbc-free-yoneda-presheaf-module`) and the
   sheafification adjunction (`def-weil-presheaf-modules-sheafification`) turn a section
   over an etale object into a map from its extension by zero.
3. Finite stalks (`lem-weil-pbc-constructible-module-finite-stalks`) and the filtered
   colimit description (`definition-torsion-sheaves--3`,
   `lem-weil-pbc-filtered-colimit-modules-elementwise`) let us represent all stalk elements
   by finitely many sections; shrink their neighbourhoods to affine ones using
   `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`. These maps surject at that stalk.
4. For each finite family, its cokernel is constructible by `thm-constructible-serre`.
   Its support is constructible (`lem-weil-pbc-constructible-module-support-constructible`).
   Exactness of geometric stalks (`prop-weil-pbc-geometric-stalks-exact`) identifies this
   support with failure of stalkwise surjectivity; enlarging the family decreases it.
5. Choose a geometric point over each point (`def-weil-geometric-point`). Step 3 and
   independence of vanishing from the geometric point (the support lemma) give a finite
   family whose cokernel support avoids this point.
6. The qcqs scheme is spectral (`lem-weil-pbc-qcqs-scheme-spectral`). Compactness of its
   constructible topology (`lem-weil-pbc-spectral-constructible-finite-intersection`)
   makes finitely many such supports have empty intersection; concatenate their families.
7. The resulting cokernel has zero stalks. Conservativity
   (`lemma-weil-pbc-geometric-stalk-conservative`) makes it zero, so the map is epi.
8. Apply this construction to `F`, then to the constructible kernel of the resulting
   epimorphism `g` (again `thm-constructible-serre`). Compose the latter epimorphism with
   the kernel inclusion to obtain `f`. In the abelian module-sheaf category, `g` is its
   cokernel, giving the asserted cofork colimit.
(blueprint: lem-weil-pbc-constructible-module-finite-presentation). -/
theorem exists_affine_free_etale_presentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
      (∀ i : Fin n, IsAffine (U i).left) ∧ (∀ j : Fin m, IsAffine (V j).left) ∧
      ∃ (f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun i : Fin n => P (U i)))
        (g : (∐ fun i : Fin n => P (U i)) ⟶ F)
        (w : f ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g w)) := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  have hP (W : X.Etale) (hW : IsAffine W.left) :
      IsConstructibleSheaf (P W) := by
    have : IsAffine W.left := hW
    obtain ⟨e⟩ := free_etale_module_shriek_comparison X Λ W
    have hc := isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := X) (U := W.left) W.hom (ModuleCat.of Λ Λ)
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact IsConstructibleSheaf.of_iso e.symm
  obtain ⟨n, U, hU, g, hg⟩ := exists_affine_free_etale_epimorphism X Λ F hF
  have : Epi g := hg
  have : ∀ i : Fin n, IsConstructibleSheaf (P (U i)) := fun i ↦ hP (U i) (hU i)
  have := Abelian.hasFiniteBiproducts
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := IsConstructibleSheaf.biproduct (fun i : Fin n ↦ P (U i))
  have := IsConstructibleSheaf.of_iso
    (biproduct.isoCoproduct (fun i : Fin n ↦ P (U i)))
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  have := IsConstructibleSheaf.kernel g
  have hK := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (kernel g)).mpr
    (inferInstance : IsConstructibleSheaf (kernel g))
  obtain ⟨m, V, hV, h, hh⟩ := exists_affine_free_etale_epimorphism X Λ (kernel g) hK
  have : Epi h := hh
  refine ⟨n, m, U, V, hU, hV, h ≫ kernel.ι g, g, ?_, ?_⟩
  · simp
  · exact ⟨isCokernelEpiComp
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι g) (kernel.condition g)) (kernelIsKernel g)) h rfl⟩

end AlgebraicGeometry.Scheme
