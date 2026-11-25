/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenDerivedTruncationComparison
import WeilConjectures.AlgebraicGeometry.KInjectiveSectionCycleComparison
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Surjectivity of affine cycle classes

Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: new-affine-algebra-kinjective-cycle-class-epi).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- Direct image of the cycle-class projection of an affine K-injective complex
with quasi-coherent cohomology is an epimorphism.
Source: Stacks Project, Tag 0AVW, the cohomology calculation in its proof;
Tag 08D4, parts (1) and (2), with bound one.
(blueprint: new-affine-algebra-kinjective-cycle-class-epi).

Proof: Fix an affine open V of Y and set U = f⁻¹V, also affine. Restriction
preserves quasi-coherence. Restriction also preserves K-injectivity, since it
is right adjoint to exact extension by zero (Tag 08BS). Thus I restricted to U
computes derived sections on U. Positive module cohomology on U vanishes by affine
vanishing. Sections on U commute with countable products. For E = Q(I), let
A = τ≤n I and B = τ≥n A, with canonical chain maps A → I and A → B.
B is H^n(I) placed in degree n. Derived sections of A → I induce an isomorphism
on H^n by left exactness (the complementary upper tail starts in degree n+1).
The lower tail τ≤(n-1)I has quasi-coherent cohomology and derived sections zero
in degrees n and n+1 by Tag 08D4 with N = 1. Its truncation triangle makes
H^n(RΓ(A)) → H^n(RΓ(B)) invertible. Bottom derived sections of B are Γ(U,H^n(I)).
Use the natural map from sections of a complex to its derived sections. It is
invertible on cohomology for I because I is K-injective. This does not require
its individual terms to be injective: a comparison to a K-injective resolution
is a homotopy equivalence, preserved by sections. Sections preserve kernels,
so H^n(Γ(A)) → H^n(Γ(I)) is invertible as well. Naturality for A → I now shows
that H^n(Γ(A)) → H^n(RΓ(A)) is invertible. Naturality for A → B identifies the
resulting isomorphism H^n(Γ(I)) → Γ(U,H^n(I)) with the raw cycle-class map:
A^n is the kernel of d^n and (A → B)^n is its homology quotient. This verifies
the identity of the map, rather than just existence of an unrelated isomorphism.
The chosen homology data identifies its K and π with these cycles and class map.
Surjectivity of that isomorphism gives a cycle representative for each section
of H^n(I) on U. Thus direct image of π is surjective on the affine-open basis
of Y and hence locally surjective. Local surjectivity is epimorphy in module
sheaves, including over f_*O_X: the forgotten sections and maps are unchanged.
The construction covers the zero complex, empty opens and every integer n. -/
theorem affine_algebra_kinjective_cycle_class_epi
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    Epi ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).map
      (I.sc n).homologyData.left.π) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let p := F.map (I.sc n).homologyData.left.π
  have hsurj (U : X.Opens) (hU : IsAffineOpen U) :
      Function.Surjective ((I.sc n).homologyData.left.π.val.app (Opposite.op U)) := by
    let E := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj (Opposite.op U)
    let := HasDerivedCategory.standard
      (SheafOfModules.{v} (moduleRings X.toRingedSpace))
    let := HasDerivedCategory.standard
      (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op U)))
    have : EnoughInjectives
        (SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    have hcomp := affine_open_derived_truncation_comparison X U hU I hI n
    have hiso := kInjective_section_cycle_comparison E I n hcomp
    let := hiso
    have hepi : Epi (E.map (I.sc n).homologyData.left.π) := by
      let h := (I.sc n).homologyData.left
      have hw : E.map h.f' ≫ E.map h.π = 0 := by
        rw [← E.map_comp, h.f'_π, E.map_zero]
      have hfac := CategoryTheory.Limits.cokernel.π_desc (E.map h.f') (E.map h.π) hw
      rw [← hfac]
      infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp hepi
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map p.val) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    have hs : Function.Surjective (p.val.app (Opposite.op V)) := by
      exact hsurj (f ⁻¹ᵁ V) (hV.preimage f)
    obtain ⟨z, hz⟩ := hs ((F.obj (I.sc n).homologyData.left.H).val.map
      (homOfLE hVW).op y)
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (moduleRings (directImageAlgebraSpace f))).map p) := hlocal
  exact (SheafOfModules.toSheaf (moduleRings (directImageAlgebraSpace f))).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

end AlgebraicGeometry
