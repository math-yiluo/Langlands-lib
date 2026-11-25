/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
import WeilConjectures.AlgebraicGeometry.SingletonCechAugmentationIso
import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionsRestrictionComparison
import WeilConjectures.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Sections of a quasi-coherent resolution on a basic open

Source: Stacks, Tags 08C2, 08D2 and 08BS
(blueprint: lem-sc-principal-open-sections-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Taking sections on a basic open sends a resolution of a termwise quasi-coherent
complex to a quasi-isomorphism, even when the resolution is not termwise quasi-coherent.
Source: Stacks, Tags 08C2, 08D2 and 08BS
(blueprint: lem-sc-principal-open-sections-resolution-quasi-iso).

Proof:
1. Restrict the map to D(g). Restriction is exact and preserves K-injective complexes
   (Tag 08BS), so this is still a quasi-isomorphism into a K-injective complex.
2. On D(g), use the basis of all affine opens. Restriction preserves quasi-coherence;
   kernels, images and cokernels of maps of quasi-coherent modules are quasi-coherent.
   Thus on every member of this basis the terms of F, the differential cokernels and
   the cohomology sheaves have vanishing positive cohomology (01XB). This verifies all
   three acyclicity conditions of 08C2, not only vanishing on D(g) itself.
3. Apply 08C2 to the one-element cover of D(g) by itself. Its alternating total is
   exactly the section complex. The canonical map to derived sections is invertible.
   Computing derived sections using the given restricted resolution identifies this
   canonical map with the sections of i. The identification is first obtained for a
   K-injective resolution with injective terms, and then for any K-injective resolution
   by a homotopy equivalence between resolutions. Additive sections preserve that
   homotopy equivalence. Hence the displayed map is a quasi-isomorphism.
4. Forgetting from O(D(g))-modules to A-modules preserves and reflects homology
   isomorphisms. This gives exactly affineOpenSections. If D(g) is empty, both section
   complexes are zero, so the conclusion also holds. No truncation of F is assumed. -/
theorem principalOpenSections_resolution_quasiIso
    (A : Type u) [CommRing A] (g : A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso (((affineOpenSections A (PrimeSpectrum.basicOpen g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map i) := by
  let X := Spec (.of A)
  let U : X.Opens := PrimeSpectrum.basicOpen g
  let Y := U.toScheme
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  have : r.Additive := Functor.additive_of_preserves_binary_products r
  have : e.Additive := Functor.additive_of_preserves_binary_products e
  let Fr := (r.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let Jr := (r.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let F' := (e.mapHomologicalComplex (ComplexShape.up ℤ)).obj Fr
  let J' := (e.mapHomologicalComplex (ComplexShape.up ℤ)).obj Jr
  let i' := (e.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((r.mapHomologicalComplex (ComplexShape.up ℤ)).map i)
  have : CochainComplex.IsKInjective Jr := kInjective_of_restrict_open X.toRingedSpace U J
  have : CochainComplex.IsKInjective J' := inferInstance
  have : QuasiIso i' := inferInstance
  have hF' (n : ℤ) : (F'.X n).IsQuasicoherent := by
    have := hF n
    let c := (Scheme.Modules.overFunctorEquiv U).app (F.X n)
    have hq : ((Scheme.Modules.restrictFunctor U.ι).obj (F.X n)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor U.ι (F.X n)
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      c.symm hq
  have : IsAffine Y := IsAffineOpen.Spec_basicOpen (R := .of A) g
  let : HasDerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤))) :=
    HasDerivedCategory.standard _
  let V : Fin 1 → Y.Opens := fun _ ↦ ⊤
  have hV : iSup V = ⊤ := by simp [V]
  have hAffine (p : ℕ) (t : Fin (p + 1) → Fin 1) :
      IsAffineOpen (⨅ k, V (t k)) := by
    simpa [V] using isAffineOpen_top Y
  obtain ⟨⟨β, hβ⟩, hβIso, _⟩ :=
    qcoh_complex_alternating_cech_derived_sections Y 1 V hV hAffine F' hF'
  have : IsIso β := hβIso β hβ
  let S := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  have hα (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
      IsIso ((alternatingCechAugmentation V).app K) :=
    singletonCechAugmentation_isIso Y K
  have := hα J'
  have htotal : IsIso (DerivedCategory.Q.map ((alternatingCechTotalFunctor V).map i')) := by
    rw [← hβ J' i']
    infer_instance
  have := hα F'
  have hsections : IsIso (DerivedCategory.Q.map
      ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i')) := by
    have hn := congrArg DerivedCategory.Q.map ((alternatingCechAugmentation V).naturality i')
    simp only [Functor.map_comp] at hn
    have : IsIso (DerivedCategory.Q.map ((S.mapHomologicalComplex
        (ComplexShape.up ℤ)).map i') ≫
          DerivedCategory.Q.map ((alternatingCechAugmentation V).app J')) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (DerivedCategory.Q.map ((alternatingCechAugmentation V).app J'))
  apply (principalOpenSections_restriction_quasiIso_iff A g F J i).mpr
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hsections

end AlgebraicGeometry
