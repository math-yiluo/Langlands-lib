/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

import WeilConjectures.AlgebraicGeometry.SectionAcyclicIncomingKernelImage
import WeilConjectures.AlgebraicGeometry.ShortComplexSectionComparison

/-! # The section class comparison for acyclic complexes

Source: Stacks Project, Tags 015J and 01E4.
(blueprint: lem-pc-section-cohomology-theta-acyclic)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical section-class map commutes homology with sections when both the
terms and the homology sheaves of a nonnegative complex are section-acyclic.
Source: Stacks Project, Tag 015J (the two Cartan--Eilenberg spectral sequences),
and Tag 01E4 (the cocycle-to-homology-sheaf map).
(blueprint: lem-pc-section-cohomology-theta-acyclic)

Proof: Restrict K to V and take a Cartan--Eilenberg injective resolution of this
nonnegative complex. Its first spectral sequence has E1 terms H^r(V,K^n|V).
Term acyclicity kills all rows r > 0, identifying the total cohomology with
H^p(K(V)). Its second spectral sequence has E2 terms H^r(V,H^n(K)|V): open
restriction is exact, so its homology objects are the restricted homology sheaves.
Homology acyclicity kills all columns r > 0, identifying the same total
cohomology with sections of H^p(K) over V. Both filtrations are finite in each
total degree, since the complex and resolution are nonnegative. Their composite
is the canonical map sending a section cocycle to its class in the homology
sheaf: the augmentation into the double resolution sends a cycle to the same
cycle, and the second edge projects it to homology. Exact sheafification commutes
with homology; its adjunction unit sends a presheaf cycle class to that same
sheaf class. This identifies the composite with sectionCohomologyTheta evaluated
at V, with precisely the homology evaluation comparison in its source. Since
that evaluation comparison is an isomorphism, the displayed map is invertible.
Degree zero uses the cycle kernel and augmentation, and an empty V gives zero
section groups, so neither case needs an exception. -/
theorem sectionCohomologyTheta_isIso_of_acyclic
    {Y : Scheme.{u}} (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (hterms : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.X n))))
    (hhomology : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.homology n)))) (p : ℕ) :
    IsIso (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op V)) := by
  obtain ⟨hkernel, himage⟩ :=
    section_acyclic_incoming_kernel_image K V hterms hhomology p 1 (by decide)
  exact shortComplex_sectionComparison_isIso (K.sc p) V hkernel himage

end AlgebraicGeometry.Scheme.Modules
