/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryInterface
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarProperOpen
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Section-normalized ordinary scalar restriction

Source: Stacks Project, Tags 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B;
blueprint fix-prop-coherence, coefficient comparisons of adjunction units and counits
(blueprint: lem-sf-semilinear-scalar-ordinary-comparison).

The existence theorem below supplies one simultaneous package on the actual ordinary
semilinear-system and strict-tower categories. Every comparison has a section or
adjunction normalization. The constant-tower beta, projector and alpha in the package
are fixed by the same intrinsic ordinary words as their varying-ring counterparts.
No choice of a package is made into a definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- Ordinary scalar restriction and all its section-normalized comparisons exist.
Source: Stacks 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B;
blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-ordinary-comparison).
Proof: restrict each level along psi and retain the section maps. Compatibility with
phi makes all transitions B-linear. These prescriptions define rho on objects and
morphisms. Restriction commutes with module sheafification: both actions uniquely extend
the same presheaf action on the same abelian sheafification. Hence kernels and cokernels
are unchanged, and componentwise exactness gives exactness on systems. Pushforward has
the same fibre-product sections, giving the identity comparison d. On inverse images
the transported B actions coincide by functoriality of inverse image and its finite-product
comparison; this gives b. The comparisons retain the underlying abelian unit and counit.
The mate formula, counit equation, naturality and the triangle identity give d = mate(b^-1).
The section formulas preserve direct-image composition; taking normalized adjoints
preserves inverse-image composition and identities. For opens, use the localized direct
sum extension presheaf: identity on each summand respects restricted scalars, the open
unit, the counit and the composite-open maps. Pass through sheafification to obtain a.
The transported cartesian beta has the same open-unit transpose and hence equals beta.
The open-to-direct comparison is the mate of the inverse open unit, so its clopen inverse
and the intrinsic projector are preserved. Substituting these equalities in the beta,
projector and compositor word proves preservation of alpha, even when the square is not
cartesian. No step uses coefficient flatness. -/
theorem ordinaryScalarComparison (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n) :
    Nonempty (OrdinaryScalarComparison R φ B ψ) := by
  obtain ⟨C⟩ := ordinaryScalarRestriction R φ B ψ hψ
  obtain ⟨G⟩ := ordinaryScalarAdjunctions R φ B ψ hψ C
  obtain ⟨P⟩ := ordinaryScalarProperOpen R φ B ψ hψ C G
  exact ⟨{
    rho := C.rho
    additive := C.additive
    limits := C.limits
    colimits := C.colimits
    level := C.level
    level_sections := C.level_sections
    transitions := C.transitions
    b := G.b
    d := G.d
    d_sections := G.d_sections
    unit := OrdinaryScalarAdjunctions.unit R φ B ψ C G
    counit := OrdinaryScalarAdjunctions.counit R φ B ψ C G
    mate := G.mate
    a := G.a
    open_unit := G.open_unit
    beta := P.beta
    beta_unit := P.beta_unit
    beta_comparison := P.beta_comparison
    clopen := P.clopen
    clopen_unit := P.clopen_unit
    pi := scalarOrdinaryPi B P.clopen
    pi_eq := by intros; rfl
    pi_comparison := P.pi_comparison
    alpha := P.alpha
    alpha_eq := P.alpha_eq
    alpha_comparison := P.alpha_comparison }⟩

end AlgebraicGeometry.ProEtale.VaryingRing
