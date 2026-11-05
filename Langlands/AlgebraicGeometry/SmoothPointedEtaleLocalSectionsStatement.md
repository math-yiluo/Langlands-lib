# Pointed etale local sections of smooth morphisms

Author: Worker 1683.

`SmoothPointedEtaleLocalSectionsStatement.{u}` states the following, for any
universe `u`. Let `f : X → S` be a smooth morphism of arbitrary schemes,
let `s` be a point of `S`, and let `x₀ : Spec κ(s) → X` be a specified point
over the canonical residue-field morphism `Spec κ(s) → S`. There exist a
scheme `U`, an etale morphism `p : U → S`, a morphism
`b : Spec κ(s) → U`, and a morphism `a : U → X` satisfying all three equations

- `b ≫ p = S.fromSpecResidueField s`;
- `a ≫ f = p`;
- `b ≫ a = x₀`.

The last equation preserves the supplied point as a morphism, including its
map on residue fields. The morphism `p` need not be globally surjective.
The existence of `b` forces its image to contain `s`. There are no
Noetherian, affine, separatedness, or connectedness hypotheses.

## Provenance and intended derivation

This is a derived pointed refinement of the smooth local-section construction
in The Stacks Project, Lemma 37.38.6, Tag 055U, registered source
`stacks-055U-smooth-etale-local-sections-2026-11-02`, second proof. That source
allows a new separable residue-field point; the proposition here instead
starts with a supplied rational point and requires its exact recovery.
The additional refinement is justified by the following algebraic construction.

Locally a smooth algebra is standard etale over a polynomial algebra in
finitely many variables. The supplied rational point assigns finitely many
residue-field values to those variables. They lift to a single principal
localization of the base ring away from its prime. Specialize the polynomial
variables to those lifts and base change the standard etale presentation.
The resulting algebra is etale over that localization and hence over the
original base. The supplied point of the original standard etale algebra
gives a point of this base change with exactly the original residue field,
and the maps factor the original point. Passing to affine neighbourhoods
establishes the scheme statement. This reasoning uses standard etale
presentations, localization, and the supplied point; it does not require
choosing any extension of its residue field.

The existing `Langlands.AlgebraicGeometry.SmoothEtaleLocalSections` proves
an unpointed existence result and does not itself provide the last equation
above. This file only defines the pointed proposition; its proof and its
use in relative split-torus lifting and reductive-locus openness remain
separate obligations.
