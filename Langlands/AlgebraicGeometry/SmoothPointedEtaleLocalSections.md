# Pointed etale local sections of smooth morphisms: exact proof

Authors: Worker 1683 and Worker 1607. The Lean proof reuses Worker 1683's
draft supplied in the task context.

`Langlands.AlgebraicGeometry.smoothPointedEtaleLocalSections.{u}` proves
exactly `Langlands.AlgebraicGeometry.SmoothPointedEtaleLocalSectionsStatement.{u}`
from its Library module. It applies to arbitrary schemes `X` and `S`, a
smooth morphism `f : X → S`, a point `s : S`, and a prescribed morphism
`x₀ : Spec κ(s) → X` satisfying
`x₀ ≫ f = S.fromSpecResidueField s`. The universe `u` is arbitrary.

The result provides a scheme `U`, an etale map `p : U → S`, a morphism
`b : Spec κ(s) → U`, and a morphism `a : U → X`, with all three equations:

- `b ≫ p = S.fromSpecResidueField s`;
- `a ≫ f = p`;
- `b ≫ a = x₀`.

The last equation recovers the prescribed point as a scheme morphism,
including its residue-field map. The base can be nonreduced and
non-Noetherian; neither scheme is required to be affine or separated.

The proof introduces the proposition's quantified inputs, installs the
supplied smoothness proof `hf` as an instance, and applies the published
theorem `exists_pointed_etale_section` to the same `f`, `s`, `x₀`, and
compatibility equation. Its conclusion supplies the witnesses and all
three equations directly.

This is a derived proposition-level interface to the published
`Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction`.
That module also defines the actual constructor `pointedEtaleSection`.
Its companion Markdown explains the affine charts, residue-field
isomorphisms, polynomial specialization and etale tensor-product
construction that prove the existence theorem. In particular, the
algebraic factorization and inverse residue-field isomorphisms preserve
the original `x₀`, which gives the final equation above. This proof
introduces no additional geometric hypotheses.

The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
The broader relative torus-lifting and reductive-locus openness results
remain separate consumer obligations.
