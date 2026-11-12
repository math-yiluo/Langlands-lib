# Compact multiplicities and independence of compact coefficients

Module `Langlands.Representation.Compact.CompactMultiplicityIndependenceProof`.
Worker 88, Task 5345.

The theorem `Langlands.Renard.CompactRepresentation.compactMultiplicityIndependence`
proves exactly the published proposition
`Langlands.Renard.CompactRepresentation.CompactMultiplicityIndependenceStatements.{u, v}`.
Its two component theorems prove `CompactGroupMultiplicityStatement` and
`CompactCoefficientLinearIndependenceStatement`. The group and representation
carrier universes remain independent. The statement pair and its imports are
unchanged, and the proof adds no hypotheses.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The targets are the multiplicity formula following IV.1.1's Corollary,
printed p.89 / PDF p.95, and the compact-representation sentence in IV.3.3's
Corollary, printed p.102 / PDF p.108. These pages were read directly.

The module proves the formula by a finite isotypic decomposition and Schur's
lemma. For coefficient independence it reuses the published algebraic proof
in `CoefficientLinearIndependenceProof`, whose hypotheses are weaker than
those of the compact assertion. Thus this proof does not follow the source's
integration argument for IV.3.3. The three private module lemmas are internal
algebraic derivations used to implement IV.1.1.

## Finite isotypic components

For a complex algebra `R`, a simple `R`-module `S`, and an `R`-module `M`
with compatible complex scalars, `isotypic_eq_iSup_range` identifies Mathlib's
`isotypicComponent R M S` with the supremum of the ranges of all maps
`S →ₗ[R] M`. A nonzero map from a simple module is injective, so its range
is isomorphic to `S`; conversely any submodule isomorphic to `S` is such a
range. The zero map contributes only the bottom submodule.

Assume `S` and `Hom_R(S, M)` are finite dimensional over the complex numbers.
The lemma `finite_isotypic` chooses a finite basis of this Hom space.
Every map is a linear combination of these basis maps, so every map's range
lies in the finite sum of their ranges. Each range is finite dimensional as
an image of `S`. This proves finite dimensionality of the whole isotypic
component before any use of `finrank`.

## Computing the dimension

The lemma `finrank_isotypic` additionally takes a complex linear equivalence
`End_R(S) ≃ₗ[ℂ] ℂ`. Mathlib proves that the simple isotypic component is
semisimple and isotypic of type `S`. Its finite dimensionality implies finite
generation over `R`. The theorem `IsIsotypicOfType.linearEquiv_fun` therefore
gives an `R`-linear equivalence with `Fin n → S` for some natural number `n`.

Every map from `S` to `M` has range in this component. Restricting its
codomain, applying the displayed equivalence, and taking coordinates gives
a complex linear equivalence
`Hom_R(S, M) ≃ₗ[ℂ] (Fin n → End_R(S))`.
The implementation proves injectivity by the component equivalence and
surjectivity by assembling a family of endomorphisms into a map to the
finite product and composing with its inverse and the component inclusion.
Applying the supplied scalar-endomorphism equivalence in every coordinate
shows `dim Hom_R(S, M) = n`. Restricting the component equivalence to complex
scalars gives `dim I = n * dim S`, proving the desired formula, including
when the Hom space and the isotypic component are zero.

For `compactGroupMultiplicity`, take `R = MonoidAlgebra ℂ K`, and use the
actual group-algebra modules of `σ` and `π`. The published
`finiteDimensional_of_compact_irreducible` supplies finite dimensionality of
`σ`; each of its fixed-vector spaces is then finite dimensional, so `σ`
is admissible. The published `admissibleSchur_homEquiv`, applied to its
identity isomorphism, supplies the scalar-endomorphism equivalence.
Mathlib's complex linear equivalence between intertwiners and group-algebra
linear maps transfers the finite Hom hypothesis. Its order isomorphism
between subrepresentations and group-algebra submodules identifies the
statement's exact supremum of intertwiner ranges with this isotypic
component. Both finite dimensionality and the dimension identity transfer
back to the published subrepresentation.

## Coefficient independence

The theorem `compactCoefficientLinearIndependence` applies the published
`coefficients_linearIndependent_of_irreducible` to the family in the target,
using the underlying algebraic duals of its smooth functionals. A nonzero
smooth functional has a nonzero underlying functional because subtype
inclusion is injective.

That published theorem embeds each irreducible representation into the
right translation representation on `G → ℂ`, using the chosen nonzero
functional. The coefficient map is injective by irreducibility and its
value at the identity. Non-isomorphic simple representations have
independent isotypic components in this function representation, so the
chosen nonzero coefficients are linearly independent. The compactness,
Haar and unimodularity hypotheses of the target are retained without being
needed by this algebraic argument.

Finally `compactMultiplicityIndependence` pairs the two exact component
proofs. All results use the pinned Lean/Mathlib environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`.
