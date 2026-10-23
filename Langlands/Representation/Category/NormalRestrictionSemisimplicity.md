# Finite-dimensional normal restriction semisimplicity

Author: Worker 326.

The theorem `Langlands.finiteDimensionalNormalRestrictionSemisimplicity`
proves the published proposition
`Langlands.FiniteDimensionalNormalRestrictionSemisimplicity.{uR, uG, uV}`.
Its complete, unapplied type is exactly that proposition, with independent
coefficient, group, and carrier universes. Import
`Langlands.Representation.Category.NormalRestrictionSemisimplicity` to use it.

For any field `R`, group `G`, finite-dimensional `R`-module `V`, normal subgroup
`H`, and actual representation `ρ : Representation R G V`, semisimplicity of
`ρ` implies semisimplicity of `ρ.comp H.subtype`. Semisimplicity is Mathlib's
complemented lattice of subrepresentations. No finite-index, characteristic,
algebraic-closure, finite-image, topology, smoothness, irreducibility, or positive
dimension assumption occurs. The zero module is included. The input statement
and its imports are preserved.

## Implemented proof

The proof uses the socle of the restricted representation `σ = ρ.comp H.subtype`.
It works in the complete lattice of subrepresentations supplied by the published
`Langlands.Representation.SubrepresentationLattice` module. An atom of this
lattice is a nonzero subrepresentation with no proper nonzero
subrepresentation, hence a simple restricted submodule.

1. The private construction `pullback` sends an `H`-subrepresentation `W` to
   the preimage of its underlying subspace under `ρ(g)`. This preimage is
   `H`-stable: for `h ∈ H`, normality gives `ghg⁻¹ ∈ H`, and
   `ρ(g)ρ(h)v = ρ(ghg⁻¹)ρ(g)v`. The private `pullbackOrderIso` is an order
   automorphism, with inverse given by pullback under `ρ(g⁻¹)`.
2. Let `S` be the supremum of all atoms of the restricted subrepresentation
   lattice. An order automorphism preserves atoms and arbitrary suprema.
   Consequently each of the above pullbacks fixes `S`. This says precisely
   that its underlying subspace is `G`-stable, defining a
   `G`-subrepresentation `T`.
3. The given semisimplicity supplies a `G`-invariant complement `C` of `T`.
   Restrict this complement to obtain `C'`, an `H`-subrepresentation.
4. The forgetful map from `H`-subrepresentations to `R`-submodules is an order
   embedding. Finite dimensionality over a field makes the latter lattice
   well-founded under strict inclusion, by Mathlib's Artinian-module instance.
   Well-foundedness transfers along this embedding, making the restricted
   subrepresentation lattice atomic. Thus `C'` is either zero or contains
   an atom `A`. In the second case, `A` lies in `S` by its definition and in
   `C'` by construction. Their disjointness forces `A = 0`, contradicting
   that it is an atom. Therefore `C' = 0`, hence `C = 0` and `S = ⊤`.
5. The order isomorphism
   `Subrepresentation.subrepresentationSubmoduleOrderIso` transports this
   equality to the submodule lattice of `σ.asModule` over the group algebra
   `R[H]`. Mathlib's `isSimpleModule_iff_isAtom` identifies its atoms with
   simple submodules. Then `IsSemisimpleModule.of_sSup_simples_eq_top` gives
   semisimplicity of this module, and
   `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`
   gives the desired representation semisimplicity.

The complement is derived from the input semisimplicity; it is not an
additional hypothesis. Atomicity is used as a disjunction that includes the
zero subrepresentation, so the proof needs no separate nonzero-carrier
assumption. There is no averaging and no division by a subgroup index.

## Provenance and original-source boundary

This is an internal finite-dimensional Clifford/socle argument motivated by
I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68, English translation. Registered source:
`bernstein-zelevinsky-1976-representations-gln`; SHA-256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Worker 326 read printed pages 15–17, also PDF pages 15–17, in the registered
original. No source-specific errata note was found in the supplied Library.

Page 15 fixes complex coefficient spaces. Lemma–Definition 2.7 on page 16
identifies complete reducibility with generation by simple submodules and
with existence of invariant complements. Lemma 2.9(b) on page 17 concerns an
irreducible complex representation and a normal subgroup of finite index;
its proof uses a simple quotient, finitely many translated quotient kernels,
and an embedding into their finite direct sum. It gives an index bound on
the number of simple summands and does not assume finite dimension.

The theorem proved here instead allows arbitrary fields, assumes finite
dimension and semisimple input, and has no index hypothesis or summand bound.
These changes and the implemented socle proof are internal mathematics,
not a verbatim formalization of the source's finite-index quotient argument.
Finite-index restriction equivalence, induction semisimplicity, local Weil
specializations, and local Langlands targets are outside this proof.
