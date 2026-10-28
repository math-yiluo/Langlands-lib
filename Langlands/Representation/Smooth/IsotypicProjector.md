# Isotypic projectors from a nondegenerate test pairing

This module is purely algebraic. For an admissible irreducible representation
`σ` and a representation `ρ` with finite-dimensional `Hom(σ, ρ)`, it builds an
idempotent self-intertwiner of `ρ` onto the `σ`-isotypic subrepresentation
`⨆ f : σ.IntertwiningMap ρ, f.range`, from a single test functional that
detects every nonzero intertwiner `σ → ρ`. No topology on `G` is used except
in the admissibility hypothesis.

## Finite generation of irreducible representations

`Langlands.moduleFinite_asModule_of_isIrreducible` proves that the module
`σ.asModule` over `MonoidAlgebra ℂ G` of an irreducible representation `σ` is
finitely generated. Irreducibility makes it a simple module, hence nontrivial,
and any nonzero vector spans it. This instance is what the Library's
finiteness theorems for `Hom(σ, ρ)` require of the source.

## Idempotence from fixing every intertwiner

`Langlands.isotypicProjector_of_fixes` takes a self-intertwiner `P` of `ρ` with

- `hfix`: `P.comp f = f` for every `f : σ.IntertwiningMap ρ`, and
- `hmem`: `P v ∈ ⨆ f : σ.IntertwiningMap ρ, f.range` for every `v`,

and concludes `P.comp P = P ∧ P.range = ⨆ f : σ.IntertwiningMap ρ, f.range`.

By `hfix`, the range of each `f` lies in the kernel of `P - id`; since that
kernel is a submodule, it contains the supremum, using
`Subrepresentation.toSubmodule_iSup`. Thus `P` fixes the supremum pointwise.
Idempotence follows from `hmem`, and the range equality from `hmem` together
with this pointwise fixing.

## Dual-basis construction

`Langlands.exists_isotypicProjector_of_nondegenerate` assumes `σ` admissible and
irreducible, `Module.Finite ℂ (σ.IntertwiningMap ρ)`, a linear functional
`m : Module.Dual ℂ W` and a vector `u` with `m u ≠ 0`, and

`hnd`: for every nonzero `f : σ.IntertwiningMap ρ` there is
`r : ρ.IntertwiningMap σ` with `m (r (f u)) ≠ 0`.

It produces a self-intertwiner `P` of `ρ` satisfying exactly the two hypotheses
of `isotypicProjector_of_fixes`.

The proof considers the bilinear pairing
`β(r, f) = m (r (f u))` between `Hom(ρ, σ)` and `Hom(σ, ρ)`. Hypothesis `hnd`
says that `β.flip` is injective. Since `Hom(σ, ρ)` is finite-dimensional,
`LinearMap.flip_injective_iff₂` makes `β` surjective onto the dual of
`Hom(σ, ρ)`. Choose a basis `b` of `Hom(σ, ρ)` and maps `r i` with
`β(r i, -) = m u • b.coord i`.

For each `i` and `f`, the composite `(r i).comp f` is a self-intertwiner of the
admissible irreducible `σ`, hence a scalar `c` by the Library's
`admissibleSchur_scalarEndomorphism`. Evaluating `m (· u)` gives
`c * m u = m u * b.coord i f`, so `c = b.coord i f` after cancelling `m u ≠ 0`.
Therefore `(r i).comp f = b.coord i f • id`.

Set `P = ∑ i, (b i).comp (r i)`. Then
`P (f v) = ∑ i, b.coord i f • b i v = f v` by the basis expansion of `f`, which
is `hfix`. Each summand `b i (r i v)` lies in the range of `b i`, so `P v` lies
in the supremum, which is `hmem`.

## Provenance and scope

This is an internal derived argument. It replaces the formal-degree projector
of the coefficient-algebra route (Silberger 1979, proofs of Theorems 3.3.1 and
4.5.18, as recorded in
[TemperedDiscreteSeriesIsotypicStatement](../Classification/TemperedDiscreteSeriesIsotypicStatement.md))
by a finite-dimensional dual-basis construction plus Schur's lemma. The Library
supplies Schur's lemma for admissible irreducible representations
(`Smooth/Schur/Proof`), the subrepresentation lattice
(`SubrepresentationLattice`), and Mathlib at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435` supplies
`LinearMap.flip_injective_iff₂` (`LinearAlgebra/Dual/Lemmas.lean`).

Nothing here constructs the test functional or verifies `hnd`; in the
reduction proof that is done analytically. No statement about the kernel of
`P` is made in this module.
