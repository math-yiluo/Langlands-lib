# Casselman's theorem for 𝔤𝔩_n(ℂ) from the Bernstein–Gelfand inputs

Module: `Langlands.Representation.Archimedean.ComplexJacquetModuleFiniteReduction`.

## Statement

`Langlands.Archimedean.ComplexJacquetModuleFiniteReductionStatement.{uV}` is the implication

`VermaGL.BernsteinGelfandInputsStatement.{uV, uV} → ComplexJacquetModuleFiniteStatement.{uV}`.

Both sides are Library statements:

- `BernsteinGelfandInputsStatement` (module `LowerVerma`) is the conjunction of six facts about
  lower Verma modules `M⁻(λ)` of `𝔤𝔩_n(ℂ)`:
  1. the weight-`λ` space of the generator;
  2. Duflo's theorem;
  3. Kostant's multiplicity lower bound;
  4. every central character comes from a `Z`-extremal `λ`;
  5. the upper bound for equivariant maps into `End M⁻(λ)`;
  6. projectivity of `M⁻(λ)`.

  Its two universe parameters are both set to `uV`. They are the universes of the auxiliary
  finite-dimensional representations and of the target spaces.
- `ComplexJacquetModuleFiniteStatement` (module `ComplexJacquetReduction`) is Casselman's
  theorem in algebraic form for `(𝔤𝔩_n(ℂ), U(n))`-modules (Wallach 1979, 4.13 and 4.14, for the
  upper triangular Borel subalgebra). For an irreducible admissible module `V`, the Jacquet
  module `V/𝔫V` is finite-dimensional and nonzero.

So the statement reduces `ComplexJacquetModuleFiniteStatement` to the six Bernstein–Gelfand input
statements. Each of them is proved in its own module (listed in `ComplexJacquetModuleFiniteProof.md`).

## Provenance

Derived. The implication combines three implications that are already proved:

- the Bernstein–Gelfand reduction (J. Bernstein and S. Gelfand, *Tensor products of finite and
  infinite dimensional representations of semisimple Lie algebras*, Compositio Math. 41 (1980),
  Theorem 5.9 and its proof in 5.10), as specialized in `ComplexJacquetBimoduleReduction.md`;
- the bridge from Harish-Chandra bimodules to one-sided nonvanishing of the Jacquet module,
  described in `ComplexJacquetBimoduleBridge.md`. It checks that an irreducible admissible
  `(𝔤𝔩_n(ℂ), U(n))`-module, with its two commuting `𝔤𝔩_n(ℂ)` actions, satisfies the hypotheses
  of the bimodule statement;
- the Library's reduction of Casselman's theorem to one-sided nonvanishing
  (`ComplexJacquetOneSided.md`).

Chaining them into this single statement is ours.

## Proof

`complexJacquetModuleFiniteReduction` is the composite of three implications:

1. `complexJacquetBimoduleReduction` (Library, module `ComplexJacquetBimoduleReduction`):
   `BernsteinGelfandInputsStatement.{uV, uV} → ComplexJacquetBimoduleStatement.{uV}`;
2. `complexJacquetOneSided_of_bimodule` (helper module `ComplexJacquetBimoduleBridge`):
   `ComplexJacquetBimoduleStatement.{uV} → ComplexJacquetOneSidedStatement.{uV}`;
3. `complexJacquetModuleFinite_of_oneSided` (Library, module `ComplexJacquetOneSided`):
   `ComplexJacquetOneSidedStatement.{uV} → ComplexJacquetModuleFiniteStatement.{uV}`.

The bridge module has its own Markdown page. In outline, for an
irreducible admissible `(ρ, π)` it takes the commuting actions `ℓ = π̃(·, 0)` and `r = π̃(0, ·)`
of `𝔤𝔩_n(ℂ)`, and `E` the `U(n)`-span of a nonzero vector. It then proves the following:

- `E` is stable under `ℓ(Y) - r(Yᵀ)`;
- `E` is spanned by joint eigenvectors with integer eigenvalues of the `ℓ(E_pp) - r(E_pp)`. The
  eigenvalues are integers, and there are no Jordan blocks, by a circle argument in `U(n)`;
- `E` generates `V` under `ℓ`, by irreducibility;
- `ℓ` has an infinitesimal character.

## Use

The six input statements are proved in the Library, and `ComplexJacquetModuleFiniteProof` derives
`ComplexJacquetModuleFiniteStatement` as
`complexJacquetModuleFiniteReduction ⟨weight, duflo, kostant, central, homBound, projective⟩`.
