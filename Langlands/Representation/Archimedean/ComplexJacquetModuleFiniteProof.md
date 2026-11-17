# Casselman's theorem for `(𝔤𝔩_n(ℂ), U(n))`-modules

Module `Langlands.Representation.Archimedean.ComplexJacquetModuleFiniteProof`, namespace
`Langlands.Archimedean`.

```lean
theorem complexJacquetModuleFinite : ComplexJacquetModuleFiniteStatement.{uV}
```

This proves the Library statement `ComplexJacquetModuleFiniteStatement` (module
`ComplexJacquetReduction`). Let `V` be an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module,
given by a representation `ρ` of `U(n)` and a complex Lie algebra map
`π : ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) → End V` with `IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and
`IsAdmissibleGKModule ρ`. Then the Jacquet module `V/𝔫V`, with `𝔫V = complexJacquetSubspace n π`,
is finite-dimensional and nonzero (`𝔫V ≠ ⊤`). This is Casselman's theorem in the algebraic
setting for the complex group `GL_n(ℂ)` (Wallach 1979, 4.13 and 4.14, for the upper triangular
Borel subalgebra, as cited in `ComplexJacquetReduction.md`). The nonvanishing part follows the
route of J. N. Bernstein and S. I. Gelfand, *Tensor products of finite and infinite dimensional
representations of semisimple Lie algebras*, Compositio Math. 41 (1980), 245–285, Theorem 5.9
and its proof in 5.10, through Harish-Chandra bimodules. All `n`, all universes `uV` and all
modules satisfying the three hypotheses are covered; no further hypothesis is added.

## Provenance

Derived. The theorem only assembles results proved in other modules: the reduction of Worker
379 (`ComplexJacquetModuleFiniteReduction`, with its bridge `ComplexJacquetBimoduleBridge`) and
the six Bernstein–Gelfand input proofs listed below. The assembly is ours.

## Proof

The Lean proof is one term:

```lean
complexJacquetModuleFiniteReduction
  ⟨VermaPBW.lowerVermaWeight, VermaPBW.lowerVermaDuflo, VermaKostant.lowerVermaKostant,
   VermaCentral.lowerVermaCentral, VermaPBW.lowerVermaHomBound, VermaPBW.lowerVermaProjective⟩
```

* `complexJacquetModuleFiniteReduction : ComplexJacquetModuleFiniteReductionStatement`
  (module `ComplexJacquetModuleFiniteReduction`) proves that
  `VermaGL.BernsteinGelfandInputsStatement` implies `ComplexJacquetModuleFiniteStatement`. It
  chains the Bernstein–Gelfand reduction `complexJacquetBimoduleReduction`, the bridge
  `complexJacquetOneSided_of_bimodule` from Harish-Chandra bimodules to one-sided nonvanishing,
  and `complexJacquetModuleFinite_of_oneSided` (module `ComplexJacquetFinite`), which also
  contains the finite-dimensionality proof.
* `VermaGL.BernsteinGelfandInputsStatement` (module `LowerVerma`) is the conjunction of six
  statements on lower Verma modules `M⁻(λ)` of `𝔤𝔩_n(ℂ)`. The anonymous constructor supplies
  their proofs, in this order:
  1. `VermaPBW.lowerVermaWeight : LowerVermaWeightStatement` (module `LowerVermaPBW`): the
     generator of `M⁻(λ)` is nonzero and spans the weight-`λ` space;
  2. `VermaPBW.lowerVermaDuflo : LowerVermaDufloStatement` (module `LowerVermaDuflo`): Duflo's
     theorem, `M⁻(λ)` is maximally faithful;
  3. `VermaKostant.lowerVermaKostant : KostantMultiplicityStatement` (module
     `LowerVermaKostant`): Kostant's multiplicity lower bound for covariants modulo `U·ker χ`;
  4. `VermaCentral.lowerVermaCentral : CentralCharacterStatement` (module `LowerVermaCentral`):
     every central character is that of some `M⁻(λ)` with `Z`-extremal `λ`;
  5. `VermaPBW.lowerVermaHomBound : LowerVermaHomBoundStatement` (module `LowerVermaHomBound`):
     the upper bound `dim W₀` for independent equivariant maps `W → End M⁻(λ)`;
  6. `VermaPBW.lowerVermaProjective : LowerVermaProjectiveStatement` (module
     `LowerVermaProjective`): singular vectors of weight `λ` lift through surjections from
     `W ⊗ M⁻(λ)`.

The universe parameters of the six input statements are fixed by
`BernsteinGelfandInputsStatement.{uV, uV}` in the reduction; Lean infers them from the expected
type. The mathematics of each input is explained in the Markdown file of its module. The
checked axioms are `propext`, `Classical.choice` and `Quot.sound`; no new axioms are used.
