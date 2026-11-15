# The Bernstein–Gelfand inputs imply one-sided nonvanishing for bimodules

Module: `Langlands.Representation.Archimedean.ComplexJacquetBimoduleReduction`.

## Statement

`Langlands.Archimedean.ComplexJacquetBimoduleReductionStatement.{uV}` is the implication

`VermaGL.BernsteinGelfandInputsStatement.{uV, uV} → ComplexJacquetBimoduleStatement.{uV}`.

Both sides are Library statements:

- `BernsteinGelfandInputsStatement` (module `LowerVerma`) is the conjunction of six facts about
  lower Verma modules `M⁻(λ)` of `𝔤𝔩_n(ℂ)`: the weight-`λ` space of the generator, Duflo's
  theorem, Kostant's multiplicity lower bound, every central character comes from a `Z`-extremal
  `λ`, the upper bound for equivariant maps into `End M⁻(λ)`, and projectivity of `M⁻(λ)`. Its
  universe parameters, for the auxiliary finite-dimensional representations and target spaces,
  are both set to `uV`.
- `ComplexJacquetBimoduleStatement` (module `ComplexJacquetBimodule`) is one-sided nonvanishing
  `ℓ(𝔫)V ≠ V` for Harish-Chandra bimodules of `𝔤𝔩_n(ℂ)`. It is given by two commuting actions
  `ℓ`, `r` on `V` and a finite-dimensional generating subspace `E` with integral weights, stable
  under `ℓ(Y) - r(Yᵀ)`, where `ℓ` has an infinitesimal character.

## Provenance

Derived. The implication is the argument of J. Bernstein and S. Gelfand, *Tensor products of
finite and infinite dimensional representations of semisimple Lie algebras*, Compositio Math. 41
(1980), proof of Theorem 5.9 in 5.10 (printed pp. 276–279). It is specialized to `𝔤𝔩_n(ℂ)`, to
lower Verma modules, and to the bimodule `X = V` with left action `r` and right action
`x · Y = ℓ(Yᵀ)x`, as in `ComplexJacquetBimodule.md`. The packaging of the inputs as six separate
statements and this implication are ours.

## Proof

`complexJacquetBimoduleReduction` destructures the conjunction and applies
`BGChase.complexJacquetBimodule_of_inputs` (module `BGChaseConclusion`). That proof follows
Bernstein–Gelfand 5.10 and is described in `BGChaseConclusion.md` and `BGChaseCore.md`; the
supporting modules are `BGChaseReps`, `BGChaseEnveloping`, `BGChaseKS` and `BGChaseSetup`. In
outline: if `ℓ(𝔫)V = V`, every `e ⊗ gen` comes from the kernel of `p : E ⊗ U → V`,
`e ⊗ u ↦ ℓ(uᵗ)e`. Projectivity of `M⁻(λ)`, together with the lifting of equivariant maps into
`End M⁻(λ)` to `U` (Kostant, HomBound, Duflo), then produces `h ∈ ker p` acting on `M⁻(λ)` like
`e ⊗ 1`. Duflo's theorem turns this into `e = 0`.

## Use

Together with the planned bridge `ComplexJacquetBimoduleStatement → ComplexJacquetOneSidedStatement`
and the Library's `complexJacquetModuleFinite_of_oneSided`, this reduces Task 7065's target
`ComplexJacquetModuleFiniteStatement` to the six Bernstein–Gelfand inputs.
