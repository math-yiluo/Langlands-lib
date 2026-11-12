# The first-order thickening of a presentation

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Presentation`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Presentation`. Author: Worker 5103
(task `14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction; no literature
statement is formalized.

Data: a commutative ring `R`, an `R`-algebra `A₀` and an `R`-algebra map
`s : MvPolynomial (Fin n) R →ₐ[R] A₀` (a presentation when surjective).

## The thickening

- `J s := ker s` and `Pres s := MvPolynomial (Fin n) R ⧸ J s ^ 2` (abbreviations).
- `presMap s : Pres s →ₐ[R] A₀`, induced by `s` (`J² ≤ J`, `sq_le_ker`); `presMap_mk`.
- Instances: `Algebra (Pres s) A₀` given by `presMap s` (`algebraMap_pres`) and
  `IsScalarTower R (Pres s) A₀`.
- `presMap_surjective`: surjective when `s` is.
- `mem_ker_iff`: the class of `a` lies in `ker (algebraMap (Pres s) A₀)` iff `a ∈ J s`.
- `ker_mul_eq_zero`: products of two elements of this kernel vanish;
  `ker_isNilpotent`: the kernel is nilpotent (its square is zero).

## Lifting property

`exists_lift`: for a surjection `q : A →ₐ[R] B` with `a * b = 0` for all `a, b ∈ ker q`,
and any `χ : A₀ →ₐ[R] B`, there is `ρ : Pres s →ₐ[R] A` with
`q ∘ ρ = χ ∘ (Pres s → A₀)`. Proof: lift the images of the variables, `ρ₁ := aeval`; then
`q ∘ ρ₁ = χ ∘ s`, so `ρ₁(J) ⊆ ker q` and `ρ₁(J²) = 0`; descend to the quotient.

## The derivation and its universality

- `d₁ s : MvPolynomial (Fin n) R →ₗ[R] (Fin n → A₀)`, `d₁ s a k = s (∂ₖ a)`
  (`d₁_apply`); Leibniz rule `d₁_mul`; `d₁_eq_zero`: `d₁` vanishes on `J²`.
- `presDer s : Derivation R (Pres s) (Fin n → A₀)`, the derivation induced by `d₁`
  (`presDer_mk`), where `Fin n → A₀` is a `Pres s`-module through `A₀`.
- `exists_presDer_factor`: for every `A₀`-module `M` that is also a `Pres s`-module and an
  `R`-module with scalar towers `Pres s → A₀ → M` and `R → Pres s → M`, and every
  `R`-derivation `δ : Pres s → M`, there is an `A₀`-linear `D' : (Fin n → A₀) → M` with
  `δ x = D' (presDer s x)` for all `x`; namely `D' v = ∑ₖ vₖ • δ (xₖ)`. Proof by induction
  on polynomials (constants, sums, products with a variable).

## The kernel as an `A₀`-module

For `s` surjective (`hs`):

- `qModule hs`: the `A₀`-module structure on `ker (algebraMap (Pres s) A₀)` (`= J/J²`),
  namely `kerModule` of `BaseLifting` (the kernel has square zero);
- `qModule_isScalarTower hs`: the tower `Pres s → A₀ → ker` for this structure and the
  ideal's `Pres s`-module structure;
- `qModule_finite hs` (`R` noetherian): the kernel is a finite `A₀`-module.
