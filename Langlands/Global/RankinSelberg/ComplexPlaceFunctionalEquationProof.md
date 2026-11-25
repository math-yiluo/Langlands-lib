# Proof: the archimedean Rankin–Selberg functional equation at the complex places

Module `Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.complexPlaceFunctionalEquation :
    ComplexPlaceFunctionalEquationStatement.{u}
```

proves `Langlands.Global.RankinSelbergGlobal.ComplexPlaceFunctionalEquationStatement` (module
`ArchimedeanFunctionalEquationStatement`) at an arbitrary universe `u`. The statement is the
conjunction

```lean
ComplexUnequalFunctionalEquationStatement.{u} ∧ ComplexEqualFunctionalEquationStatement.{u}
```

of the two statements of the same module, whose complete text is given there.

- `ComplexUnequalFunctionalEquationStatement.{u}`: let `T`, `T'` be actual cuspidal realizations
  of `GL_(r+1)` and `GL_(t+1)`, `t < r`, with contragredient realizations `Td`, `Td'`, over a
  number field `F : Type u` with an additive character `ψ` of the adeles trivial on `F`. Let `w`
  be a complex place, `ψ_w = complexScaledCharacter a` the component of `ψ` at `w`, and `d`,
  `d'`, `dd`, `dd'` the parameters of `T`, `T'`, `Td`, `Td'` at `w`. For every quotient measure
  `D` on `N_(t+1)(ℂ) \ GL_(t+1)(ℂ)` and archimedean restrictions `W` of a Whittaker function of
  `T` for `ψ` and `W'` of one of `T'` for `ψ⁻¹` at `w`, there are a real `σ` and meromorphic
  functions `M`, `Md` on `ℂ` such that, for `σ < Re s`, the integrands of `Ψ(s; W, W')` and of
  `Ψ_(r-t-1)(s; ρ(w_(n,m)) W̃, W̃')` are absolutely integrable, both integrals are holomorphic
  and equal `M(s)` and `Md(s)`; and off a discrete set
  `L_w(s) Md(1 - s) = ω'_w(-1)^r ε_w(s) L∨_w(1 - s) M(s)`.
- `ComplexEqualFunctionalEquationStatement.{u}`: the same with `T`, `T'` both of rank `r + 1`,
  the integrals `Ψ(s; W, W', Φ)` and `Ψ(s; W̃, W̃', Φ̂)` for every Schwartz function `Φ` on
  `ℂ^(r+1)` (Fourier transform for `ψ_w` and its self-dual measure), and the same functional
  equation.

## Proof as implemented

The proof is a single term that combines three Library theorems.

1. `complexPlaceFunctionalEquationLocalFEReduction` (module
   `ComplexPlaceFunctionalEquationLocalFEReduction`) proves
   `ComplexPlaceFunctionalEquationLocalFEReductionStatement.{u}`, the implication
   `ComplexLocalUnequalFunctionalEquationStatement →
   ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceFunctionalEquationStatement.{u}`.
   Its other premises (the minus-one premise and the contragredient premise) are discharged
   inside it by Library theorems; it passes from the global realizations to the standard modules
   of their parameters at `w`.
2. `complexLocalUnequalFunctionalEquation` (module `ComplexPlaceUnequalFunctionalEquationProof`)
   proves `ComplexLocalUnequalFunctionalEquationStatement`: the local functional equation for
   `GL_(r+1)(ℂ) × GL_(t+1)(ℂ)`, `t < r`, and the induced representations of lists of complex
   characters.
3. `complexLocalEqualFunctionalEquation` (module `ComplexPlaceEqualFunctionalEquationProof`)
   proves `ComplexLocalEqualFunctionalEquationStatement`: the same for
   `GL_(r+1)(ℂ) × GL_(r+1)(ℂ)` with a Schwartz function.

Applying the reduction to the two local theorems gives the statement.

## Declarations

- `complexPlaceFunctionalEquation : ComplexPlaceFunctionalEquationStatement.{u}` (theorem).

## Provenance

H. Jacquet, *Archimedean Rankin–Selberg integrals*, in D. Ginzburg, E. Lapid and D. Soudry
(eds.), *Automorphic Forms and L-functions II. Local Aspects*, Contemp. Math. 489 (2009), 57–172.
The pages below are those of the proceedings volume (file `Part II - Local Aspects.pdf`, PDF page =
printed page + 22); the page of `ArchimedeanFunctionalEquationStatement` cites the same theorem in
the registered copy `jacquet-2009-archimedean-rankin-selberg`, whose pagination differs.
Theorem 2.1, printed p. 62 (PDF page 84): (i) the integrals
converge for `Re s ≫ 0`; (ii) each extends to a meromorphic function of `s` which is a
holomorphic multiple of `L(s, σ_u ⊗ σ'_u')`, bounded at infinity in vertical strips; (iii) the
functional equations for `n = n' + 1`, `n > n' + 1` and `n = n'`, with the signs
`ω_π(−1)^(n−1) ω_π'(−1)`, `ω_π(−1)^(n') ω_π'(−1)` and `ω_π(−1)^(n−1)`. The Library statement
keeps (i), the meromorphic continuation and (iii) in multiplied-out form at the complex places;
the conversion of the signs to `ω'_w(−1)^r` is explained on the page of
`ArchimedeanFunctionalEquationStatement`.

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), §3.2: Theorems 3.5 and 3.6,
printed p. 217 (PDF page 220), the meromorphic continuation of the archimedean integrals and the
local functional equations
`Ψ_(n−m−j−1)(1 − s; ρ(w_(n,m)) W̃, W̃') = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ_j(s; W, W')` and
`Ψ(1 − s; W̃, W̃', Φ̂) = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ(s; W, W', Φ)`.
