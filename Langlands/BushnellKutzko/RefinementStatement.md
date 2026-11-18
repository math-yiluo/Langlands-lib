# The refinement theorem (T6)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.2.8),
printed p. 56 (PDF p. 68); the refinement and derived-stratum definitions
are on printed p. 51.

`RefinementStatement` is an unproved proposition definition for every
nonarchimedean local field `F`, finite-dimensional `V` and field action
`E/F` on `V`, in independent universes.

Its objects are the original stratum `S`, perturbation `b`, tame
corestriction `s`, actual derived stratum `D` over `E`, and a simple
stratum `C` over `E`. The premises express exactly the source hypotheses:

- `D` is `[𝔅,r,r−1,s(b)]` for `S`, using `IsDerivedStratum`, which
  includes simplicity of `S`, `E = F[S.b]`, and the correct
  centralizer-chain lattice sets;
- `v_𝔄(b) = −r`;
- `C` has the same chain, `n` and `r` as `D`, is equivalent to `D`,
  and is simple.

Specifying a centralizer chain and the two actual strata is a
representation of the source's objects, rather than an additional
mathematical property. The ring of integers for both `D` and `C`
is the published `subfieldIntegers F E`; their endomorphisms are
`E`-linear endomorphisms of `V`. No valuation on `E` or external
exactness result is a premise.

The conclusion supplies a simple stratum `T = [𝔄,n,r−1,β₁]`,
with the same original chain, whose coset is
`S.b + b + 𝔓^{1−r}`. This is the stated equivalence to the
refinement. It also states

`e(F[β₁]|F) = e(F[β,c]|F)`,
`f(F[β₁]|F) = f(F[β,c]|F)`, and
`k₀(β₁,𝔄) = max(k₀(β,𝔄),k₀(c,𝔅))`.

Here `β = S.b` and `c = C.b`. The algebra `F[β,c]` is constructed
as `Algebra.adjoin F {S.b, C.b.restrictScalars F}` in the actual
ambient endomorphism algebra. It equals `E[c]` since `E = F[β]`;
the simplicity of `C` makes it a field. The two auxiliary
subalgebra-invariant definitions apply the existing constructed
ramification and residue-degree invariants after `IsField.toField`,
with arbitrary default zero in nonfield cases. No field or
invariant is independently supplied.

The second critical exponent uses the actual chain over `𝔬_E`.
Both exponents are in `WithBot ℤ`, so the maximum also handles
the source's scalar `−∞` convention.
