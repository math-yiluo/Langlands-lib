# Finitely many twisted classes from a finite-valued separating map

Module `Langlands.TraceFormula.TwistedClassRepresentatives`, namespace `Langlands.TraceFormula`.
It imports `Langlands.TraceFormula.TwistedOrbital`, which defines
`IsTwistedConjugate Γ θ δ δ'`: `h⁻¹ * δ * θ h = δ'` for some `h ∈ Γ`.

## Statement

`exists_twistedClass_representatives Γ θ S c Rs hRs hcR hc` works in a group `H` with a
subgroup `Γ`, and with any `θ` in a type `E` of monoid homomorphisms `H → H`
(`[FunLike E H H] [MonoidHomClass E H H]`). Its other data are a set `S : Set Γ`, a map
`c : Γ → R` into an arbitrary type and a finite set `Rs : Set R` (`hRs : Rs.Finite`). The
hypotheses are:

- `hcR`: `c q ∈ Rs` for every `q ∈ S`;
- `hc`: for `q, q' ∈ S`, `c q = c q'` implies `IsTwistedConjugate Γ θ q q'` (with `q, q'`
  read in `H`).

The conclusion gives `m : ℕ` and `r : Fin m → Γ` such that

1. every `r j` lies in `S`;
2. `IsTwistedConjugate Γ θ (r j) (r k)` implies `j = k`;
3. every `q ∈ S` satisfies `IsTwistedConjugate Γ θ (r j) q` for some `j`.

So `S` meets only finitely many `θ`-twisted `Γ`-classes, and one point of `S` is chosen in
each of them.

## Proof

Three private lemmas show that `IsTwistedConjugate Γ θ` is reflexive (witness `1`),
symmetric (witness `h⁻¹`, using `map_inv`) and transitive (witness `g * k`, using
`map_mul`), for any `θ` in a `MonoidHomClass`. The Library's
`IsTwistedConjugate.symm`, `IsTwistedConjugate.trans` and `IsTwistedConjugate.refl` (modules
`Langlands.TraceFormula.SingleOrbitGeometricTrace` and
`Langlands.TraceFormula.SimpleTraceGeometricExpansionSum`) are stated for `θ : G →* G` only.

These lemmas make twisted conjugacy a setoid on the subtype `S`; let `Q` be its quotient. The
map `Q → Rs` sending a class to `c` of its chosen representative (`Quotient.out`) is
injective by `hc`, so `Q` is finite. Enumerating `Q` by `Finite.equivFin` gives `m = Nat.card Q`
and `r j = Quotient.out` of the `j`-th class. Clause 1 holds by construction. Clause 2 holds
because twisted-conjugate representatives have the same class, and clause 3 because every
`q ∈ S` is twisted-conjugate to the representative of its own class (`Quotient.mk_out`).

## Use

The proof of `exists_twistedClass_representatives_of_isCompact` (module
`Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`) applies the theorem
with `c` sending a rational point to the representative in a finite set of rational
`σ`-conjugacy classes of `GL_n(L)` that its coordinates are `σ`-conjugate to. The theorem is
elementary and is not taken from a source.
