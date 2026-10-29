# Critical norm approximation after bounded unramified base change

`Langlands.LocalClassField.PrimeCriticalNormAfterUnramifiedBaseChange.{u}`
is a `Prop`-valued statement. This module does not prove it.

For every prime `p`, every `F : PadicField.{u} p`, and every actual finite
intermediate field `E` of the specified algebraic closure, assume `E/F`
is Galois of prime degree `ell` and has canonical absolute ramification
index `ell * e(F)`. The statement chooses an actual lower ramification
break `t`: the lower groups are the whole group through `t` and the
trivial group above it. It also retains `0 < t ↔ ell = p`.

For each actual element `z` of the canonical unit filtration `U_F^t`,
the conclusion supplies an actual finite intermediate field `K`,
Galois over `F`, with `e(K) = e(F)` and `[K:F] ≤ ell`. This choice may
depend on `z`. It supplies an actual compositum `M` with
`M.field = E.field ⊔ K.field` and both inclusion proofs `hE` and `hK`.
With the algebras induced by those inclusions and their compatible
scalar towers, it retains the following arithmetic facts:

- `[M:K] = ell`, and `e(M) = ell * e(K)`;
- `M/K` is Galois and has the same actual break `t`;
- there is `y ∈ U_M^t` for which the quotient of the image of `z` by
  `N_{M/K}(y)` belongs to `U_K^(t+1)`.

The norm in this last clause is exactly
`FiniteIntermediateExtension.unitsNorm K M hK`, the determinant norm on
field units for the supplied inclusion. The image of `z` uses the actual
field algebra map `F → K`. All fields lie in the specified algebraic
closure, and the universe `u` is arbitrary. At `t = 0`, the assertion
uses residue units and their multiplicative power map; it does not
replace that map by an additive coordinate. Degree one for `K` and
`z = 1` are allowed.

## Provenance and intended role

This is an intermediate assertion extracted from the proof of
Proposition 6 in Jean-Pierre Serre, *Local Fields*, Greenberg translation,
GTM 67, Springer (1979), registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter V, section 4, printed pages 87–88 (PDF pages 94–95) identifies
the ramification groups and graded norm coefficients after extending
the residue field. In the proof on printed page 88, a residue extension
of degree at most `ell` makes the critical unit class a graded norm.
The quotient formulation above expresses precisely that intermediate
step. Realizing the extensions in the specified closure, using
canonical absolute indices, retaining the actual scalar towers, and
recording the break criterion are derived encoding choices.

The registered author corrections `serre-book-corrections-2019`,
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P.
Serre's books (2019).pdf`, were checked on PDF pages 2–3. They list no
correction affecting this passage.

An intended arithmetic proof combines the published actual single-break
theorem, graded norm formulas, bounded root lifting, and unramified
compositum and break preservation results. At a positive break the
critical equation has the literal norm and trace coefficients; at
break zero it is an `ell`-th power equation with a nonzero root.
Literal coefficient transport is a distinct prerequisite.

This statement provides an approximation modulo `U_K^(t+1)`. It does
not assert exact higher-unit norm surjectivity or the full
`PrimeNormAfterUnramifiedBaseChange` theorem. Those require the separate
norm-reduction result and an exact correction of the remaining quotient.

Authored by Worker 27.
