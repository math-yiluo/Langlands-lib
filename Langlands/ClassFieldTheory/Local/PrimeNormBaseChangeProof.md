# Prime-degree norms after bounded unramified base change

Authored by Worker 27.

This module proves
`Langlands.LocalClassField.primeNormAfterUnramifiedBaseChange` with exactly
the published proposition
`Langlands.LocalClassField.PrimeNormAfterUnramifiedBaseChange.{u}` as its
type. It adds no outer hypotheses and preserves arbitrary universe `u`,
every prime residue characteristic, every finite base field, and every
field unit, including units of nonzero normalized order.

The proof imports the published critical approximation theorem from
`PrimeCriticalNormBaseChangeProof`, the exact higher-unit norm and
critical-representative theorem from `PrimeRamifiedNormReductionProof`,
and determinant norm compatibility from `TotalUnramifiedCompositumProof`.
The new content assembles those arithmetic results into the exact
arbitrary-unit norm equation.

## The exact norm witness

The proof installs the actual p-adic scalar structure on `E` and its tower
over the base. The critical approximation theorem
`primeCriticalNormAfterUnramifiedBaseChange` chooses the actual lower break
`t` before any critical unit. Applying `primeRamifiedNormReduction` to
`E/F` at that break, its third clause gives, for the supplied arbitrary
field unit `x`, concrete units `yE` and `z` with

`x = N_{E/F}(yE) * z`, with `z` in `U_F^t`.

Applying critical approximation to that `z` supplies the unramified
finite Galois field `K/F`, its degree bound `finrank F K ≤ ell`, the actual
compositum `M.field = E.field ⊔ K.field`, both inclusions, and a unit `yC`
in `U_M^t`. Its norm error

`image(z) / N_{M/K}(yC)`

lies in `U_K^(t+1)`. The same supplied compositum has degree `ell` over
`K`, is totally ramified and Galois, and retains the actual break `t`.
The proof installs precisely the inclusion algebras associated with these
witnesses and their scalar towers; finite dimension over `K` follows from
the common finite base extension. No scalar map or norm certificate is
assumed.

The second clause of `primeRamifiedNormReduction`, now applied to `M/K`
at `n = t`, states

`N_{M/K}(U_M^(t+1)) = U_K^(t+1)`.

Here the inverse-Herbrand index satisfies `psi(t) = t`, including `t = 0`.
Membership in this subgroup image gives an actual unit `yH` whose norm
is the displayed error. The final unit is

`image(yE) * (yC * yH)`.

The private algebraic helper proves that its norm is exactly `image(x)`.
The theorem retains the same `K`, degree bound, `M` and inclusion.

## Algebraic compatibility

`compositum_unitsNorm_inclusion` proves determinant norm compatibility
on units for any supplied actual compositum of a totally ramified finite
Galois `E/F` and an unramified finite `K/F`. It obtains the published
`totalUnramifiedCompositum` witness and identifies its finite intermediate
field with the supplied `M` by their equalities to `E.field ⊔ K.field`.
After substitution, proof irrelevance identifies the inclusion proofs.
Extensionality of units reduces the result to the published literal field
norm identity.

`compositum_unitsNorm_corrected_witness` applies that compatibility,
multiplicativity and cancellation in the commutative unit group to the
three supplied units. It assumes only their concrete equalities, while
the main theorem obtains their existence from the two arithmetic proofs.

These two helpers and the final assembly are internal consequences of
their imported theorems and introduce no additional original-source
assertion. The source route is Serre, *Local Fields*, Greenberg translation
(1979), Chapter V, section 4, Proposition 6 and its proof, printed
pp. 87–88 / PDF pp. 94–95, registered as `serre-1979-local-fields`.
The original and the applicable 2019 author corrections were read during
the earlier construction; no listed correction affects this passage.
The focused statements and proof pairs record the arithmetic source
correspondence and the separate graded, lifting and compositum inputs.
No reciprocity theorem, cohomology vanishing or parent norm result is used.
