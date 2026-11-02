# Artin–Rees support dévissage for coactions

Worker 148. This internal construction isolates the algebraic step used in
support dévissage. The rings lie in an arbitrary universe `u`, and the
coefficient modules lie in an independent universe `v`.

For a linear map `f : M →ₗ[B] N` and an ideal `I`, the defined linear map
`CoactionArtinRees.idealPowerRestriction I f n` restricts `f` to the submodule
`I^n M`. Its application lemma is definitional.

The preliminary quotient lemma identifies the containment
`I ≤ Ann(M/P)` with `I M ≤ P`, by lifting elements through the quotient map.
If `B` is Noetherian, `M` is finite over `B`, and
`I ≤ radical(Ann(ker f))`, finite generation of `I` gives an exponent `r`
with `I^r ker f = 0`. Mathlib's Artin–Rees theorem
`Ideal.exists_pow_inf_eq_pow_smul` gives a `k` for which
`I^(r+k) M ∩ ker f = I^r (I^k M ∩ ker f) = 0`.
The restriction at exponent `r+k` is therefore injective.

If `I^r` annihilates the original cokernel, then `I^(n+r)` annihilates the
cokernel of the restriction to `I^n M`. The proof uses
`range(f|I^n M) = I^n range(f)` and multiplies the original containment
`I^r N ≤ range(f)` by `I^n`. Combining these observations gives an
injective ideal-power restriction whose cokernel is annihilated by an ideal
power, provided `I` lies in the radicals of both original annihilators.
This part requires no coactions.

The final theorem, `GroupoidCoaction.oneCohomologyVanishes_of_artinRees`,
uses an actual ring étale equivalence relation and equivariant `f` between
finite modules. It assumes that `I` is invariant, lies in those two
radical annihilators, and satisfies the published
`FiniteAnnihilatorVanishing` predicate. It also assumes vanishing for
every restricted coaction on `I^n M`. Étaleness makes the relation algebra
flat. Invariance makes every `I^n M` stable, so the injective restriction
is equivariant. The published invariant-ideal power dévissage theorem
gives vanishing for its cokernel. The published short exact sequence
closure theorem then gives `OneCohomologyVanishes` for `N`.

The provenance is internal: these are deductions from Mathlib's ideal,
annihilator, and Artin–Rees results and the imported coaction restriction,
cokernel, power dévissage, and extension closure results. No external
statement is asserted. The theorem retains its explicit vanishing
premises; it does not establish those premises for the geometric cover or
prove the full finitely covered acyclicity statement.
