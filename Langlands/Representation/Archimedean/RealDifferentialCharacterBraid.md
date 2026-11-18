# The actual differential braid for three real characters

This internal construction proves equality of two actual three-crossing
Frobenius maps, including their scalar normalization and parity changes.
It applies when at least one of the two adjacent positive integral gaps
is one or two.

Let `a,b,c` be real character data. The proposition `Parameters a b c n m`
records precisely these assumptions:

- `n,m` are positive natural numbers;
- `b.exponent-a.exponent=n` and `c.exponent-b.exponent=m`;
- `Even(n-1-pairParity a b)` and `Even(m-1-pairParity b c)`.

Write `bar a=flip a` for the character with the same exponent and opposite
parity. A differential crossing of gap `ℓ` uses tail symmetry `(-1)^ℓ`.
On the reducible parity class this equals the negative of the usual
sign-preserving swap symmetry. Consequently its target reverses the
characters and flips both parities.
`data` constructs the actual Frobenius data in arbitrary surrounding
lists. `crossing_exact` proves exact intertwining at the specified
positive gap, and `crossing_fourier` identifies its multiplier with the
polynomial `Pℓ(j)`.

In rank three the first word follows

`[a,b,c] → [bar b,bar a,c] → [bar b,bar c,a] → [c,b,a]`,

with rotation positions `0,1,0` and cutoffs `n,n+m,m`. The second follows

`[a,b,c] → [a,bar c,bar b] → [c,bar a,bar b] → [c,b,a]`,

with positions `1,0,1` and cutoffs `m,n+m,n`. Intermediate double flips
are retained literally in the Lean definitions, then transported to the
displayed final list using the proved `flip_flip`. Each character is
flipped twice overall, so the final character data, including their
characters, agree exactly with the ordinary reversed list.

`leftWord` and `rightWord` are these concrete composite maps from
`KF 3 [a,b,c]` to `KF 3 [c,b,a]`. The main theorem `braid` proves their
equality when `n∈{1,2}` or `m∈{1,2}`. `leftWord_exact` and
`rightWord_exact` prove exact intertwining by composing the three
published recurrence-based intertwining criteria and the final equality
transport.

For the map equality, the exact normalization
`Pℓ(-iX)=(-i)^ℓ Dℓ(X)/(2^ℓ ℓ!)` converts the proved compact polynomial
braids for parameter one or two into normalized polynomial identities.
The scalar products of the two words agree. Interchanging the compact
generators supplies the case where the other gap is small.

The seven functions comprising the input and both three-step words lie
in one finite polynomial degree space after restriction to `O(3)`.
The exact Fourier/operator relation identifies each step with the
corresponding polynomial in the compact generator. The normalized braid
therefore makes their final vectors equal. Restriction to `O(3)` determines
a principal-series function, so their actual final standard-module
vectors are equal.

The auxiliary `ambient_functional_braid` also transfers the multiplier-word
comparison to every ambient three-coordinate compact coset. It takes the
displayed six coefficient relations as explicit hypotheses and concludes
equality on the ambient compact subgroup. This includes ambient rank four.

`RealDifferentialCharacterBraidStatement` packages the actual rank-three
word equality and both exact intertwining properties for all stated
inputs. `realDifferentialCharacterBraid` proves it.

This proves only the small-gap differential braid. It neither proves
the general two-parameter braid nor identifies these words with the
chosen interlaced equivalences or canonical sign-preserving tail words.
Neither remaining GL4 kernel-image containment nor the unrestricted
two-induction-block filtration is asserted.
