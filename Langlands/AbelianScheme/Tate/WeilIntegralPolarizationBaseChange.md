# Base change of exact integral polarization cross-multiples

This internal construction combines actual integral dual pullback from
`WeilIntegralPolarizationComparison` with the published naturality theorem
for the canonical comparison between the base change of a chosen dual and
the chosen dual of the base-changed abelian scheme. All displayed tensor,
Picard-zero, dual geometry, evaluation and canonical comparison prerequisites
remain inputs. No rational dual-additivity assumption is needed.

`integralDualPullbackHom_baseChange` proves an equality of actual integral
homomorphisms. For an actual map `f : A ⟶ B` and an integral map `lamB` to
the constructed dual of `B`, canonically changing the integral composite
`f ≫ lamB ≫ dualAB f` gives the integral dual pullback of the canonically
changed `lamB` by the actual changed `f`. The proof uses preservation of
composition by actual abelian-scheme base change and the published
naturality of the integral canonical dual comparison, followed by
associativity.

`integralDualMultipleDataBaseChange` transports supplied exact integral
cross-multiple data for that integral pullback and a supplied `lamA`.
It preserves the actual integers `left` and `right`, their nonzero-left
proof and the prescribed rational ratio `q`. For the equation proof,
apply actual base change to the original integral equality and postcompose
with the canonical dual comparison at `A`. Additivity preserves both integer
multiples; the commuting equality just proved identifies the new left side.
Thus no further torsion-clearing multiplier, denominator or changed ratio is
introduced by this transport.

This construction transports supplied witnesses and compares actual chosen
duals through the canonical maps. It makes no claim about equality of
independently chosen witnesses, reflection by base change, integral model
existence, geometric isogenies or moduli representability. In particular,
a ratio that contains the square of a supplied representative's denominator
is preserved exactly as a prescribed rational number.
