# Coinvariant evaluation and complements for proper refined induction

Author: Worker 167. This is a derived construction unit for the proof of
`PadicProperRefinedInductionTheorem`. It constructs the needed maps and proves
their intrinsic properties. It does not prove the quasicuspidal decomposition
or the final assertion about all subquotients.

## Evaluation through actual coinvariants

`Langlands.Induction.coinvariantEvaluation` takes subgroups `N ≤ P` of a
topological group `G`, a complex representation `ρ` of `G`, a representation
`σ` of `P` trivial on `N`, and an actual intertwiner `f` from `ρ` into the
published smooth induced representation. It returns a complex linear map from
`Jacquet.Coinvariants ρ N` to the carrier of `σ`. The group, source carrier,
and target carrier have independent universes. Neither smoothness of `ρ` or
`σ` nor normality or closedness of `N` is required for this construction.
The ambient group is a topological group, as required by smooth induction.

The construction evaluates `f(v)` at the identity. The intertwining equation
and covariance show that this evaluation is unchanged when `v` is acted on
by an element of `N`. The existing `Jacquet.lift` therefore descends it through
the actual relation quotient. `coinvariantEvaluation_mk` gives the precise
formula on quotient representatives: evaluation of the descended map at `[v]`
is `f(v)(1)`.

`intertwiner_eq_zero_of_coinvariants` proves the intrinsic vanishing consequence.
If the source coinvariants are subsingleton, the descended linear map is zero.
For any group element `g`, equivariance identifies evaluation at one of
`f(ρ(g)v)` with `f(v)(g)`. Every function value is therefore zero, so `f = 0`.
This is the needed vanishing implication of first adjointness; it does not
construct the full Hom-space equivalence.

## Actual refinements and complements

`refinedInduced_intertwiner_eq_zero` applies this construction to any proper
standard refinement of a product Levi over a topological field. The inducing
representation and an arbitrary complex unit character factor through the
actual refined Levi projection. Its kernel is the refined unipotent radical,
so the inducing action is trivial on that radical. Quasicuspidality makes the
corresponding actual coinvariant module subsingleton. No admissibility,
irreducibility, or finite length is used.

`induced_quasicuspidal_subrepresentation_subsingleton` specializes this to the
actual p-adic `normalizedRefinedInductionFunctor`, whose character is the
positive half modulus. A quasicuspidal invariant subrepresentation of its
value has zero inclusion by the preceding lemma. Injectivity of inclusion
then makes its carrier subsingleton. The inducing carrier is in `Type uV`,
and the induced carrier and its subrepresentation are in `Type (max uF uV)`.

`complementIsoOfSubsingleton` constructs an actual isomorphism from a smooth
product-Levi representation `A` to one of two complementary invariant subspaces
`Q`, provided the other subspace `U` is subsingleton. It first proves `U = ⊥`
on underlying submodules. The full-sum component of `IsCompl` then implies
`Q = ⊤`. Its inclusion is bijective, and `IntertwiningMap.ofBijective` and
`SmoothRep.mkIso` give the required inverse isomorphism. This construction does
not assert the existence of a quasicuspidal complement.

## Provenance and scope

These constructions are derived directly from the published induction,
coinvariant, refined-projection, and smooth-subrepresentation definitions,
with their properties proved in Lean. They isolate the maps used by the
Bernstein–Zelevinsky argument, rather than transcribing a separately named
construction in the original.

For the motivating argument, see I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), section 2.4(d),
printed p.447 / PDF p.8; it uses decomposition from 2.4(a) and first
adjointness from 2.3(b). The general adjunction is 1.9(b), printed p.445 /
PDF p.6. Those original pages were read directly. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The final decomposition-dependent proof remains a separate obligation.
