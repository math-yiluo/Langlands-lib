# Away finite-adelic Tate comparison for the multiplicative group

This internal construction bundles the published `awayRationalEquiv` from
`MultiplicativeRational` as a linear equivalence over the away finite adeles.
Its scalar structures are those already constructed in `AwayRationalScalars`
and `TwistAwayRationalScalars`. The proof specializes the existing compatibility
with rationalized residue scalars to the inverse scalar-comparison image.
No new original-literature assertion is used.

## Inputs and explicit comparison assumptions

Let `S` be any scheme, `T` a test scheme over `S`, and `m` any natural number.
The construction takes the two coupled published comparison propositions:

* `h : Global.RationalProfiniteIntegerAdeleComparison`;
* `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.

The full hypothesis remains an implicit parameter through the type of
`hAway`; neither proposition is proved in this module. The same `hAway`
supplies the chosen inverse scalar comparison in both module actions.
There is no primality or nonzero condition on `m`.

The source is the rationalization over the integers of the actual Gm
torsion-section limit over `T`, retaining the positive orders coprime to
`m`. The target is the rationalization over the integers of the actual
roots-of-unity limit of `Γ(T.left, ⊤)` at the same orders.
Both rationalizations are written `ℚ ⊗[ℤ] Integral`.

## Linear equivalence and formulas

`awayRationalEquiv_primeToFiniteAdeleAction` states that the published
Gm-to-roots rational equivalence intertwines the two actions of
`Global.PrimeToFiniteAdeles m`. It is the already proved
`awayRationalEquiv_scalarAction` evaluated at the inverse image of the
adelic scalar under the chosen comparison.

`primeToFiniteAdeleEquiv` equips the same additive equivalence with this
scalar compatibility. Its type and body install the source and target
`primeToFiniteAdeleModule` structures locally. The application theorem
identifies its underlying function with `awayRationalEquiv`.

The two pure-tensor formulas say that the equivalence sends `q ⊗ x` to
`q ⊗ awayEquiv x`, and its inverse sends `q ⊗ y` to
`q ⊗ awayEquiv.symm y`. These are definitional identities.
`primeToFiniteAdeleEquiv_symm_action` explicitly states inverse scalar
compatibility. Its proof applies the forward equivalence, uses forward
compatibility, and cancels the equivalence with its inverse.

## Full-to-away restriction

`primeToFiniteAdeleEquiv_restrictAway` compares rational restriction on
Gm Tate modules followed by the away finite-adelic equivalence with the
full finite-adelic equivalence followed by rational root restriction.
The full equivalence uses precisely the `h` occurring in `hAway`.
`primeToFiniteAdeleEquiv_symm_restrictAway` gives the reverse square.
Both proofs reuse the published rational restriction squares, since
bundling scalar linearity leaves the underlying functions unchanged.

This is an algebraic comparison under explicit scalar-comparison
hypotheses. It makes no claim about rational topology or continuity,
affine specialization, test-scheme base change, geometric monodromy,
torsion rank or finite étaleness, a trivialization of the twist, a Weil
pairing, or completion of the parent PEL task.
