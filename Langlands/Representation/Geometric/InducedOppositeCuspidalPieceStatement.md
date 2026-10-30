# Cuspidal geometric pieces of opposite Jacquet modules of induction

Authors: Worker 954 (draft), Worker 264.

`Langlands.GLInducedOppositeJacquetCuspidalPieceStatement` is a proposition
definition. The module states it and proves nothing about representations.

## Exact statement

Fix a prime `p`, an actual finite extension `F : PadicField p`, compatible
`TopologicalData T` (its topology is used throughout), a positive integer `n`,
and two ordered block shapes `B C : BlockShape n`. Let

- `π : Rep ℂ (B.Levi F.Carrier)` be smooth (`IsSmooth π.ρ`), with no
  irreducibility, admissibility, finite-length, central-character or
  temperedness condition;
- `ρ : Rep ℂ (C.Levi F.Carrier)` be irreducible
  (`Representation.IsIrreducible ρ.ρ`) and satisfy the existing
  `CuspidalSupport.IsLeviCuspidal C ρ.ρ` (admissible and quasicuspidal).

Assume that `ρ` is an actual subquotient of

```lean
CuspidalJacquetMultiplicity.oppositeJacquet T C
  (CuspidalJacquetMultiplicity.induced T B π),
```

in the form: some subrepresentation `U` of that opposite Jacquet module has a
surjective intertwining map onto `ρ.ρ`.

The conclusion gives a standard refinement `S : BlockRefinement B`, a
permutation `w : Equiv.Perm (Fin n)`, a proof
`hw : CuspidalSupport.ConjugatesLevi (B.flatten S) C w` that the permutation
matrix of `w` conjugates the embedded Levi of the flattened shape
`B.flatten S` onto the embedded Levi of `C`, and a subrepresentation `U` of

```lean
(T.normalizedRefinedJacquet B S π.ρ).comp
  (flattenedLeviEquiv F.Carrier B S).toMonoidHom,
```

such that `CuspidalSupport.transport (B.flatten S) C w hw U.toRepresentation`
has a surjective intertwining map onto `ρ.ρ`. So `ρ` is an actual quotient of
the `w`-transport of an actual subrepresentation of one upper refined Jacquet
module of `π`, read on the flattened product Levi.

## Constructions

All constructions are imported unchanged.

- `induced` is the actual normalized upper parabolic induction
  `T.normalizedParabolicInduced B`, and `oppositeJacquet` is the actual quotient
  by `C.oppositeUnipotentSubgroup F.Carrier`, transported to `C.Levi F.Carrier`.
  Both come from `CuspidalJacquetMultiplicityStatement`. `oppositeJacquet`
  passes the inverse `δ_C⁻¹` of the upper full modulus `δ_C` of `C` as the
  parameter of `Jacquet.normalizedActionOfModulus`. That construction acts by
  the inverse square root of its parameter
  (`Jacquet.normalizedActionOfModulus_mk`), so the scalar is `δ_C^(+1/2)`, not
  a full twist by `δ_C⁻¹`.
- `T.normalizedRefinedJacquet B S` is the upper refined Jacquet module of
  `RefinementFunctors`, along the standard parabolic of `B.Levi` given by `S`.
  It passes the full refined modulus `δ_ref = T.refinedLeviModulus B S` to the
  same construction, so it acts by `δ_ref^(-1/2)`
  (`PadicField.TopologicalData.normalizedRefinedJacquet_mk` in
  `RefinementFunctors`). `flattenedLeviEquiv`
  identifies `(B.flatten S).Levi` with the refined Levi.
- `ConjugatesLevi` and `transport` come from `CuspidalSupport.LeviDefinitions`.
  `transport` acts through the inverse conjugation: on embedded matrices,
  `(transport σ)(m) = σ(P_w⁻¹ m P_w)` with `P_w = permutation n F w`
  (`leviConjugation_symm_embedding`). This is the convention of BZ77
  section 1.7 (printed page 443), `(αρ)(n) = ρ(α⁻¹ n)`.

The universes are independent: `uF` for the field, `uW` for the carrier of `π`,
`uV` for the carrier of `ρ`. Induction and its opposite Jacquet module have
carrier universe `max uF uW`.

## Scope

The conclusion has no minimality, stabilizer, Weyl-group, block-class,
temperedness or numerical clause, and it does not say which refinement occurs.
It does not claim `ρ` occurs in every piece, does not count multiplicities, and
does not exclude any piece. In particular the statement supplies:

- no exponent, temperedness or other numerical information;
- no exclusion of the identity piece;
- no constituent repair;
- no adjointness step;
- no occurrence of `ρ` in a prescribed quotient.

Neither the geometric lemma nor any filtration is a hypothesis.

## Provenance

This is a derived statement, not a numbered result of the source. The source is
I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Annales scientifiques de l'École Normale Supérieure (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`
(SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).

It combines the following facts.

1. Section 2.12, printed page 448 (the geometric lemma, in the Library as
   `Geometric.GeometricLemmaTheorem`): the upper Jacquet module of an upper
   induction is glued from pieces, one per minimal double coset
   representative. Each piece is normalized inner induction of a transported
   upper refined Jacquet module of the inducing representation.
2. Section 2.4(d) together with 2.4(a) (section 2.4 begins on printed page 446;
   the theorem with items (a)–(d) is on printed page 447; in the Library as
   `CuspidalSupport.ProperRefinedInductionTheorem`): normalized induction from
   a proper standard refinement has no nonzero quasicuspidal subquotient.
3. Section 1.7, printed page 443: the transport of a representation along an
   isomorphism, used here for the Levi transport `transport`.
4. An elementary GL fact, not taken from the paper: conjugation by the
   block-reversal permutation of `C` takes the opposite parabolic of `C` to the
   upper parabolic of `C.reverse`. This is how the opposite Jacquet module
   reduces to an upper one.

Intended proof route, a future obligation and not an established result. Use 4
to replace the opposite Jacquet module along `C` by the upper Jacquet module
along `C.reverse`, pulled back along the reversed-label Levi equivalence. Apply
1 to `(B, C.reverse)`. An irreducible subquotient of a finitely filtered
representation is a subquotient of one graded piece. By 2, that piece has the
trivial target refinement. Induction from the whole Levi is the identity, and
the intersection transport is the Levi transport of 3. Composing with the
reversal gives the stated `w`, which is block reversal composed with a minimal
representative for `(B, C.reverse)`. That is why the statement asserts no
minimality of `w`.

## Intended use

This is meant as a numerics-free input of quotient reflection
(Silberger 1978, Proposition 5.8, for tempered `π`; reflection task
`9f88af41-d438-475e-ae54-6ef33bcfb8ed`). It replaces no existing target. There,
a surjection `Ind_C(ρ) → J` onto a common irreducible quotient `J` gives, by
second adjointness, a nonzero and hence injective map `ρ → r̄_C(J)`; it does
not make `ρ` a quotient of all of `r̄_C(J)`. Exactness of the opposite Jacquet
functor gives a surjection `r̄_C(Ind_B(π)) → r̄_C(J)`, and the preimage of the
image of `ρ` is the subrepresentation `U` of the hypothesis, with its
surjection onto `ρ`. This statement then places `ρ` in one upper refined
Jacquet module of `π`. The exponent and temperedness argument, the exclusion of
the identity piece, the constituent repair and the adjointness step itself are
not part of this statement.
