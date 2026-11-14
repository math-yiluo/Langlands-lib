# Naturality of torus Kottwitz homomorphisms for actual torus morphisms

Source: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 11.1.1 and its proof, printed pp. 421–422 (PDF pp. 452–453);
Lemma 11.1.3 and its proof, printed p. 422 (PDF p. 453); and Lemma 11.5.1
and its proof, printed p. 430 (PDF p. 461). The setting is the one fixed on
printed p. 420 (PDF p. 451). The authors' corrections of 1 November 2024
change only §11.7 in Chapter 11, so these passages are unchanged.

## Provenance

This statement is derived, not quoted. The text of Proposition 11.1.1 does
not state functoriality on its own. It characterizes `κ_T : T(K) → X_*(T)_I`
by the norm square for every finite Galois extension `L/K` splitting `T`, and
it proves uniqueness from surjectivity of the norm `T(L) → T(K)`. That
characterization and uniqueness imply functoriality for a morphism of tori
`f : S → T`. Choose one finite Galois `L/K` splitting both tori. For
`t ∈ S(L)`, the norm commutes with `f`, the split valuation map commutes
with `f_*` on cocharacters, and the projection to inertia coinvariants
commutes with `f_*`. So `κ_T ∘ f` and `f_* ∘ κ_S` agree on norms. Because
the norm `S(L) → S(K)` is surjective, they agree everywhere.

The book uses this functoriality without stating it separately. The proof of
Lemma 11.1.3 cites "the functoriality of `κ_T` and `ω_T`" for the maximal
split quotient `T → A`. The proof of Lemma 11.5.1 cites "the functoriality of
the Kottwitz homomorphism for tori" for the homomorphism of tori `Z → D`.
This file makes that functoriality an explicit Library proposition for those
consumers. It is a torus-level input to the reductive construction, not a
consequence of it.

## Lean statement

`TorusKottwitzNaturalityStatement` in `Langlands.Geometry.Building.Kottwitz`
is a Prop-valued definition. It has no proof here. Write
`K = UnramifiedClosure F` and `E = SeparableClosure F`.

It quantifies over exactly the fields and towers that
`TorusKottwitzExistenceStatement` allows:

- every nonarchimedean local field `F`;
- every coefficient field `k`, with algebra maps `k → K` and `k → E`
  forming a scalar tower `k → K → E`;
- the single extra hypothesis `Normal k K`.

There is no further restriction on the characteristic or the residue field.
The statement does not assume that `E` is a separable closure of `k`, and it
makes no splitness, rank or ramification assumption on the tori. The case
`k = K` is the setting of Proposition 11.1.1. A general `k` gives the same
assertion for the base changes `S_K` and `T_K`, with points and cocharacters
read through the actual coefficient-point and base-change constructions.

For actual commutative group schemes `S` and `T` over `Spec k`, with proofs
`hS : IsTorus S.toGrp` and `hT : IsTorus T.toGrp`, it takes every actual
morphism `f : S ⟶ T` of commutative group schemes and every point
`x : torusKPoints F k S` (a `K`-coefficient point of `S`). It asserts the
exact equation

```
(torusKottwitz F k T hT
    (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
  torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
    (torusKottwitz F k S hS x).toAdd
```

in `TorusTarget F k T`. That is, `κ_T(f(x)) = f_*(κ_S(x))`.

## The maps

- `affinePointsTarget` applies `f` to `K`-coefficient points by
  postcomposition.
- `torusKottwitz` (in `TorusMap`) is the homomorphism chosen by
  `Classical.epsilon` to satisfy the norm characterization
  `IsTorusKottwitzHom`. Its unconditional specification is
  `TorusKottwitzExistenceStatement`, which is **not** a premise here. If no
  homomorphism with the norm law existed, the chosen map would be arbitrary,
  so a proof of this naturality statement has to establish or import the
  norm law for both tori.
- `torusInertiaMap` (in `TorusInertiaFunctoriality`) is the map on integral
  inertia coinvariants `torusInertiaCoinvariants k K E` induced by
  `geometricCocharacterMap`. That map postcomposes a geometric cocharacter
  over `E` with the base change of `f` to `E`. The coinvariants are taken for
  `relativeInertia k K E`, the automorphisms of `E` over `k` that fix `K`;
  this is the inertia group `I = Gal(E/K)`. The induced map uses Mathlib's
  map on coinvariants for this intertwining map.

## Scope

The targets are the integral coinvariants, torsion included. Nothing is
passed to the torsion-free quotient or tensored with `ℚ`.

None of the following is a premise of the proposition:

- a chosen substitute map, a naturality hypothesis or a commuting-square
  witness;
- the torus existence, descent or equivariance statements;
- any reductive Kottwitz existence, functoriality or descent statement.

The statement says nothing about the rational-point restriction
`torusKottwitzRational` or about Galois equivariance.

## Consumer

The published theorem `simplyConnectedDerivedKottwitz_natural_of_torus_naturality`
in `SimplyConnectedDerivedNaturalityReduction` takes a hypothesis `hnat`. That
hypothesis is exactly the instance of this proposition for the induced
cocenter morphism `cH.map cG hH f`, with `S = cH.torus` and `T = cG.torus`.
Its coefficient tower also assumes `IsSepClosure k (SeparableClosure F)`,
which this statement does not need.
