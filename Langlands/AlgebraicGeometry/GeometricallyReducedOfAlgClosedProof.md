# Proof: geometric reducedness from algebraically closed base changes

`Langlands.AlgebraicGeometry.geometricallyReducedOfAlgClosed.{u}` proves the
published `GeometricallyReducedOfAlgClosedStatement.{u}`: a morphism
`f : X ⟶ Y` is geometrically reduced as soon as `pullback f y` is reduced for
every algebraically closed field `K : Type u` and every `y : Spec K ⟶ Y`.

## Auxiliary lemmas

The namespace `GeometricallyReducedOfAlgClosedProof` contains two lemmas.

- `isReduced_of_flat_of_surjective`: if `f : X ⟶ Y` is flat and surjective and
  `X` is reduced, then `Y` is reduced. Every point of `Y` has the form `f x`.
  The stalk map `O_{Y,f x} → O_{X,x}` is flat (`Flat.stalkMap`) and a local
  ring map (part of `f` being a morphism of locally ringed spaces), so it is
  faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`) and hence
  injective. A ring with an injective map into a reduced ring is reduced
  (`isReduced_of_injective`), and a scheme whose stalks are all reduced is
  reduced (`isReduced_of_isReduced_stalk`). This is Stacks Project, Algebra,
  Lemma 10.164.2 (Tag 033F), applied stalkwise. The `algebraize` tactic turns
  the stalk map into an algebra structure so that the faithful-flatness lemma
  applies.
- `surjective_specMap_field`: for a ring map `φ : K →+* L` of fields,
  `Spec L ⟶ Spec K` is surjective, because `Spec K` has a single point: the
  closed point of `Spec L` maps to it.

## Main proof

Mathlib's `GeometricallyReduced.eq_geometrically` rewrites the goal as
`geometrically IsReduced f`, and
`geometrically_iff_of_isClosedUnderIsomorphisms` (reducedness is invariant
under isomorphism) reduces it to: for every field `K : Type u` and every
`y : Spec K ⟶ Y`, the scheme `pullback f y` is reduced.

Fix such `K` and `y`, and let `q : Spec (AlgebraicClosure K) ⟶ Spec K` be
induced by the algebra map `K → AlgebraicClosure K`. Since
`AlgebraicClosure K` is an algebraically closed field in `Type u`, the
hypothesis applied to it and to the point `q ≫ y` says that
`pullback f (q ≫ y)` is reduced. Mathlib's pullback pasting isomorphism
`pullbackLeftPullbackSndIso f y q` identifies
`pullback (pullback.snd f y) q` with `pullback f (q ≫ y)`, so the former is
reduced as well (`isReduced_of_isOpenImmersion` applied to the isomorphism).

The projection `pullback.fst (pullback.snd f y) q` to `pullback f y` is the base
change of `q`, and instance search shows that it is flat and surjective:

- `q` is flat by Mathlib's low-priority instance that every morphism to a
  one-point integral scheme, such as the spectrum of a field, is flat, and
  flatness is stable under base change;
- `q` is surjective by `surjective_specMap_field`, and surjectivity is stable
  under base change.

The first auxiliary lemma, applied to this projection, shows that
`pullback f y` is reduced, which finishes the proof. This is the argument of
Stacks Project, Lemma 33.6.6 (Tag 0384), for the extension
`AlgebraicClosure K / K`, carried out fibrewise over `Y`.

The proof uses only Mathlib and has no other Library dependency than the target
statement. Fields range over `Type u`, the universe of the schemes, and
`AlgebraicClosure K` lies in the same universe. The theorem uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
