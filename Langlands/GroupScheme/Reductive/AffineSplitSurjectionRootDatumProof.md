# Proof: quasi-finite surjections of split reductive groups respect the splittings

This module proves
[`AffineSplitSurjectionRootDatumStatement`](AffineSplitSurjectionRootDatumStatement.md),
Conrad, *Reductive group schemes* (2014), Proposition 6.1.7 (p.190), over an
affine base `Spec R`. The main theorem is

`Langlands.GroupScheme.affineSplitSurjectionRootDatum :
  AffineSplitSurjectionRootDatumStatement.{u}`.

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

Conrad's argument (pp.187-190) has three parts.

1. The map of character lattices induced by `τ` is locally constant on the base.
2. On each fibre the map `φ` is an isogeny, so the classical theory gives a
   root-datum isogeny with that character map.
3. On root groups the map is `x ↦ c x ^ q` with `c` a unit, which forces `p = 0`
   when `q = p ^ n > 1` (Lemma 6.1.4, pp.188-189).

Conrad also proves that the root bijection is locally constant (Lemma 6.1.3).
The Lean proof does not need this step: the Lean statement asks for one
root-datum isogeny `f` on a neighbourhood, and the proof takes the isogeny
produced at a single point and uses it on the whole neighbourhood.

The three parts are proved in the supporting modules:

1. [`Torus.SplitTorusCharacterIdempotents`](../Torus/SplitTorusCharacterIdempotents.md):
   `splitTorus.exists_isIdempotentElem_characterMapOn` gives, around every point
   `s`, an idempotent `e` of `R` with `s ∈ D(e)` and a linear map `h` such that
   `splitTorus.CharacterMapOn τ D(e) h`.
2. [`Reductive.AffineSplitSurjectionFieldIsogeny`](AffineSplitSurjectionFieldIsogeny.md):
   `exists_rootDatumIsogeny_weightMap` gives, for every point `s`
   of an open set `V` with `CharacterMapOn τ V h`, a root-datum isogeny
   `r : RootDatumIsogeny p Q P` with `r.weightMap = h`.
3. [`Reductive.AffineSplitSurjectionLocalBaseChange`](AffineSplitSurjectionLocalBaseChange.md):
   `natCast_eq_zero_of_local_baseChange` gives `(p : A) = 0` for every local
   `R`-algebra `A` whose spectrum maps into `V`, provided that some root factor of
   `r` differs from `1`. It rests on
   [`Reductive.AffineSplitSurjectionLocalCore`](AffineSplitSurjectionLocalCore.md)
   and [`CommutativeAlgebra.AdditivePrimePower`](../../CommutativeAlgebra/AdditivePrimePower.md).

## Declarations

The first three are in the namespace
`Langlands.GroupScheme.AffineSplitSurjection`.

- `natCast_eq_zero_on_basicOpen`: if `t * n = 0` in `R` for a natural number `n`,
  then `n = 0` in the sections of `Spec R` over the basic open set `D(t)`. The
  restriction of `t` to `D(t)` is a unit.
- `algebraBaseMap_preimage_basicOpen_eq_top`: if the prime `s` lies in `D(e)`,
  then `Spec R_s` maps into `D(e)`. It suffices that the closed point of
  `Spec R_s` maps into `D(e)` (`Scheme.preimage_eq_top_of_closedPoint_mem`). The
  closed point maps to `s`, because the maximal ideal of `R_s` pulls back to `s`
  (`Localization.AtPrime.under_maximalIdeal`).
- `characterMapOn_of_fieldIsogeny` (assembly): it takes the hypotheses of the
  target statement except closedness of the tori and surjectivity of `φ`. It also
  takes the conclusion of step 2 as a hypothesis `hfield`. It proves both
  conclusions of the target, with the character-map clause written as
  `splitTorus.CharacterMapOn`.

The main theorem `affineSplitSurjectionRootDatum` is in the namespace
`Langlands.GroupScheme`. It introduces the binders of the statement and applies
`characterMapOn_of_fieldIsogeny`, with `hfield` given by
`exists_rootDatumIsogeny_weightMap`. The first conclusion is the target's first
conclusion, since `CharacterMapOn` unfolds to the character identity of the
statement. For the second conclusion, every test scheme maps into `⊤`
(`Scheme.Hom.preimage_top`).

## Proof of the assembly

**Part (1).** Let `s` be a point of `Spec R`. Step 1 gives an idempotent `e` with
`s ∈ D(e)` and `h` with `CharacterMapOn τ D(e) h`. Step 2, applied at `s`, gives
`p` and `r` with `r.weightMap = h`.

- If every root factor of `r` is `1`, then `V = D(e)` works.
- Otherwise, choose `β` with `r.rootFactor β ≠ 1`. Step 3 with `A = R_s` (using
  `algebraBaseMap_preimage_basicOpen_eq_top`) gives `(p : R_s) = 0`. Hence
  `t * p = 0` in `R` for some `t ∉ s` (`IsLocalization.exists_of_eq`). Take
  `V = D(e t)`. It contains `s`, since `s` is prime and `e, t ∉ s`. Since
  `e t * p = 0`, `natCast_eq_zero_on_basicOpen` gives `p = 0` on `V`, so the
  root-factor clause holds. The character identity holds on `V` because
  `D(e t) ⊆ D(e)`.

**Part (2).** Suppose `Spec R` is connected. It is nonempty, so pick a point
`s`. Step 1 gives `e` and `h`, and step 2 gives `p` and `r` with
`r.weightMap = h`. The basic open set of an idempotent is clopen
(`PrimeSpectrum.isClopen_iff`). It contains `s`, so by connectedness `D(e)` is
all of `Spec R`. The character identity therefore holds over every test scheme.
If some root factor `r.rootFactor β` differs from `1`, then step 3 applies to
`A = R_𝔪` for every maximal ideal `𝔪`, since `D(e) = ⊤`. Thus `p = 0` in every
localization `R_𝔪`, and so `(p : R) = 0` (`eq_zero_of_localization`).
