# Algebraic spaces under saturated reduced closed subschemes of a finite cover

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceStatement`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. It imports the definition `SameImage` from
`Langlands.AlgebraicGeometry.AlgebraicSpace.SameImagePoints` and, for the existing predicates,
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement`.

## Statement

`ReducedClosedSubspaceStatement.{u}` is the proposition below. Fix

- a scheme `S : Scheme.{u}`, a scheme `U : Over S` and an algebraic space
  `Y : AlgebraicSpace S`;
- a morphism `f : (schemeToSpace S).obj U ⟶ Y`;
- a scheme `UT : Over S` and a morphism `j : UT ⟶ U` over `S`.

Assume:

- `Y` is quasi-compact (`IsQuasiCompact Y`) and quasi-separated over `S`
  (`IsQuasiSeparated Y`);
- `hom f` is finite and surjective (`IsFinite`, `IsSurjective`: every represented base change
  of `f` to a scheme is a finite, resp. surjective, morphism of schemes);
- `j.left` is a closed immersion and the scheme `UT.left` is reduced;
- the range of `j.left` is saturated: if `SameImage (hom f) u u'` and `u` lies in the range,
  then `u'` lies in the range.

Then there are an algebraic space `YT : AlgebraicSpace S` and a morphism
`fT : (schemeToSpace S).obj UT ⟶ YT` such that:

- `YT` is quasi-compact and quasi-separated;
- `hom fT` is finite and surjective;
- for all points `x`, `x'` of `UT.left`, `SameImage (hom fT) x x'` holds exactly when
  `SameImage (hom f) (j x) (j x')` holds.

The names `_root_.AlgebraicGeometry.IsClosedImmersion` and `_root_.AlgebraicGeometry.IsReduced`
are Mathlib's scheme predicates. They are written with `_root_` because the namespace has a
presheaf-level `IsClosedImmersion` of its own.

## Mathematical content and provenance

Derived. The intended `YT` is the reduced induced closed subspace of `Y` on the closed subset
`T = f(|UT|)` of `|Y|`, which exists by Stacks Project, Properties of Algebraic Spaces,
Lemma 66.12.3 (Tag 03IQ). The intended `fT` is the factorization of `UT ⟶ U ⟶ Y` through it,
which exists because `UT` is reduced and maps into `T`, by Lemma 66.12.4 (Tag 03JJ):

- `fT` is finite: `UT` is a closed subscheme of `U ×_Y YT`, which is finite over `YT`.
- `fT` is surjective because the range of `j` is saturated, so it is the full preimage of `T`.
- Points of `UT` have the same image in `YT` exactly when their images in `U` have the same
  image in `Y`, because `|YT| ⟶ |Y|` is injective (Lemma 66.12.1, Tag 0ABJ).
- `T` is closed because finite morphisms are closed.
- `YT` is quasi-compact, being a closed subspace of a quasi-compact space, and quasi-separated,
  because its diagonal is a base change of the diagonal of `Y` (`YT ⟶ Y` is a
  monomorphism).

The statement records only the properties of `(YT, fT)` that are used downstream, not the
closed immersion `YT ⟶ Y` itself. Any algebraic space with these properties is acceptable.

Use: in the Noetherian induction for `NoetherianQuasiAffineSourceAFStatement`, applied to the
reduced closed subscheme of a quasi-affine cover over a proper closed subset of `|Y|`.

## Source

The Stacks Project Authors, *The Stacks Project*, Chapter 66, Properties of Algebraic Spaces,
version ed88ff78 (source `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`,
file `spaces-properties.pdf`), Section 66.12 "Reduced spaces", printed pp. 15–17:

- Lemma 66.12.3 (Tag 03IQ): "Let `T ⊂ |X|` be a closed subset. There exists a unique closed
  subspace `Z ⊂ X` with the following properties: (a) we have `|Z| = T`, and (b) `Z` is
  reduced."
- Lemma 66.12.4 (Tag 03JJ): "Let `Z ⊂ X` be a closed subspace. Assume `Y` is reduced. A
  morphism `f : Y → X` factors through `Z` if and only if `f(|Y|) ⊂ |Z|`."
