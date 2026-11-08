# A finite proper-parabolic supercuspidality test from structural inputs

Worker 1582. This is a conditional reduction for
`FiniteProperParabolicSupercuspidalTestStatement`, which is stated in
`Langlands/Representation/Exponents/SmoothRepNoetherianReduction.lean`. That
statement is a finite form of Renard VI.2.1, Remark 1, printed page 137 / PDF
page 143, in David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In that
remark Renard says that a smooth representation is supercuspidal as soon as its
Jacquet modules along the proper standard parabolics vanish. Standard
parabolics correspond to subsets of the simple roots, so there are finitely
many of them; the remark does not say this, and the finiteness is supplied here.

## Definitions

The section `Faces` fixes `G` with `IsAffineHom G.X.hom`, a torus morphism
`i : T ⟶ G`, a cocharacter `ν` with finitely many simple roots `SimpleRoot i ν`,
and a function `std`. For each actual parabolic datum `D : ParabolicDatum G` with
`¬ IsIso D.p`, `std` gives a `ProperParabolicUnipotentStandardization i ν D.p D.r`:
a proper face `face ⊆ SimpleRoot i ν` and a rational point that conjugates the
standard unipotent subgroup `unipotent i ν face` onto `pointImage (D.r ≫ D.p)`.

- `AttainedProperFace i ν std` is the subtype of faces `I : Finset (SimpleRoot i ν)`
  that are attained, meaning `(std D hD).face = I` for some proper datum `D`. It is
  `Finite`, because the simple roots are finite.
- `AttainedProperFace.ofDatum D hD` is the face attained by `D`.
- `AttainedProperFace.datum I` is a datum attaining `I`, chosen with
  `Classical.choose`. `datum_proper` says that it is proper, and `face_datum` says
  that `std` sends it to `I`.

`AttainedProperFace.subsingleton_coinvariants` takes any complex representation
`ρ` of `G(k)`, a face `I` and a proper datum `D` with `I = (std D hD).face`. If the
coinvariants of `ρ` under `pointImage` of `I.datum`'s radical are `Subsingleton`,
then so are its coinvariants under `pointImage (D.r ≫ D.p)`.

## Statement

`finiteProperParabolicSupercuspidalTest_of_structure` takes three published
structural statements as hypotheses:

- `ParabolicDynamicStatement`: over a field, a closed subgroup of a connected
  reductive group is parabolic exactly when its range is a dynamic parabolic
  `P(χ)` (Milne, Theorem 25.1);
- `SmoothMaximalSplitTorusConjugacyStatement`: two maximal split tori of a smooth
  connected affine group are conjugate by a rational point;
- `RelativeRootSystemStatement`: the relative roots of a maximal split torus of a
  connected reductive group form a root system.

From these it proves `FiniteProperParabolicSupercuspidalTestStatement.{u, v}`.
Fix a nonarchimedean local field `k` and a connected reductive `G` over `k`, and
put the canonical point topology on `G(k)`. Then there are a natural number `n`
and data `D : Fin n → ParabolicDatum G`, each with `¬ IsIso (D i).p`, with this
property: any smooth complex representation `A` (carrier universe `v`) whose
normalized Jacquet modules `(jacquetFunctor (D i).p … ).obj A` are all
`Subsingleton` is `IsSupercuspidal`. That is, its Jacquet module vanishes along
every proper actual rational parabolic datum.

The module proves none of the three inputs. In the Library at the time of
writing each has only conditional derivations, so
`FiniteProperParabolicSupercuspidalTestStatement` stays conditional, and so
does Renard VI.7.5.

## Provenance

The statement is derived. Renard's Remark 1 is about standard parabolics of a
fixed minimal parabolic. The Lean statement only asks for some finite family of
proper actual parabolic data, and they need not be standard. The proof gets the
family by choosing one actual datum for each proper standard face that occurs.

## Implemented proofs

`subsingleton_coinvariants` rewrites `(std D hD).face` as the face of `I.datum`,
using `hI` and `face_datum`. The published linear equivalence
`coinvariantsTranslateEquiv` (`Aubert/General/Conjugation.lean`) is taken for the
conjugating point of `std I.datum`. Its inverse is injective, so the hypothesis
makes the coinvariants under `unipotent i ν face` `Subsingleton`. The same
equivalence for the conjugating point of `std D hD` is injective too, and it
carries this to the coinvariants under `pointImage (D.r ≫ D.p)`. The published
`isSupercuspidal_of_isCuspidal` uses the same step.

The main theorem first introduces `k`, `G`, the affine instance
`hG.isAffineHom`, the point topology and the two topological instances. The
published `exists_maximalSplitTorus_genericCocharacter` gives a maximal split
torus `i : T ⟶ G` and a generic cocharacter `ν`. `RelativeRootSystemStatement`
gives `HasRelativeRootSystem i`, and `simpleRelativeRootFintype` makes
`SimpleRoot i ν` a finite type. Then `std` is defined with the published
`properParabolicUnipotentStandardization` (in `RepresentedCuspidalityComparison`).
That function uses `ParabolicDynamicStatement` and
`SmoothMaximalSplitTorusConjugacyStatement`.

Next, `Finite.equivFin` enumerates `AttainedProperFace i ν std` as an equivalence
`e` with `Fin (Nat.card _)`. The family is `j ↦ (e.symm j).datum`, and
`datum_proper` makes every member proper. Suppose `A` has `Subsingleton` Jacquet
modules along the family. Let `Q` be an arbitrary proper datum and
`I = ofDatum Q`. The member at index `e I` is `(e.symm (e I)).datum`, and its face
is `(std Q hproper).face` by `Equiv.symm_apply_apply`. Normalization does not
change the carrier, so each normalized Jacquet module of `A` is, by definition,
the coinvariants of `A.representation` under `pointImage (r ≫ p)`. Hence
`subsingleton_coinvariants`, applied to the hypothesis at index `e I`, gives the
vanishing along `Q`. That is `IsSupercuspidal A`.

The file opens `CategoryTheory.MonObj` in scoped form, because that scope holds
the group law on `G(k)` as a hom-set of the group object.
