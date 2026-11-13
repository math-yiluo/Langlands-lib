# Statement: quasi-split inner forms of reductive groups over a semi-local base

Worker 75.

`Langlands.GroupScheme.ReductiveSemilocalQuasiSplitInnerFormStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale`, for `Etale`, and
  `Mathlib.RingTheory.Spectrum.Maximal.Defs`, for `MaximalSpectrum`;
- [`AutomorphicAction`](../AutomorphicAction.md), for `AutomorphicAction`,
  `AutomorphicAction.restrict` and `AutomorphicAction.conjugation`;
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G`;
- [`Rational.InnerDiscrepancy`](../Rational/InnerDiscrepancy.md), for
  `LocalGroupIso.HasInnerDiscrepancy`, and transitively
  [`LocalGroupIso`](../LocalGroupIso.md), for `LocalGroupIso`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`RelativeLevi.Borel`](../RelativeLevi/Borel.md), for `IsRelativeQuasiSplit`, and
  transitively [`Reductive.Basic`](Basic.md), for `IsReductive`.

`GroupScheme S` is `Grp (Over S)`. An isomorphism `G₁ ≅ G₂` in it is an isomorphism of group
schemes over `S`.

## Predicates and constructions used

- `Finite (MaximalSpectrum R)`: the commutative ring `R` has only finitely many maximal
  ideals, that is, `R` is semi-local.
- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field.
- `center G`: the subgroup functor of all-test central points of `G`, the functor of points
  of the scheme-theoretic centre `Z_G`.
- `RelativeRoot.IsFppfQuotient N q`: the underlying morphism of `q` is flat, surjective and
  locally of finite presentation, and the range of the scheme kernel of `q` is `N`.
- `AutomorphicAction A G`: an action of `A` on `G` by group automorphisms, given by one
  morphism `A × G → G` with the action laws on the points over every `T : Over S`.
  `c.restrict p` is the action through `p`, and `AutomorphicAction.conjugation (𝟙 G)` is
  conjugation `g · x = g x g⁻¹` of `G` on itself.
- `LocalGroupIso G G' U`, for `U : Over S`: for every `Z : Over S` and every point
  `b : Z ⟶ U`, a group isomorphism `e_b` from the `Z`-points of `G` to the `Z`-points of
  `G'`, natural in `Z`. This is an isomorphism `G_U ≅ G'_U` of group schemes over `U`.
- `e.HasInnerDiscrepancy c`: for every `T : Over S` and every two points
  `b b' : T ⟶ U` there is a point `x : T ⟶ Gad` such that, on every `t : W ⟶ T` and every
  `W`-point `g` of `G`, `e_{t ≫ b} (c.act (t ≫ x) g) = e_{t ≫ b'} g`. So the discrepancy
  `e_b⁻¹ ∘ e_{b'}` between the two local isomorphisms is the automorphism of `G` given by
  the point `x` of `Gad` through `c`.
- `IsRelativeQuasiSplit G'` (Conrad Definition 5.2.10): `G'` is reductive and has a Borel
  subgroup over the base, a relative parabolic subgroup whose residue fibres are Borel
  subgroups.

## Statement and quantifiers

The proposition quantifies over every commutative ring `R : Type u` with
`Finite (MaximalSpectrum R)`, every `G : GroupScheme (Spec R)` with `IsReductive G`, every
`Gad : GroupScheme (Spec R)` and `p : G ⟶ Gad` with
`RelativeRoot.IsFppfQuotient (center G) p`, and every `c : AutomorphicAction Gad G` with
`c.restrict p = AutomorphicAction.conjugation (𝟙 G)`.

It introduces a local predicate. `IsInnerForm G'`, for `G' : GroupScheme (Spec R)`, holds
when there are `U : Over (Spec R)` with `Etale U.hom` and `Surjective U.hom`, and
`e : LocalGroupIso G G' U` with `e.HasInnerDiscrepancy c`.

It asserts the conjunction of:

1. (existence) there is `G' : GroupScheme (Spec R)` with `IsRelativeQuasiSplit G'` and
   `IsInnerForm G'`;
2. (uniqueness) for all `G₁ G₂ : GroupScheme (Spec R)` with `IsRelativeQuasiSplit G₁`,
   `IsInnerForm G₁`, `IsRelativeQuasiSplit G₂` and `IsInnerForm G₂`, there is an
   isomorphism `G₁ ≅ G₂`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Proposition 7.2.12, p.258: "For semi-local S, up to isomorphism every reductive S-group G
  admits a unique quasi-split inner form G′."
- Proof of Proposition 7.2.12, pp.258–259. It reduces to `G` having a Borel subgroup `B` as
  in Proposition 7.2.11, takes "a class ξ ∈ H¹(S_ét, G/Z_G) which twists G into G′", makes
  it valued in `B/Z_G` by étale-local conjugacy of Borel subgroups (Corollary 5.2.13), and
  shows `H¹(S_ét, B/Z_G) = 1` using Theorem 5.4.3 and `Pic(S′) = 1` for the semi-local
  finite étale cover `S′`. Remark 7.2.13, p.259: "The only role of semi-locality for the
  affine S in the proof of Proposition 7.2.12 is to ensure that every finite étale cover of
  S has trivial Picard group."
- Proposition 7.2.11, p.258: over any non-empty `S`, a reductive `S`-group whose geometric
  fibres have a given root datum has a quasi-split inner form (with further properties).
- Inner forms, p.253: "Consider a reductive group G over a non-empty scheme S. The inner
  forms of G are the forms of G that correspond to the image of H¹(S_ét, G/Z_G) in
  H¹(S_ét, Aut_{G/S})."
- Definition 5.2.10, p.157: "A reductive group G → S is quasi-split over S if it admits a
  Borel subgroup scheme over S."

## Derivation from the source

- **Semi-local base.** Conrad's "semi-local S" is affine (Remark 7.2.13 speaks of "the
  affine S"), the spectrum of a semi-local ring. A semi-local ring is a commutative ring
  with finitely many maximal ideals, stated as `Finite (MaximalSpectrum R)`. No Noetherian
  hypothesis is imposed; the proof uses only that finite étale covers of `S` are
  semi-local and hence have trivial Picard group.
- **`G/Z_G` and its action.** As in `ReductiveConnectedActionInnerStatement`
  (Proposition 7.2.6), `G/Z_G` is a group scheme `Gad` with an fppf quotient map
  `p : G ⟶ Gad` whose kernel has range `center G`, and its natural action on `G` is the
  action `c` whose restriction along `p` is conjugation. Since `p × 𝟙 : G × G → Gad × G` is
  an fppf epimorphism, at most one such `c` exists.
- **Inner forms.** A form `G′` of `G` is given by an étale cover of `S` and isomorphisms
  `G_U ≅ G′_U` on it. Its class in `H¹(S_ét, Aut_{G/S})` is the cocycle of discrepancies of
  these isomorphisms on the overlaps. The class lies in the image of `H¹(S_ét, G/Z_G)`
  exactly when, for some such cover and isomorphisms, every discrepancy is the action of a
  point of `G/Z_G`. In the encoding the cover is one étale surjective morphism
  `U ⟶ Spec R` (a disjoint union of the members of a cover), the isomorphisms are
  `e : LocalGroupIso G G' U`, and the condition on the discrepancies is
  `e.HasInnerDiscrepancy c`. Every pair of points `b b' : T ⟶ U` factors through the
  overlap `U ×_S U`, so this is the condition on overlaps.
- **Quasi-split.** `IsRelativeQuasiSplit` is the Library transcription of Definition 5.2.10.
  Conrad notes there that SGA3's relative notion has additional requirements, but that the
  two notions agree for semi-local `S` (SGA3 XXIV 3.9.1).
- **"Up to isomorphism … a unique".** Item 1 is the existence of a quasi-split inner form.
  Item 2 is its uniqueness up to isomorphism of group schemes over `Spec R`.

## Scope

All objects are in universe `u`. `R` is any commutative ring with finitely many maximal
ideals; it need not be Noetherian, local or connected. The zero ring is allowed, and over
it the statement holds trivially. No splitting of `G`, maximal torus, Borel subgroup or
constancy of the root datum of `G` is assumed.

## Not stated

The statement does not assert that the quotient `G/Z_G` or the action `c` exist (Conrad
§3.3 and Theorem 7.1.9); without such `Gad`, `p` and `c` it holds vacuously. It does not
state the existence result over a general base (Proposition 7.2.11) or its additional
properties (a section of `Aut_{G′/S} → Out_{G′/S}`, a maximal torus in a Borel subgroup,
and the description of `T′/Z_{G′}` as a Weil restriction). It does not state that being an
inner form is an equivalence relation, or the vanishing `H¹(S_ét, B/Z_G) = 1` used in the
proof.
