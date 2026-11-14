# Statement: quasi-split inner forms over `Spec ℤ`, affine spaces and bases with trivial Picard groups

Worker 75.

`Langlands.GroupScheme.ReductivePicardTrivialQuasiSplitInnerFormStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It records Conrad's Remark 7.2.13, which extends
Proposition 7.2.12 (recorded for semi-local bases in
[`Reductive.SemilocalQuasiSplitInnerFormStatement`](SemilocalQuasiSplitInnerFormStatement.md))
to `Spec ℤ`, to affine spaces over fields of characteristic zero, and to every affine base
whose finite étale covers have trivial Picard groups. It imports:

- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale`, for `Etale` (of morphisms of
  schemes); `Mathlib.RingTheory.Etale.Basic`, for `Algebra.Etale`;
  `Mathlib.RingTheory.PicardGroup`, for `CommRing.Pic`; and
  `Mathlib.RingTheory.MvPolynomial.Basic`, for `MvPolynomial`;
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

These are the imports of the semi-local statement, with `MaximalSpectrum` replaced by the
three Mathlib modules for étale algebras, Picard groups and polynomial rings.

`GroupScheme S` is `Grp (Over S)`. An isomorphism `G₁ ≅ G₂` in it is an isomorphism of group
schemes over `S`.

## Predicates and constructions used

The group-scheme predicates are those of the semi-local statement:

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field (Conrad,
  Definition 3.1.1).
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

The ring-theoretic notions come from Mathlib:

- `Algebra.Etale R R'`: `R'` is a formally étale `R`-algebra of finite presentation, so
  `Spec R' → Spec R` is étale. Together with `Module.Finite R R'`, the morphism
  `Spec R' → Spec R` is finite étale.
- `CommRing.Pic R'`: the Picard group of `R'`, the group of isomorphism classes of
  invertible `R'`-modules under tensor product. `Subsingleton (CommRing.Pic R')` says that
  every invertible `R'`-module is free (Mathlib's `CommRing.Pic.subsingleton_iff`), that is,
  `Pic(Spec R') = 1`.
- `MvPolynomial (Fin n) k`: the polynomial ring `k[x₁, …, xₙ]`, the coordinate ring of
  affine `n`-space `𝔸ⁿ_k`.

## Statement and quantifiers

The proposition first introduces a local predicate `QSInner R` for every commutative ring
`R : Type u`. It holds when, for every `G : GroupScheme (Spec R)` with `IsReductive G`, every
`Gad : GroupScheme (Spec R)` and `p : G ⟶ Gad` with
`RelativeRoot.IsFppfQuotient (center G) p`, and every `c : AutomorphicAction Gad G` with
`c.restrict p = AutomorphicAction.conjugation (𝟙 G)`, with the inner local predicate
`IsInnerForm G'` (there are `U : Over (Spec R)` with `Etale U.hom` and `Surjective U.hom`,
and `e : LocalGroupIso G G' U` with `e.HasInnerDiscrepancy c`), the conjunction of

- (existence) there is `G' : GroupScheme (Spec R)` with `IsRelativeQuasiSplit G'` and
  `IsInnerForm G'`, and
- (uniqueness) for all `G₁ G₂ : GroupScheme (Spec R)` with `IsRelativeQuasiSplit G₁`,
  `IsInnerForm G₁`, `IsRelativeQuasiSplit G₂` and `IsInnerForm G₂`, there is an isomorphism
  `G₁ ≅ G₂`

holds. This is word for word the conclusion of
`ReductiveSemilocalQuasiSplitInnerFormStatement` after its hypothesis
`Finite (MaximalSpectrum R)`.

The proposition asserts the conjunction of three clauses:

1. for every commutative ring `R : Type u` such that every `R'` with `[CommRing R']`,
   `[Algebra R R']`, `Algebra.Etale R R'` and `Module.Finite R R'` (in universe `u`) has
   `Subsingleton (CommRing.Pic R')`, `QSInner R` holds;
2. for every commutative ring `R : Type u` with `Nonempty (R ≃+* ℤ)`, `QSInner R` holds;
3. for every field `k : Type u` with `[CharZero k]` and every `n : ℕ`,
   `QSInner (MvPolynomial (Fin n) k)` holds.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers, which agree with the one-based PDF pages.

- Proposition 7.2.12, p.258: "For semi-local S, up to isomorphism every reductive S-group G
  admits a unique quasi-split inner form G′."
- Proof of Proposition 7.2.12, pp.258–259. It reduces to `G` having a Borel subgroup `B`,
  takes "a class ξ ∈ H¹(S_ét, G/Z_G) which twists G into G′", makes it valued in `B/Z_G`,
  and shows `H¹(S_ét, B/Z_G) = 1`: the unipotent radical has a composition series by vector
  groups, whose cohomology vanishes "because it agrees with the Zariski cohomology and S is
  affine", and "the torus (B/Z_G)/U has the form R_{S′/S}(G_m) for a finite étale cover
  S′ → S", with `H¹(S_ét, R_{S′/S}(G_m)) ≃ H¹(S′_ét, G_m) = Pic(S′)`; "Since S′ is
  semi-local, Pic(S′) = 1."
- Remark 7.2.13, p.259: "The only role of semi-locality for the affine S in the proof of
  Proposition 7.2.12 is to ensure that every finite étale cover of S has trivial Picard
  group. Thus, the conclusion also holds (with the same proof) for S = Spec Z and S = A^n_k
  for a field k of characteristic 0."
- Inner forms, p.253: "The inner forms of G are the forms of G that correspond to the image
  of H¹(S_ét, G/Z_G) in H¹(S_ét, Aut_{G/S})."
- Definition 5.2.10, p.157: "A reductive group G → S is quasi-split over S if it admits a
  Borel subgroup scheme over S."

## Derivation from the source

- **The conclusion `QSInner R`.** "The conclusion" of Remark 7.2.13 is that of
  Proposition 7.2.12: up to isomorphism every reductive `S`-group admits a unique
  quasi-split inner form. `QSInner R` encodes it exactly as the semi-local statement does;
  its Markdown explains the encoding of `G/Z_G`, of its action `c` (unique when it exists),
  of inner forms through one étale surjective `U ⟶ Spec R` and local isomorphisms with inner
  discrepancies, and of quasi-splitness (Definition 5.2.10).
- **Clauses 2 and 3.** These are the two cases the remark names: `S = Spec ℤ`, stated for
  every ring isomorphic to `ℤ` so that it lives in universe `u`, and `S = 𝔸ⁿ_k =
  Spec k[x₁, …, xₙ]` for a field `k` of characteristic zero and any `n` (`n = 0` gives
  `Spec k`).
- **Clause 1.** The first sentence of the remark says that the proof of
  Proposition 7.2.12 works for an affine `S` as soon as every finite étale cover of `S` has
  trivial Picard group; clause 1 records this criterion. Finite étale covers of
  `S = Spec R` are affine, of the form `Spec R'` for a finite étale `R`-algebra `R'`, and
  `Pic(Spec R') = Pic(R')`. The clause quantifies over all finite étale `R`-algebras, not
  only faithful ones. This is equivalent: a finite étale `R'` is supported on an open and
  closed subset `Spec (R e)` (`e` idempotent), `R' × R(1 - e)` is then a finite étale cover,
  and its Picard group is `Pic(R') × Pic(R(1 - e))`. Universe `u` loses nothing, since every
  finite `R`-algebra is isomorphic to one in the universe of `R`. Clause 1 includes the
  semi-local case: finite algebras over a semi-local ring are semi-local, and Mathlib proves
  `Subsingleton (CommRing.Pic R')` for semi-local `R'`. Clauses 2 and 3 are the cases of
  clause 1 named by the source; deriving them from clause 1 requires that every finite étale
  `ℤ`-algebra is a product of copies of `ℤ` (Minkowski), and that every finite étale
  `k[x₁, …, xₙ]`-algebra is `k'[x₁, …, xₙ]` for a finite étale `k`-algebra `k'` when
  `char k = 0`. The proposition states all three clauses.

## Scope

All objects are in universe `u`. In clause 1, `R` is any commutative ring; it need not be
Noetherian, local or connected, and the zero ring is allowed (over it `QSInner` holds
trivially). No splitting of `G`, maximal torus, Borel subgroup or constancy of the root
datum of `G` is assumed. The field `k` of clause 3 is any field of characteristic zero.

## Not stated

As in the semi-local statement, the proposition does not assert that `G/Z_G` or the action
`c` exist (Conrad §3.3 and Theorem 7.1.9); without such `Gad`, `p` and `c` the clauses hold
vacuously. It does not state the facts about `Spec ℤ` and `𝔸ⁿ_k` that place them under
clause 1, the existence result over a general base (Proposition 7.2.11), that being an inner
form is an equivalence relation, or the vanishing `H¹(S_ét, B/Z_G) = 1` used in the proof.

## Relation to the Library

- [`Reductive.SemilocalQuasiSplitInnerFormStatement`](SemilocalQuasiSplitInnerFormStatement.md)
  is Proposition 7.2.12. With Mathlib's semi-local Picard instance it follows from clause 1.
- [`Reductive.RelativeQuasiSplitInnerFormStatement`](RelativeQuasiSplitInnerFormStatement.md)
  records the existence of quasi-split inner forms over a general base (Proposition 7.2.11).
