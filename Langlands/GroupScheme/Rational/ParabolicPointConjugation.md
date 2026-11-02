# Rational-point adapters for conjugate algebraic parabolics

Authors: Worker 1265 and Worker 113.

This is an internal adapter on the published group-scheme, subgroup-functor
and inner-automorphism constructions. It fixes the direction of rational-point
conjugation needed by the Iwasawa statement family. Its algebraic core applies over any
commutative ring `k`, in an arbitrary universe, with no topology, affineness,
connectedness or reductivity hypothesis. The standard-parabolic
specializations and the topology construction have the additional hypotheses
listed below.

## Definitions and intrinsic laws

For a group scheme `G` over `Spec k`, its point group is the existing
`Langlands.GroupScheme.rationalPoints G`, namely morphisms from the identity
test scheme `Over.mk (𝟙 (Spec k))` to `G.X`.
`SubgroupFunctor.rationalPoints P` is the subgroup obtained by evaluating
the existing subgroup functor `P` at that test scheme. This abbreviation
retains its actual categorical point carrier.

`constantPoint_rationalPoint` identifies restriction of a base point to the
identity test with the original point, reusing `HomConjugacy.constantPoint_self`.
`rationalPoints_map_innerIso` then applies the published
`comp_innerIso_hom`: the actual point map of `G.innerIso g` is the
homomorphism `x ↦ g * x * g⁻¹`. `rationalPoints_map_innerIso_inv`
uses `innerIso_inv_hom` to identify the inverse point map with
`x ↦ g⁻¹ * x * g`.

`SubgroupFunctor.rationalPoints_range` identifies the point subgroup of
`SubgroupFunctor.range j` with the range of the actual rational-point map
of `j : H ⟶ G`. `rationalPoints_comap` identifies evaluation of the
functor preimage with preimage of the point subgroup. Both are definitional
equalities, without a surjectivity-of-points assertion for a quotient.
`rationalPoints_eq_range` gives the same point-range identification when
`P.IsRepresentedBy j` identifies the subgroup functor with `range j`.

The two inner-automorphism preimage formulas record different orientations:

- `rationalPoints_comap_innerIso_hom` identifies
  `(P.comap (G.innerIso g).hom)(k)` with the preimage of `P(k)` under
  `x ↦ g x g⁻¹`, hence with `g⁻¹ P(k) g`.
- `rationalPoints_comap_innerIso_hom_eq_map` expresses that first preimage
  as the image under inverse conjugation.
- `rationalPoints_comap_innerIso_inv` identifies
  `(P.comap (G.innerIso g).inv)(k)` with the image `g P(k) g⁻¹`.

The image formulas use `Subgroup.mem_map_equiv` to test membership by the
inverse automorphism; the inverse-map formula also uses the published
inverse formula for `innerIso`. `mem_rationalPoints_comap_innerIso_hom`
records membership as the literal test `g * x * g⁻¹ ∈ P(k)`.
`rationalPoints_range_comp_innerIso` proves the corresponding image formula
for the actual algebraic map `j ≫ (G.innerIso g).hom`, by transporting
the witnesses in each point-map range.
This applies in particular when `j` is an actual algebraic parabolic inclusion;
no claim that an arbitrary subgroup is algebraic is involved.

`Dynamic.rationalPoints_parabolic_conjugate` identifies the actual
`Dynamic.parabolic` of the conjugate cocharacter `χ ≫ (G.innerIso g).hom`
with the image of `(Dynamic.parabolic χ)(k)` under `x ↦ g x g⁻¹`.
The proof takes the published `parabolic_eq_comap_of_iso`, pulls back
through the inverse inner automorphism, cancels the isomorphism, and
uses the preceding point-preimage formula.

`standardParabolicPoints_comap_innerIso_hom` and
`standardParabolicPoints_comap_innerIso_inv` specialize the general
subgroup-functor formulas to the existing `standardParabolic i ν J` and
`standardParabolicPoints i ν J`. They require a field `k`, a commutative
group scheme `T`, `i : T.toGrp ⟶ G`, a cocharacter `ν`, a set `J` of
characters, and `[IsAffineHom G.X.hom]`, exactly as the existing standard
functor does. They apply to every `J` as identities of those constructions.
Identification with the usual algebraic standard parabolics still requires
the existing maximal-split-torus, positivity, standard-index and
representability/classification hypotheses; these identities do not
discharge them. In particular, the classification convention
`(standardParabolic i ν J).comap (G.innerIso g).hom`
has points `g⁻¹ P_J(k) g`, whereas pullback along `.inv` has points
`g P_J(k) g⁻¹`.

These are intrinsic laws of the existing constructions. They prove no
parabolic classification, building existence, compactness or Iwasawa
decomposition.

## Source use and topology boundary

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Theorem 5.3.4, printed pp.190–191 / PDF pp.221–222, uses rational
conjugation to pass from a minimal parabolic to an arbitrary parabolic.
The definitions and laws in this module are derived point-carrier adapters
for that use, rather than additional assertions attributed to the book.
The mandatory corrections, registered as
`kaletha-prasad-2024-corrections`, 1 November 2024, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.30, repair the preceding Theorem 5.3.3 proof and replace Lemma 5.3.5;
they do not change these conjugation conventions.

In the local-field Iwasawa application, `G(k)` carries the named canonical
`PointTopology.rationalPointTopology k G.X`. Its subgroup topology is the
induced topology on the actual point subgroup.
`rationalPointsConjHomeomorph G g` constructs the multiplicative
homeomorphism of this actual point group with itself, with underlying map
`x ↦ g * x * g⁻¹` and inverse `x ↦ g⁻¹ * x * g`.
It assumes `[TopologicalSpace k] [IsTopologicalRing k]`,
`[IsAffine G.X.left]` and `[LocallyOfFiniteType G.X.hom]`.
Its type explicitly installs the named canonical topology using `letI`,
so an arbitrary caller-supplied topology on `G(k)` is not substituted.
The proof uses the published `rationalPoint_isTopologicalGroup` and
continuity of multiplication by constants. Its application formula is
`rationalPointsConjHomeomorph_apply`; together with
`rationalPoints_map_innerIso` this is the same point map as the actual
scheme inner automorphism. No global topology instance is installed.
No subgroup compactness, openness, or quotient compactness is asserted.

Renard's 9 July 2026 edition, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.5.1(1), printed p.122 / PDF p.128, is consumer row S19(1) of
`notes/renard/chapter-v-structural-inputs.md`. The direct consumer is the
actual-parabolic product family in
`Langlands.BruhatTits.Iwasawa.PointProducts`: its represented-map,
dynamic-cocharacter and standard-functor conjugate carriers have the
forward `g P(k) g⁻¹` orientation proved here.
For S19(1), the final targets must still use the actual special parahoric
`P_x` and the same geometrically defined `K0` as its special-compact
sibling, with the canonical topology and explicit actual-building
existence obligation. These adapters supply none of those objects or
Iwasawa premises. The Iwasawa statements, their proofs, and deductions of
compactness of `G/P` remain separate obligations. Corrected KP 5.3.3 and
the replaced Lemma 5.3.5 belong to the chamber/Iwahori sibling.
