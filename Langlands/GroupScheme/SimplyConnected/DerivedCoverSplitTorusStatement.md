# Maximal split tori through the simply connected cover of a derived subgroup

Author: Worker 1384.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.SimplyConnectedDerivedCoverSplitTorusStatement`. The
Lean file only defines the proposition. It contains no proof of it, and it
adds no new definitions or axioms.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over every
`k : Type u` with `[Field k]`. The field may be imperfect and may have
positive characteristic. It also quantifies over:

- group schemes `G D C : GroupScheme (Spec (CommRingCat.of k))` and
  homomorphisms `d : D ⟶ G` and `π : C ⟶ D` with
  `IsSimplyConnectedDerivedCover d π`. This published predicate from
  [`SimplyConnected.DerivedCover`](DerivedCover.md) says three things. `G`
  is connected reductive. `d` is a closed immersion whose range is the full
  scheme-theoretic derived subgroup of `G` (`IsDerivedSubgroup d`). `π`
  satisfies `IsSimplyConnectedCover π`, so `D` is semisimple, `C` is
  simply connected and `π` is a central isogeny.
- a commutative group scheme `S` and a homomorphism `i : S.toGrp ⟶ G` with
  `IsMaximalSplitTorus i`, the published predicate from
  [`Rational.SplitTorus`](../Rational/SplitTorus.md).

No hypothesis mentions a torus of `D` or `C`, or a cocharacter. So none of
the conclusions is assumed.

## Conclusion

The conclusion has two existential layers, the derived torus and then the
covering torus.

**The derived torus.** There exist a commutative group scheme `S_D`, a
homomorphism `j : S_D.toGrp ⟶ D` and a homomorphism of commutative group
schemes `e : S_D ⟶ S` such that

1. `IsMaximalSplitTorus j`: `j` is a maximal split torus of `D`;
2. `IsClosedSubgroup (CommGroupScheme.groupHom e)`: the underlying morphism
   of schemes of `e` is a closed immersion, so `S_D` is a closed subtorus
   of `S`;
3. `j ≫ d = CommGroupScheme.groupHom e ≫ i`: the two inclusions of `S_D`
   into `G`, through `D` and through `S`, agree.

**The covering torus.** For these data, there exist a commutative group
scheme `S_C`, a homomorphism `i_C : S_C.toGrp ⟶ C` and a homomorphism of
commutative group schemes `f : S_C ⟶ S_D` such that

4. `IsMaximalSplitTorus i_C`: `i_C` is a maximal split torus of `C`;
5. `i_C ≫ π = CommGroupScheme.groupHom f ≫ j`: the square with the cover
   `π` commutes;
6. `IsCentralIsogeny (CommGroupScheme.groupHom f)`: the underlying morphism
   of schemes of `f` is finite, flat, surjective and locally of finite
   presentation, with central kernel (published in
   [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md));
7. `i_C ≫ π ≫ d = CommGroupScheme.groupHom (f ≫ e) ≫ i`: the ambient map
   `S_C → S` is the composite `f ≫ e` through the derived torus, and it is
   compatible with the ambient composite `π ≫ d : C → G`.

**Rational and real identification.** The cocharacter maps are the
published ones from
[`Rational.RelativeCentralDirections`](../Rational/RelativeCentralDirections.md).
`RealTorusSpace.cocharacterMapInt g` sends a cocharacter `ν` to `ν ≫ g`, on
the actual lattices `cocharacterLattice` of
[`Torus.Lattice`](../Torus/Lattice.md). `RealTorusSpace.cocharacterMapReal g`
is its real scalar extension
`(cocharacterMapInt g).baseChange ℝ : RealTorusSpace.V _ →ₗ[ℝ] RealTorusSpace.V _`.
The rational map is written inline as `(cocharacterMapInt g).baseChange ℚ`
on `ℚ ⊗[ℤ] cocharacterLattice _`; no new map is defined. Then:

8. `(cocharacterMapInt (f ≫ e)).baseChange ℚ` is injective;
9. its range equals the range of `(cocharacterMapInt e).baseChange ℚ`;
10. `cocharacterMapReal (f ≫ e)` is injective;
11. its range equals the range of `cocharacterMapReal e`.

Thus the rational and real cocharacter spaces of `S_C` are identified,
through `f ≫ e`, with the image of those of the derived torus `S_D` in those
of `S`.

All objects are existential. No chosen torus or construction is presented.

## What is not asserted

The statement asserts no surjectivity onto `S`. The map `f ≫ e : S_C → S`
is not surjective when `G` has a nontrivial central split torus. For
example, with `G = GL_n` and `S` the diagonal torus, `S_D` is the diagonal
torus of `SL_n`, of dimension `n - 1`. Accordingly, the ranges in items 9
and 11 are in general proper subspaces.

The statement does not identify `S_D` with the scheme-theoretic intersection
of `S` and `D`, or `S_C` with the inverse image of `S_D` in `C`. It asserts
nothing on the integral level for `f ≫ e`. For instance, with
`G = D = PGL_2` and `C = SL_2`, the map `f` on diagonal tori is the
squaring map of `𝔾_m`, whose integral cocharacter map has cokernel `ℤ/2`.
Nothing is asserted about `k`-points or about uniqueness.

## Related statements

Items 4–6 are the conclusion of
[`SimplyConnected.SplitTorusStatement`](SplitTorusStatement.md) for the cover
`π : C → D` and the maximal split torus `j`. That statement is not imported,
so this module states the composite structure self-containedly. For `f`,
Worker 1392's `SplitTorusIsogenyCocharacterStatement` in
[`Rational.SplitTorusIsogenyCocharacter`](../Rational/SplitTorusIsogenyCocharacter.md)
states integral injectivity with finite cokernel and rational and real
bijectivity. Its proved lemmas
`comp_groupHom_eq_one_iff_of_comp_eq_of_isClosedSubgroup` and
`mem_range_kernelι_groupHom_iff_of_comp_eq_of_isClosedSubgroup` compare the
points killed by `f` with those killed by `i_C ≫ π`, using item 5 and the
closed immersion `j`. This module does not import that one either.

## Sources and provenance

The statement is derived, not a verbatim theorem.

**Classical language.** Borel and Tits use affine algebraic groups defined
over `k` in the classical sense. These are the smooth affine group schemes
of finite type over `k` that `IsConnectedReductive` and `IsSplitTorus`
describe.

**The derived torus (items 1–3).** Borel and Tits, *Groupes réductifs*
(1965), §0.6, printed p.59 (PDF p.6), call `G` the almost direct product of
normal subgroups when the product map is surjective with finite kernel.
Proposition 2.2 and §2.3, printed pp.63–64 (PDF pp.10–11), show that a
connected reductive `G` is the almost direct product of its connected
centre, a torus, and its derived group `𝒟G`, which is semisimple.
Proposition 4.27, printed p.94 (PDF p.41), is for an arbitrary field `k`.
If `G` is the almost direct product of connected normal `k`-subgroups
`G_i` and `S` is a maximal `k`-split torus of `G`, then `S_i = (S ∩ G_i)°`
is a maximal `k`-split torus of `G_i`. Applied to the derived group, this
gives `S_D = (S ∩ D)°`. It is a closed subtorus of `S`, contained in `D`,
which gives items 1–3.

Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
(2015), give the scheme-theoretic form. Definition C.2.11, printed p.599
(PDF p.625), defines a quasi-reductive group as a smooth connected affine
group with trivial `R_us,k`, which includes every connected reductive group.
Theorem C.2.15, printed p.603 (PDF p.629), says that for quasi-reductive
`G` with maximal `k`-split torus `S`, `S′ := (S ∩ D(G))⁰_red` is a maximal
`k`-split torus of `D(G)`. It also says that `S` is an almost direct product
of `S′` and the maximal central split torus.

**The covering torus (items 4–7).** Borel and Tits, *Compléments à
l'article « Groupes réductifs »* (1972), Théorème 2.20(ii), printed p.260
(PDF p.9), applies to the central surjective morphism `π` from the
connected reductive group `C`. The setting of their §2, printed p.253
(PDF p.2), is an arbitrary commutative field. A maximal `k`-split torus
`S_C` of the inverse image of `S_D` is a maximal `k`-split torus of `C`.
Its image is a maximal `k`-split torus of `D` contained in `S_D`, hence
equal to `S_D`. Remarque 2.3, printed p.254 (PDF p.3), says that central
means that the scheme-theoretic kernel lies in the centre. The restriction
`f : S_C → S_D` is surjective with kernel the inverse image of `ker π`
under `i_C`, a closed subscheme of the finite scheme `ker π`. Conrad,
*Reductive group schemes* (2014), Proposition 3.3.10 with Definition 3.3.9,
PDF p.103, then makes `f` a finite flat surjection with central kernel.
Over a field, `f` is locally of finite presentation. Item 7 follows from
items 3 and 5.

**Rational and real identification (items 8–11).** By the proof of
Corollary 1.9 in the 1965 article, printed p.62 (PDF p.9), a `k`-isogeny of
tori maps the character group of the target injectively onto a subgroup of
finite index of the character group of the source. The 1972 article,
Remarque 4.5(b), printed p.273 (PDF p.22), recalls that the cocharacter
group `X_*(S)`, the morphisms from `GL_1` to `S`, is canonically the
`ℤ`-dual of the character group. Dualizing a finite-index inclusion of
lattices of equal rank gives a rational isomorphism, so `f` induces a
bijection on rational and on real cocharacters. The closed immersion `e`
induces an injective map on cocharacters, and so do its scalar extensions
to the flat `ℤ`-modules `ℚ` and `ℝ`. The composite therefore has the stated
injectivity and the same range as the map induced by `e`.

**Arbitrary-field scope.** The cited Borel–Tits and Conrad–Gabber–Prasad
results are stated over an arbitrary field. No valued-field hypothesis is
imported.

**Application.** Kaletha and Prasad, *Bruhat–Tits theory: a new approach*
(2023), printed p.103 (PDF p.134), take `A′_M` to be the maximal torus in
`A_M ∩ G_der`. Definitions and Facts 2.6.20–2.6.23, printed p.104 (PDF
p.135), use the simply connected cover. The proof of Lemma 2.6.29, printed
p.106 (PDF p.137), takes `S′` in this way for `M = Z_G(S)` and the maximal
torus `S_sc` in the preimage of `S` in `G_sc`. It uses that `S_sc → S′` is
an isogeny, so that `X_*(S_sc)` has finite index in `X_*(S′)`. Their 2024 corrections, PDF p.25, insert before Definition
2.6.20 that `k` is Henselian with perfect residue field. That restriction
concerns the valued-field application and is not imported here.

No retained errata for the two Borel–Tits articles were found other than
the 1972 article's own corrections to the 1965 article (§1.2 and §5,
printed pp.253–254 and 274–275). Those corrections do not concern the
cited passages. No retained project errata for Conrad–Gabber–Prasad or for
Conrad's notes was found.
