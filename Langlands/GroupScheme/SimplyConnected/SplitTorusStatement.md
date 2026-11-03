# Maximal split tori of an actual simply connected cover

Author: Worker 1384.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.SimplyConnectedCoverSplitTorusStatement`. The Lean
file only defines the proposition. It contains no proof of it, and it adds
no new definitions or axioms.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over every
`k : Type u` with `[Field k]`. The field may be imperfect and may have
positive characteristic. It also quantifies over:

- group schemes `G C : GroupScheme (Spec (CommRingCat.of k))` and a
  homomorphism `π : C ⟶ G` with `IsSimplyConnectedCover π`. This published
  predicate from [`SimplyConnected.Basic`](Basic.md) says three things.
  `G` is semisimple, so it is smooth, affine, connected and reductive with
  finite centre. `C` is algebraically simply connected, so in particular
  semisimple. `π` is a central isogeny with the stated unique-factorization
  law.
- a commutative group scheme `S` and a homomorphism `i : S.toGrp ⟶ G` with
  `IsMaximalSplitTorus i`. This published predicate from
  [`Rational.SplitTorus`](../Rational/SplitTorus.md) says that `S` is a
  split torus and `i` is a closed immersion. It also says that every
  factorization of `i` through another split subtorus of `G` is an
  isomorphism.

The universal-property field of `IsSimplyConnectedCover` is not needed for
the mathematics below; only semisimplicity and the central-isogeny field
are used. The hypotheses mention no torus of `C`, so the conclusion is not
assumed.

## Conclusion

There exist

- a commutative group scheme `S_C` over `Spec k`,
- a homomorphism `i_C : S_C.toGrp ⟶ C`, and
- a homomorphism of commutative group schemes `f : S_C ⟶ S`

such that

1. `IsMaximalSplitTorus i_C`: `i_C` is a maximal split torus of `C`;
2. `i_C ≫ π = CommGroupScheme.groupHom f ≫ i`: the square with the cover
   commutes, so `f` is the restriction of `π` to `S_C`, landing in `S`;
3. `IsCentralIsogeny (CommGroupScheme.groupHom f)`: the underlying morphism
   of schemes of `f` is finite, flat, surjective and locally of finite
   presentation, and its scheme-theoretic kernel is central. This is the
   published predicate from
   [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md).

All three objects are existential. No chosen torus, chosen preimage or
construction is presented.

## What is not asserted

The statement does not identify `S_C` with the inverse image of `S` in `C`.
That inverse image contains the whole kernel of `π`, and this kernel need
not lie in `S_C`. For example, let `D` be a quaternion division algebra over
`k`. Take `C = SL₁(D)` and `G = C/μ₂`, both anisotropic. Then `S` and `S_C`
are trivial, but the inverse image of `S` is the kernel `μ₂` of `π`. The
inverse image can therefore carry additional finite central information.

The statement asserts nothing about `k`-points: `f` need not be surjective
on `k`-points. It does not assert that the inverse image of `S` is a torus
or is smooth. It does not assert uniqueness of `S_C`, `i_C` or `f`.

## Related Library results

The comparison of points killed by `f` with points killed by `i_C ≫ π`, on
every test scheme, is not repeated here. It follows from item 2 of the
conclusion and the closed immersion `i` (supplied by `IsMaximalSplitTorus i`
as `hi.1.2`), by the proved lemmas
`comp_groupHom_eq_one_iff_of_comp_eq_of_isClosedSubgroup` and
`mem_range_kernelι_groupHom_iff_of_comp_eq_of_isClosedSubgroup` in Worker
1392's module
[`Rational.SplitTorusIsogenyCocharacter`](../Rational/SplitTorusIsogenyCocharacter.md).
That module also states `SplitTorusIsogenyCocharacterStatement`: for an
isogeny of split tori, the integral cocharacter map is injective with finite
cokernel, and its rational and real scalar extensions are bijective. Item 3
of the conclusion and the splitness of `S_C` and `S` supply its hypotheses
for `f`. This module does not import that one.

## Sources and provenance

The statement is derived, not a verbatim theorem.

**Existence of `S_C` and surjectivity onto `S`.** Borel and Tits,
*Compléments à l'article « Groupes réductifs »* (1972), Théorème 2.20(ii),
printed p.260 (PDF p.9), is the source. Throughout their §2, printed p.253
(PDF p.2), `k` is an arbitrary commutative field and the source group is
connected reductive. For a central surjective `k`-morphism `f : G → G'`,
part (ii) says that the maximal `k`-split tori of the target are the images
of maximal `k`-split tori of the source. It also says that the maximal
`k`-split tori of the source are the maximal split tori of the inverse
images of maximal `k`-split tori of the target. No separability hypothesis
appears. Remarque 2.3, printed p.254 (PDF p.3), says that in scheme
language a morphism is central exactly when its scheme-theoretic kernel
lies in the centre. This matches the Library's `IsCentralIsogeny`.
Borel and Tits use affine algebraic groups defined over `k` in the
classical sense. These are the smooth affine group schemes of finite type
over `k` that `IsConnectedReductive` and `IsSplitTorus` describe.

Apply this to the source `C`, which is connected reductive, and the central
isogeny `π`. Let `S_C` be a maximal `k`-split torus of the inverse image of
`S`. By the theorem it is a maximal `k`-split torus of `C`. Its image
`π(S_C)` is a `k`-split torus contained in `S`, and it is a maximal
`k`-split torus of `G`, so `π(S_C) = S`. The 1965 article, Proposition
4.25, printed p.94 (PDF p.41), proves the analogous statement only for
separable isogenies, with neutral components of inverse images. The 1972
§1.2, printed pp.253–254 (PDF pp.2–3), replaces the erroneous example 4.26
of the 1965 article. It notes that an isogeny changing the `k`-rank can be
neither separable nor central. This is why the central-isogeny hypothesis is
the relevant one.

**`f` is a central isogeny in the Library's sense.** The restriction
`f : S_C → S` is a surjective homomorphism of tori. Because `i` is a
monomorphism, its scheme-theoretic kernel is the inverse image of `ker π`
under `i_C`. This is a closed subscheme of the finite `k`-scheme `ker π`,
so it is finite. It is central because `S_C` is commutative. Tori
are reductive groups. Conrad, *Reductive group schemes* (2014), Proposition
3.3.10, PDF p.103, says that a surjective homomorphism of reductive groups
over a scheme is a central isogeny exactly when its fibres have finite
central kernel. That source's Definition 3.3.9, on the same page, defines a
central isogeny as a finite flat surjection with central kernel. Over a
field, `S_C` and `S` are of finite type, so `f` is also locally of finite
presentation, as the Lean predicate makes explicit.

**Arbitrary-field scope.** The Borel–Tits theorem is stated for an
arbitrary field. No hypothesis from a valued-field application is imported.

**Application.** Kaletha and Prasad, *Bruhat–Tits theory: a new approach*
(2023), proof of Lemma 2.6.29, printed p.106 (PDF p.137), uses the
maximal torus `S_sc` in the preimage of `S` in `G_sc`, mapping by an
isogeny onto the derived torus. Their 2024 corrections, PDF p.25, insert
before Definition 2.6.20 that `k` is Henselian with perfect residue field.
That restriction concerns their valued-field application and is not
imported here. The derived-subgroup version of this statement is the
separate module
[`SimplyConnected.DerivedCoverSplitTorusStatement`](DerivedCoverSplitTorusStatement.md).

No retained errata for the two Borel–Tits articles were found other than
the 1972 article's own corrections to the 1965 article (§1.2 and §5,
printed pp.253–254 and 274–275). Those corrections do not concern
Théorème 2.20 or the cited 1965 propositions. No project errata note for
Conrad's notes was found.
