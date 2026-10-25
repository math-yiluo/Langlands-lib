# Finite-group quotient cocone obligations

This module states three propositions about the actual category of finite étale
covers. It imports `Langlands.AlgebraicGeometry.FiniteEtale.Definitions` and
proves none of the quotient existence assertions. All declarations are in
`Langlands.AlgebraicGeometry.FiniteEtale`, with an arbitrary universe `u`.

## Source and derived formulation

The source is Grothendieck et al., *Revêtements étales et groupe fondamental*
(SGA 1), Exposé V, recomposed annotated edition, arXiv math/0206203v2:

- Proposition 1.1(ii)–(iv) and Corollary 1.2, printed p.88 (PDF p.104), describe
  the invariant spectrum, its orbit fibres and residue-field automorphisms,
  its categorical quotient property, and localization of invariants.
- Proposition 1.8 and its proof, printed p.90 (PDF p.106), construct the quotient
  by gluing the quotients of invariant affine opens. Corollary 1.4, printed p.89
  (PDF p.105), identifies restrictions to quotient opens.
- Proposition 3.1 and Corollary 3.4, printed pp.96–97 (PDF pp.112–113), give the
  étale and finite étale properties of the quotient over a locally noetherian
  base. Local noetherianity is retained from that context.

The registered source is `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`, retained as
`literature/Grothendieck et al. - SGA 1, Revetements etales et groupe fondamental (recomposed edition, arXiv math-0206203v2).pdf`.
No source-specific project errata note was present when these passages were
checked.

These statements are derived categorical formulations designed for the Library's
finite étale quotient construction; they are not verbatim formulas in SGA 1.
The source's quotient universal property gives a colimit of the group-action
diagram. Because all action maps lie over the base, the quotient acquires a
structural map to that base. The universal property then restricts to the slice
category. Corollary 3.4 places its vertex in the full subcategory `Cover S`, so
it gives the corresponding colimit there.

Proposition 1.1(ii) concerns underlying topological points. Its combination with
(iii) supplies the stronger assertion about points valued in any algebraically
closed field: integrality gives a point above a given quotient point, algebraic
residue-field extensions embed into the algebraically closed field, and the
stabilizer surjects onto the residue-field automorphism group. The resulting
lifts form exactly one group orbit. This explains both surjectivity and the
orbit equivalence in the predicate below; topological orbit fibres alone would
not express the required geometric-point assertion.

For a finite étale cover `X → S`, finiteness implies that the morphism is affine.
Thus the inverse image of each affine open of `S` is affine. Every action map is
an automorphism over `S`, so each such inverse image is invariant under the
group; these inverse images cover `X`. Over an affine base, `X` is itself affine,
and the candidate quotient is the spectrum of its invariant ring. Over a
general base, the invariant affine charts satisfy Proposition 1.8. Localization
of invariants from Corollary 1.2 and restriction of quotients from Corollary 1.4
provide the compatibility used to glue their quotients, even when intersections
of the original affine opens are not affine. This argument requires neither
connectedness nor a separatedness assumption on the base. The statements record
the resulting existence obligations; this module does not implement that
construction or its proof.

## Exact predicate

`FiniteGroupQuotientCocone` has parameters

```lean
{S : Scheme.{u}} {G : Type u} [Group G]
(D : SingleObj G ⥤ Cover S) (c : Cocone D)
```

and returns `Prop`. It is the conjunction of `Nonempty (IsColimit c)` and the
following assertion for every `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and
`s : Spec (.of Ω) ⟶ S`. Write

```lean
q := (pointFunctor s).map (c.ι.app (SingleObj.star G))
```

Then `q` is surjective, and for every
`x y : Fiber s (D.obj (SingleObj.star G))`,

```lean
q x = q y ↔ ∃ g : G,
  y = (pointFunctor s).map (D.map (SingleObj.toEnd G g)) x
```

The codomain of `q` is the actual geometric fibre `Fiber s c.pt`. Here `Fiber`
is the set of lifts of `s` in the slice of schemes, and `pointFunctor` acts by
postcomposition. A cocone is an invariant morphism from the diagram's sole
object into a cover; `Nonempty (IsColimit c)` asserts its universal property in
`Cover S`. It does not select a colimit witness as extra data.

The action uses the existing `SingleObj.toEnd G` convention explicitly.
Mathlib composes the endomorphisms corresponding to `g` and `h` as `h * g`;
the functor therefore gives the usual left action on geometric points.
Changing between the source's left and right conventions by inversion leaves
the orbit relation unchanged. No new action or replacement point functor is
introduced here.

Despite its name, this predicate does not assume `Finite G`, local
noetherianity, or affineness: those are hypotheses of the existence statements.

## Existence statements and scope

`AffineFiniteGroupQuotientCocones.{u} : Prop` quantifies over every
`S : Scheme.{u}` with `[IsAffine S]` and `[IsLocallyNoetherian S]`, every
`G : Type u` with `[Group G]` and `[Finite G]`, and every
`D : SingleObj G ⥤ Cover S`. It asserts

```lean
∃ c : Cocone D, FiniteGroupQuotientCocone D c
```

`FiniteGroupQuotientCocones.{u} : Prop` has the same quantifiers and conclusion,
with only `[IsLocallyNoetherian S]` required of the base. It omits `[IsAffine S]`.
Both definitions retain `u` through these quantified types, although neither
has explicit arguments outside its proposition body.

Neither existence statement assumes `ConnectedSpace S`, finite packaging of
fibres (`hfin`), a Galois-category structure, a free or faithful group action, or
invertibility of the group order. Every geometric point in the fixed arbitrary
universe is covered by the conclusion. The orbit description is intended to
support a subsequent proof of preservation by the actual point functor and its
finite-set packaging. No preservation theorem or geometric Galois-category
instance is asserted or installed here. The affine and global existence proofs,
and their categorical assembly, remain separate obligations.
