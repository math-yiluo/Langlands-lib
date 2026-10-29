# Pullback preservation of smooth-family algebraic triviality

`Langlands.AbelianScheme.SmoothFamilyPullbackStatement` is a proposition
definition with a single universe parameter `u`. It quantifies over every
scheme `S : Scheme.{u}`, abelian scheme `A : AbelianScheme S`, two objects
`T U : Over S`, slice morphism `h : T ⟶ U`, and actual rigidified line
bundle `L : RigidifiedFamily A U`. It asserts that
`IsAlgebraicallyTrivialFamilyViaSmoothFamily A L` implies the same predicate
for the actual relative rigidified pullback

```
(RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
  (unitSection_comp A) h).obj L : RigidifiedFamily A T.
```

The module contains only this definition. It proves nothing and adds no
axiom.

## The objects in the type

All objects and predicates are already published; this module defines no
new mathematical notion.

- `RigidifiedFamily A U`, from `RelativePicardZero`, is the existing
  category of rigidified line bundles on `U ×_S A`, the total space
  `(relativeSpace A.X.hom).obj U` with the parameter first. The
  rigidification is along the section induced by `unitSection A`.
- `RigidifiedLineBundle.relativePullback`, from `RigidifiedLineBundle`, is
  the existing functor `RigidifiedFamily A U ⥤ RigidifiedFamily A T`.
  It pulls back along `(relativeSpace A.X.hom).map h : T ×_S A ⟶ U ×_S A`
  over `h.left`. The commuting square is the naturality of the induced
  relative section. The new rigidification is the canonical one from the
  structure-sheaf pullback comparison. After forgetting the rigidification,
  its underlying bundle is the ordinary `LineBundle.pullback` along
  `(relativeSpace A.X.hom).map h`, by the existing `pullbackForgetIso`,
  which is `Iso.refl`.
- `IsAlgebraicallyTrivialFamilyViaSmoothFamily`, from
  `SmoothFamilyAlgebraicTriviality`, applies the geometric-fibre predicate
  `IsFibrewiseAlgebraicallyTrivialViaSmoothFamily` to the base change
  `(baseChange T.hom).obj A` and to `familyLineBundle A L`. That bundle
  forgets the rigidification and pulls back along
  `(relativeSpaceSymmetry A.X.hom T).inv : A ×_S T ⟶ T ×_S A`.
  For every algebraically closed field `K : Type u` and every scheme map
  `s : Spec K ⟶ T.left`, the fibre restriction `fibreLineBundle` must
  satisfy `IsAlgebraicallyTrivialViaSmoothFamily`. That field predicate
  asks for an actual parameter `C` over `Spec K` that is smooth,
  separated, locally of finite type, quasi-compact and geometrically
  integral. It also asks for two rational points `c0, c1` and an actual
  line bundle on `C ×_K A_s` whose restrictions along
  `smoothFamilyPointMap` are isomorphic to the trivial bundle and to the
  given fibre bundle, respectively.

So the hypothesis tests every geometric point of `U.left`. The conclusion
tests every geometric point of `T.left` for the actual pulled-back family,
with its existing canonical pulled-back rigidification. The conclusion is
not existence of some other family, a bijection of geometric points, a
quotient of ordinary line bundles, or a translation-invariance condition.
The rigidification plays no role in the predicate, which forgets it, but
the statement concerns the rigidified object produced by the actual functor.

## Generality

The morphism `h` is arbitrary. There is no smoothness, flatness,
surjectivity or finiteness hypothesis on `h.left`. There is no
quasi-separatedness, noetherian, reducedness or finiteness hypothesis on
`S`, `T.left` or `U.left`, so the test schemes may be nonreduced or
non-quasi-separated. The only geometric hypotheses are those built into
`AbelianScheme S`. No comparison, coherence, representability or dual
hypothesis appears. Each smooth-family witness in the conclusion may depend
on the field `K` and the point `s`, as in the governing predicate.

## Intended proof (not supplied here)

The intended proof is elementary functoriality. It is recorded only to
motivate the statement and is not proved by this module.

Fix a geometric point `s : Spec K ⟶ T.left` and use the composite
`s ≫ h.left` as a geometric point of `U.left`. The hypothesis gives a
parameter `C`, points `c0, c1` and a bundle `N` on the fibre product
`C ×_K` (the fibre of `A_U` over `s ≫ h.left`). The existing
`Langlands.GroupScheme.fibreComparison A.toGrp h s` constructs a
homomorphism from the fibre of `A_T` at `s` to that fibre of `A_U`.
The published `picardZeroPullback` proof already passes it, with
`fibreComparison_fst`, to `fibreComparison_lineBundleIso`. The projection
lemmas `fibreComparison_fst` and `fibreComparison_snd` give the
compatibility with the maps to `A` and to `Spec K`. `fibreComparison` is only a homomorphism;
a proof should not assume an inverse that the module does not construct,
and a direct commuting-square argument is equally acceptable.

Pull `N` back along the induced map of products `C ×_K (fibre at s) ⟶
C ×_K (fibre at s ≫ h.left)`, keeping the same `C`, `c0` and `c1`. The
restrictions at `c0` and `c1` are pullbacks of the old endpoint
restrictions along the fibre map. The trivial-bundle pullback comparison
and the existing ordinary isomorphism
`Langlands.AbelianScheme.fibreComparison_lineBundleIso`, from
`PicardZeroPullbackComparison`, then identify them with the trivial bundle
and with the fibre restriction of `familyLineBundle` of the actual relative
pullback. That isomorphism is ordinary line-bundle pullback infrastructure.
It needs no translation-invariance hypothesis, although the same module
also contains translation-invariance lemmas, which are not needed here.

No comparison with divisor algebraic equivalence, Picard components,
translation invariance or the geometric Picard-zero predicate is needed or
authorized for this proof. The translation-invariance analogue
`PicardZeroPullbackStatement`, and its published proof
`picardZeroPullback`, concern a different predicate. They are not a proof
of this statement, and the comparison between the two predicates is a
separate, paused obligation.

## Provenance

This is a derived internal compatibility target, not a verbatim literature
result. The governing smooth-family predicate and its sources are recorded
in `SmoothFamilyAlgebraicTriviality.md`. The original is Edixhoven, van der
Geer and Moonen, *Abelian Varieties*, preliminary version of the first
chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Remark (6.9), printed p.91 (PDF p.95), defines algebraic equivalence of
divisors through a smooth parameter variety `T` with two rational points.
The cited passage states no pullback-stability result for families. The
present target says that the derived line-bundle-family predicate is stable
under base change of the family's parameter scheme. Its rationale is the
fibre-by-fibre argument above.
No errata note for this source was found in the Library `notes/errata/`.

The statement design was proposed by Worker 442 while working on the
flatness proof task `faa0d019-2eb8-446f-8fa3-de9ef52e340a`.

## Consumers and remaining obligations

The intended consumer is the actual-family comparison of universal
smooth-family parameters, task `b0d652f3-90b7-40af-8df7-4dc15ce7e599`, whose
prototype takes exactly this proposition as a hypothesis. That comparison
feeds the flatness and finite-presentation proofs and the shared
representer route. Quotient induction will give the class-level version for
`IsAlgebraicallyTrivialClassViaSmoothFamily` once this statement is proved.
The proof of this proposition belongs to a separate exact-target proof task.
This module constructs no representer and compares no parameters. It does
not compare algebraic-equivalence definitions, smooth-family triviality
with translation invariance, or open loci. It provides no
rigidification-normalization, descent or gluing.
