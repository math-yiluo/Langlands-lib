# Renard’s actual categorical induction adjunctions

This module states the canonical additive categorical adjunctions `F ⊣ I` and
`P ⊣ pseudoF` on the actual published categories of nondegenerate original
modules. Its namespace is
`Langlands.Algebra.NondegenerateInductionAdjunction`. The principal declarations
are proposition definitions, with the actual adjunctions and their canonical
additive Hom correspondences existentially quantified in their conclusions.
They are unproved theorem targets. The implemented helper laws only package
evaluation, intrinsic balancing, the published quotient lift, and additive
composition on actual morphisms.

## Original source and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source conventions at printed pp.5–7 / PDF pp.11–13 allow nonunital rings
and actions without a unit law, and define nondegeneracy by fixation of each
vector by an idempotent. I.2.1–I.2.2, printed pp.14–16 / PDF pp.20–22,
explain complex coefficients, unitization, and the nondegenerate tensor-Hom
corollary. All of I.2.3, printed pp.16–18 / PDF pp.22–24, was consulted.
Its formulas (I.2.3.1–2), induction definitions, and the unnumbered theorem on
printed p.18 / PDF p.24 supply the handed functors and adjunction directions.

Renard displays the first natural Hom equivalence from
`Hom_B(N, I M)` to `Hom_A(F N, M)`. The present additive refinement uses its
inverse, from `Hom_A(F N, M)` to `Hom_B(N, I M)`, to agree with the standard
left-adjoint convention for `CategoryTheory.Adjunction.homEquiv`. The second
source equivalence already has that convention for `P ⊣ pseudoF`. Renard deduces
both from the nondegenerate tensor-Hom corollary of I.2.2, in particular its
left-module formula (I.2.2.6). The present targets retain the corresponding
curry formula and specify the entire inverse quotient lift explicitly.

The registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pp.1–2 and 18–19. Its first page corrects the 2010 printed
adjunction theorem to exactly these two directions; this correction is already
incorporated in the governing 2026 edition. Its printed-page-299 correction on
PDF p.18 agrees with the precomposition and postcomposition used in the
naturality statements below. The separate warning concerning a degenerate
corner action and the later complex-vector-space/unitization correction do
not supply omitted hypotheses or comparison results here. The author’s book
section checked on 1 November 2026 links the corrected 2026 French edition and
separately labels the 2010 errata; no separate 2026 errata link occurs in that
bounded section. The registered snapshot `renard-author-book-links-2026-10-31`
records those links.

This is a derived internal arbitrary-ring additive formulation. Renard’s
I.2 discussion works with complex algebras and coefficient or unitized models.
Here the tensor is the published quotient of the integer tensor product and
Hom means the published original additive intertwiners. An additive Hom
equivalence by itself proves neither complex-linearity nor agreement with a
coefficient-linear or unitized construction. Those bridges are separate.

## Data, universes, and actual functors

Let `A : Type uA` and `B : Type uB` have their specified `NonUnitalRing`
structures, with `hA : IsIdempotented A` and `hB : IsIdempotented B`. The two
families are independent. The F family supplies only a left A-action on B;
it explicitly selects `NonUnitalModule.rightRegular B` as the right B-action.
Its `hAB : ActionsCommute A B B` and
`hnd : IsNondegenerateBimodule A B B` refer to exactly those actions.
The P family supplies only a right A-action on B, written as an original
left action of `Aᵐᵒᵖ`; it explicitly selects
`NonUnitalModule.regular B` as the left B-action. Its `hBA` and `hnd` refer
to exactly those B–A actions. Each family retains its own source two-sided
nondegeneracy assumption. The unrelated supplied actions need not coexist,
and no ring homomorphism `A → B` is assumed.

For arbitrary independent `uA`, `uB`, and `v`, all variable module carriers
are in `Type w`, where `w = max uB v`. The actual tensor and Hom functors
output carriers in `Type (max uB w)`, definitionally the same `Type w`.
Thus they compose on the stated categories without a change of carrier.
The ring universe `uA` remains independent and may be strictly larger than w.
There is no smallness hypothesis or replacement by a functor on lifted
carriers. The independent-universe general unbundled tensor-Hom family is
outside this unit.

The left functor in `CanonicalFInductionAdjunction` is precisely
`NondegenerateTensorFunctor.F hA hAB hnd`, specialized to carrier universe w
and the selected right regular action. Its object at N has carrier
`NonUnitalModuleTensor.Tensor B B N.obj`, the published tensor additive group,
and the published residual A-action. Its right adjoint is precisely
`RenardHomFunctors.I hAB hB`. Its object at M is the B-nondegenerate part of
the actual `NonUnitalModuleHom A B M.obj` under source precomposition:

```text
(b • h)(b′) = h(b′ * b).
```

The left functor in `CanonicalPInductionAdjunction` is precisely
`NondegenerateTensorFunctor.P hB hBA hnd`, with carrier
`NonUnitalModuleTensor.Tensor A B M.obj` and the published residual action of
B using its selected regular action. Its right adjoint is precisely
`RenardHomFunctors.pseudoF hBA hA`. This takes the A-nondegenerate part of
`NonUnitalModuleHom B B N.obj`, under the original action

```text
(a • h)(b) = h(op a • b).
```

In particular the part in `pseudoF` is taken for A. Every Hom part has the
actual subtype additive group and restricted source-precomposition action.
Its `.val` is the published part inclusion, exposed categorically by
`RenardHomFunctors.inductionInclusion` or `pseudoInclusion`. The ambient Hom
need not be nondegenerate. The tensor maps are exactly the fixed-first-factor
maps `id_B ⊗ f` of the published functors, and the Hom maps are their published
restricted original postcomposition maps. The predicates reuse the complete
functors, hence all these original carrier, group, action, and morphism choices.

## Intrinsic inverse quotient lifts

For an actual `g : N ⟶ I.obj M`, `fEvaluationPairing` is the biadditive map

```text
(b,n) ↦ (g.hom n).val b.
```

Its balancing is proved in `fEvaluationPairing_balanced` from g’s original
B-linearity and the displayed source-precomposition action: evaluating
`g(c • n) = c • g(n)` at b gives equality of the two values at `(b*c,n)` and
`(b,c • n)`. The values of g already belong to the actual Hom part, so no
ambient-Hom nondegeneracy certificate is an input.

`fUncurry` applies the existing `NonUnitalBimoduleTensor.leftLift` to this
pairing, proves the residual A-linearity by the A-linearity of each value of g,
and wraps this original map as a morphism in the full subcategory. Its whole
underlying additive map is definitionally
`NonUnitalModuleTensor.lift B` of the pairing and the intrinsic balancing proof;
`fUncurry_toAddMonoidHom` records that equality. `fUncurryAddHom` packages
uncurrying as an additive map on the actual Hom groups. Its zero and addition
laws use the published tensor-generator extensionality.

Independently, `pEvaluationPairing` evaluates `g : M ⟶ pseudoF.obj N` at
`(b,m)`. `pEvaluationPairing_balanced` evaluates g’s original A-linearity and
the supplied right A-action on B, giving equality at `(op a • b,m)` and
`(b,a • m)`. Each value is a B-intertwiner for the selected regular source
action. `pUncurry` therefore reuses `leftLift` with residual B-linearity, and
`pUncurry_toAddMonoidHom` identifies its entire additive map with the published
`NonUnitalModuleTensor.lift A`. `pUncurryAddHom` proves and packages additivity
by the same generator-extensionality argument.

These helpers construct only the prescribed inverse-lift maps. They construct
no Hom equivalence and prove neither principal adjunction target.

## Canonical predicates and closed targets

`CanonicalFInductionAdjunction hA hB hAB hnd` concludes the existence of
an actual `adj : F ⊣ I` and a family of additive equivalences

```text
E(N,M) : (F.obj N ⟶ M) ≃+ (N ⟶ I.obj M).
```

`CanonicalPInductionAdjunction hA hB hBA hnd` separately concludes
`adj : P ⊣ pseudoF` with

```text
E(M,N) : (P.obj M ⟶ N) ≃+ (M ⟶ pseudoF.obj N).
```

For both, `AdditiveAdjunctionCoherence` requires equality of `E.toEquiv` with
that very adjunction’s `homEquiv`, at every pair of objects. Its adjunction and
E parameters are existential conclusions of the canonical predicates. They
are never premises of the closed targets.

The F curry formula, after actual part inclusion, is
`(E(N,M) f)(n).val(b) = f(tmul B B N.obj b n)`. The P formula is
`(E(M,N) f)(m).val(b) = f(tmul A B M.obj b m)`. Their Lean expressions use
the corresponding evaluation helpers and the original morphism’s entire
underlying additive map. Each inverse is identified as a whole additive map
on Hom groups with `fUncurryAddHom` or `pUncurryAddHom`. The predicates also
explicitly identify each inverse value’s entire underlying additive map with
the appropriate published `lift`, state its pure-tensor evaluation formula,
and require both composites of currying and the specified uncurry additive
map to equal `AddMonoidHom.id`. Thus neither an unspecified inverse nor only
its values on individual pure tensors can satisfy the interface.

The unit and counit belong to the same existential adjunction. Their required
formulas are, respectively,

```text
F-I:       ((unit.app N) n).val b = tmul B B N.obj b n,
           (counit.app M) (tmul B B (I.obj M).obj b h) = h.val b;
P-pseudoF: ((unit.app M) m).val b = tmul A B M.obj b m,
           (counit.app N) (tmul A B (pseudoF.obj N).obj b h) = h.val b.
```

The Lean formulas pass through the actual full-subcategory wrappers and part
inclusions. Their types retain the required original linearity and intrinsic
subtype membership. `AdditiveAdjunctionCoherence` additionally requires both
triangle identities as equalities of complete categorical morphisms:
`L.map (unit.app X) ≫ counit.app (L.obj X) = 𝟙 _` and
`unit.app (R.obj Y) ≫ R.map (counit.app Y) = 𝟙 _`.

`NondegenerateFInductionAdjunctionTheorem` and
`NondegeneratePInductionAdjunctionTheorem` are two closed Prop-valued targets,
universally quantifying all data of their respective handed families, including
the specified ring structures and original supplied action. No adjunction,
equivalence, bijectivity, or curry/uncurry certificate is assumed.

## Whole-map naturality

`compositionMap l r` is the canonical additive map `f ↦ l ≫ f ≫ r` on
actual categorical Hom groups. For arbitrary `s : X′ ⟶ X` and `t : Y ⟶ Y′`,
write `H_L = compositionMap (L.map s) t` and
`H_R = compositionMap s (R.map t)`. These are Hom-space composition maps;
they are unrelated to the induction functor named P. The common coherence
predicate requires both equalities of entire additive maps:

```text
E(X′,Y′).toAddMonoidHom.comp H_L = H_R.comp E(X,Y).toAddMonoidHom,
E(X′,Y′).symm.toAddMonoidHom.comp H_R = H_L.comp E(X,Y).symm.toAddMonoidHom.
```

The functor maps occurring here are exactly the actual tensor and restricted
postcomposition maps already fixed above. Both source and target morphisms
vary simultaneously. The same predicate records whole-morphism naturality
of the actual unit and counit:

```text
s ≫ unit.app X′ = unit.app X ≫ R.map (L.map s),
L.map (R.map t) ≫ counit.app Y′ = counit.app Y ≫ t.
```

These obligations fix the canonical correspondence and its categorical
coherence; a dimension equality or existence of some adjoint cannot replace
them.

The companion interface-check pair records complete unapplied declaration and
exact-unfolding checks, the actual functor and original-structure choices,
independent universe assignments, competing structures on common carriers,
and regular-integer and subsingleton boundary interfaces. Such checks establish
that the targets express the intended data; they assume no proof of either
closed target. Zero rings and trivial nondegenerate modules are allowed. A
zero action on a nonzero module is not asserted to be nondegenerate.

A later exact-target proof must establish the two closed propositions, possibly
using a published nondegenerate tensor-Hom refinement. The general tensor-Hom
equivalences, complex coefficient and unitization bridges, completion and
regular-Hom comparisons, equality of the A- and B-Hom parts, scalar restriction,
I.2.4 exactness and preservation of injectives remain separate obligations.
This statement unit does not complete I.2.3 or the whole book.
