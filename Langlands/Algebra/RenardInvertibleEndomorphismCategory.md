# Local polynomial modules and invertible endomorphisms

Author: Worker 1581.

The namespace `Langlands.Renard.EndomorphismLocalization` constructs the actual
restriction of the published polynomial-module equivalence:

```lean
localEquivalence.{u, v} (R : Type u) [CommRing R] :
  Langlands.Renard.ModuleLocalization.LocalModuleCat.{u, v} (powersX R) ≌
    InvertibleEndomorphismCat.{u, v} R

fieldLocalEquivalence.{u, v} (k : Type u) [Field k] :
  Langlands.Renard.ModuleLocalization.LocalModuleCat.{u, v} (powersX k) ≌
    InvertibleEndomorphismCat.{u, v} k
```

Here `powersX R` is the existing `Submonoid.powers (Polynomial.X : R[X])`.
Write `P` for the existing namespace
`Langlands.Algebra.PolynomialEndomorphism` and `L` for
`Langlands.Renard.ModuleLocalization` in the explanations below.
These abbreviations are explanatory notation.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, Appendix A.III.1, examples 4–5, printed p.252 / one-based
PDF258. The right universal problem is defined on printed p.251 / PDF257.
The registered literature identifier is
`renard-2026-representations-groupes-reductifs-padiques`, with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The author read PDF257–258 and visually inspected PDF258.

Example 4 selects modules on which every denominator acts invertibly.
Example 5 identifies unital polynomial modules over a field with vector spaces
equipped with an endomorphism and linear intertwiners, and explicitly
translates localization at the powers of `X` through that equivalence.
`fieldLocalEquivalence` constructs the restriction to the selected objects
needed for this translation. The commutative-ring generalization, independent
Lean universes, exact full-subcategory representation, and explicit coherence
and comparison laws are derived implementation content.

The construction uses the corrected invertible-endomorphism meaning of
`L.IsSLocal`. The false scalar-inverse parenthesis in source example 4 is not
an assumption: the published integer/rational counterexample in
`Langlands.Algebra.RenardModuleLocalization` records its failure.

## The actual categories and locality laws

`invertibleEndomorphismProperty R` is exactly the object property
`fun A => IsUnit (P.endomorphism R A)` on `P.EndomorphismCat.{u,v} R`.
`InvertibleEndomorphismCat R` is its `ObjectProperty.FullSubcategory`.
Consequently its morphisms are all the existing ambient linear intertwiners
between its selected pairs. If `f : A ⟶ B` is a morphism of this full
subcategory, `f.hom` is the ambient intertwiner and `f.hom.f` is its
underlying module morphism. No further condition is imposed on morphisms.

`invertibleEndomorphismInclusion R` is the actual `ObjectProperty.ι`.
`invertibleEndomorphismInclusionFullyFaithful R` supplies its fully faithful
structure; the preimage wraps the same ambient intertwiner.
The polynomial side is exactly the existing
`L.LocalModuleCat.{u,v} (powersX R)`, with its published inclusion into
`ModuleCat.{v} R[X]` and all actual polynomial-linear maps.

`isSLocal_iff_isUnit_fromPolynomial R M` proves, for every actual polynomial
module `M`,

```text
L.IsSLocal (powersX R) M
  ↔ IsUnit (P.endomorphism R ((P.fromPolynomial R).obj M)).
```

The implemented proof uses `L.isSLocal_iff_bijective` and
`Module.End.isUnit_iff`. Locality implies bijectivity of the `X` action by
taking the denominator `X`. Conversely, every denominator is `X ^ n`.
Multiplication by `X ^ 0` is the identity, and multiplication by `X ^ (n+1)`
is the composite of multiplication by `X` and by `X ^ n`.
Induction and composition of bijections prove locality. This works for the
original polynomial action on `M`, without an evaluation-module replacement.

`evalModule_isSLocal_iff R a` proves
`L.IsSLocal (powersX R) (EvalModule a) ↔ IsUnit a` for an arbitrary actual
linear endomorphism `a`. The forward implication takes the bijective `X`
action and conjugates it by the carrier identification `Module.AEval'.of a`.
The identity `X • Module.AEval'.of a x = Module.AEval'.of a (a x)` shows that
the conjugate is precisely `a`. The reverse implication is the published
`evalModule_isSLocal`.
`toPolynomial_isSLocal_iff R A` specializes this exact law to the actual
evaluation object of the existing functor:

```text
L.IsSLocal (powersX R) ((P.toPolynomial R).obj A)
  ↔ IsUnit (P.endomorphism R A).
```

These are proved intrinsic selection laws, not locality certificates supplied
as additional premises.

## Restricted functors and inclusion comparisons

`localFromPolynomial R` is `ObjectProperty.lift` of
`L.localModuleInclusion (powersX R) ⋙ P.fromPolynomial R`.
Its underlying object at `M` is exactly
`(P.fromPolynomial R).obj M.obj`: restriction along constant polynomials,
with the actual original multiplication by `X` as the specified operator.
The first locality law supplies its object-property proof.

`localToPolynomial R` is `ObjectProperty.lift` of
`invertibleEndomorphismInclusion R ⋙ P.toPolynomial R`.
At `A` its underlying polynomial module is exactly
`Module.AEval' (P.endomorphism R A.obj)`, with the existing evaluation action.
The second locality law supplies its object-property proof.
Both functors inherit their identity and composition laws from the actual
ambient functors via `ObjectProperty.lift`.

`localFromPolynomial_comp_inclusion` and
`localToPolynomial_comp_inclusion` prove the two functor equalities

```text
localFromPolynomial R ⋙ invertibleEndomorphismInclusion R
  = L.localModuleInclusion (powersX R) ⋙ P.fromPolynomial R

localToPolynomial R ⋙ L.localModuleInclusion (powersX R)
  = invertibleEndomorphismInclusion R ⋙ P.toPolynomial R.
```

Both proofs are `rfl`, so these comparisons require no additional carrier
isomorphisms.
`localFromPolynomial_map_hom` and `localToPolynomial_map_hom` identify the
underlying maps with the corresponding ambient functor maps.
The concrete formulas are exposed by `localFromPolynomial_map_apply` and
`localToPolynomial_map_of`:

```text
((localFromPolynomial R).map f).hom.f x = f.hom x

((localToPolynomial R).map f).hom (Module.AEval'.of a x)
  = Module.AEval'.of b (f.hom.f x),
```

where `a = P.endomorphism R A.obj` and `b = P.endomorphism R B.obj`
in the second formula. Each formula is definitional equality. In particular
the inverse uses the existing polynomial-linear map associated to the
original intertwiner.

## Unit, counit and coherence

`localUnitIso R` has type
`𝟭 _ ≅ localFromPolynomial R ⋙ localToPolynomial R`.
Its component at a local module `M` is `ObjectProperty.isoMk` applied to
`(P.equivalence R).unitIso.app M.obj`.
`localCounitIso R` has type
`localToPolynomial R ⋙ localFromPolynomial R ≅ 𝟭 _`.
Its component at an invertible pair `A` is the analogous lift of
`(P.equivalence R).counitIso.app A.obj`.

The underlying functions of the unit and its inverse are
`Module.AEval'.of (P.xAction R M.obj).hom` and its inverse.
The counit's underlying functions are
`(Module.AEval'.of (P.endomorphism R A.obj)).symm` and its inverse.
These are the existing carrier identifications from the published equivalence.
The component comparisons `localUnitIso_app_inclusion` and
`localCounitIso_app_inclusion` assert that applying the respective inclusion's
`mapIso` recovers exactly the ambient unit and counit components; both are
proved by `rfl`. The functor equalities above identify their sources and
targets under the inclusions.

`NatIso.ofComponents` packages the restricted natural isomorphisms.
Naturality is proved by `ObjectProperty.hom_ext` applied to the existing
unit or counit naturality equation at `f.hom`.
`localEquivalence R` uses exactly these two functors and natural isomorphisms.
Its required `functor_unitIso_comp` coherence is
`ObjectProperty.hom_ext` of `(P.equivalence R).functor_unit_comp M.obj`.
Thus the coherence comes from the actual ambient equivalence; it is not an
additional hypothesis. The locality laws, map formulas, naturality and
coherence are intrinsic laws of these definitions.

## Scope and universes

The coefficient ring lies in `Type u`, and every module carrier lies in the
independent `Type v`. All declarations, including
`fieldLocalEquivalence.{u,v}`, retain these two independent levels. The
coefficient ring may be the zero ring, and zero modules are included.
There are no finite-dimension, finite-generation, nontriviality, faithful-action,
domain, characteristic, algebraic-closure or smallness assumptions.

Both categories use the same arbitrary carrier universe `v`. This equivalence
does not construct a localization in `Type v`; the existing actual
localizations may require a larger carrier universe.
The full subcategory selects invertible operators only and imposes no
invertibility assumption on arbitrary source pairs in later localization
problems.

This unit does not compare the chosen lifted localization arrows, prove their
factorization, uniqueness or initiality, or construct a chosen localization
functor or adjunction. Those are successor obligations. The scalar universal
property, B-module localization and PDF259 kernel and quotient results remain
separate published interfaces and are not repeated here.
