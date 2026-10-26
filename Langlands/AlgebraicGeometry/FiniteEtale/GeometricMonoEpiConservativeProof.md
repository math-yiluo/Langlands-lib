# Mono complements, epimorphism preservation and conservativity of the geometric fibre

`Langlands.AlgebraicGeometry.FiniteEtale.geometricMonoEpiConservative` proves exactly the
published proposition `GeometricMonoEpiConservative s hfin` from
`Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements`. It retains the statement's
complete parameter list, in this order:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S)
(hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

The target is the right-associated conjunction of three assertions about the published
category `Cover S` of finite étale covers of `S` and the published geometric fibre functor
`fiberFunctor s hfin : Cover S ⥤ FintypeCat`:

1. every monomorphism `i : X ⟶ Y` of covers is the first inclusion of a binary coproduct
   cocone `BinaryCofan.mk i v` with vertex `Y`, for some cover `Z` and `v : Z ⟶ Y`;
2. `fiberFunctor s hfin` preserves epimorphisms;
3. `fiberFunctor s hfin` reflects isomorphisms.

The statement pair and its imports are unchanged. The module adds no instances, no
hypotheses and no assumption of a Galois category, a pre-Galois category, a fibre-functor
structure or a continuous-action equivalence.

## Implemented proof

The proof unfolds `GeometricMonoEpiConservative` and supplies the three conjuncts from the
accepted, published component theorems. Each component theorem has the same parameter list
and proves one of the three separate propositions of
`Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements`, whose bodies are
literally the three conjuncts above:

- `geometricMonomorphismComplements s hfin : GeometricMonomorphismComplements s hfin`, from
  module `Langlands.AlgebraicGeometry.FiniteEtale.GeometricMonomorphismComplementsProof`.
  The underlying scheme morphism of a monomorphism of covers is finite étale and a
  monomorphism, hence both a closed and an open immersion. The open subscheme on the
  complement of its clopen image is also a closed immersion, hence a finite étale cover.
  The two inclusions form a coproduct cocone of schemes, and this colimit is reflected back
  into `Cover S`.
- `geometricEpimorphismPreservation s hfin : GeometricEpimorphismPreservation s hfin`, from
  module `Langlands.AlgebraicGeometry.FiniteEtale.GeometricEpimorphismPreservationProof`.
  An epimorphism of covers is surjective on underlying points; it is tested against two
  maps into `Y ⨿ Y` that agree exactly on the clopen image. A geometric point of the
  target then lifts through a closed point of the fibre over the algebraically closed
  field `Ω`.
- `geometricFiberConservative s hfin : GeometricFiberConservative s hfin`, from module
  `Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberConservativeProof`. Surjectivity
  on the fibre at `s` makes the underlying finite étale morphism surjective: the image in
  the connected base of the missed locus is clopen and avoids the point of `s`. Injectivity
  on the fibre makes the diagonal surjective by the same argument. Both steps then use
  Mathlib's `Flat.isIso_of_surjective_of_mono`: a flat, quasi-compact, surjective
  monomorphism of schemes is an isomorphism. The diagonal of the étale morphism is an open
  immersion, hence a flat monomorphism; it is quasi-compact because finite morphisms are
  separated. So the diagonal is an isomorphism and the morphism is a monomorphism. The
  morphism itself is étale, hence flat, and finite, hence quasi-compact, so it is an
  isomorphism of schemes. Finally `Over.forget S` and the inclusion `Cover S ⥤ Over S`
  reflect isomorphisms.

The component Markdown files document these proofs in full. The assembly itself uses only
the definitional unfolding of `GeometricMonoEpiConservative` and the anonymous constructor
for `∧`. Lean reports the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Provenance

This is an internal assembly of accepted component proofs. The target is a derived axiom
formulation whose three conjuncts correspond to `PreGaloisCategory.monoInducesIsoOnDirectSummand`,
`FiberFunctor.preservesEpis` and `FiberFunctor.reflectsIsos` in
`Mathlib.CategoryTheory.Galois.Basic` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`); those classes are not hypotheses here. The
geometric context is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 (PDF p.154), and Theorem
(10.28), printed p.151 (PDF p.155); registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The source does not
state these three properties verbatim, and this module does not prove the classification of
Theorem (10.28).
