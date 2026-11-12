# Proper quotients of reductive group schemes by parabolic subgroups: proof

Author: Worker 4778.

Module `Langlands.GroupScheme.RelativeParabolicQuotientProof`, namespace
`Langlands.GroupScheme.RelativeParabolicQuotient`.

The theorem `Langlands.GroupScheme.RelativeParabolicQuotient.existence` proves the published
proposition `Langlands.GroupScheme.RelativeParabolicQuotient.ExistenceStatement.{u}` (module
`Langlands.GroupScheme.RelativeParabolicQuotientStatement`). The theorem's type is that
proposition itself, in the same universe `u`. The statement and its imports are unchanged.

## What is proved

Take any commutative ring `R : Type u`, group schemes `G P` over `Spec R` and a homomorphism
`i : P ⟶ G`. Assume that `G` is reductive (`IsReductive G`), that `P` is smooth over `Spec R`,
that the underlying scheme map of `i` is a closed immersion, and that for every field
`k : Type u` with `Algebra R k` the base change of `i` to `Spec k` is a parabolic subgroup.
Then there are an object `Q` of `Over (Spec R)` and a morphism `q : G.X ⟶ Q` with these
properties:

- `Q` is proper over `Spec R`;
- `q.left` is flat, surjective and quasi-compact;
- for every test object `T` over `Spec R` and all `g h : T ⟶ G.X`, `g ≫ q = h ≫ q` holds
  exactly when `g⁻¹ * h` lies in `(SubgroupFunctor.range i).carrier T`.

Every case of the statement is kept: arbitrary rings (non-Noetherian, non-local and the zero
ring), non-split groups, the improper case `P = G`, and arbitrary test schemes `T`. The proof
adds no hypothesis. It supplies no quotient, properness certificate, split torus, cocharacter
presentation or local section as a premise. `lean_check` reports that it depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## The Lean proof

The proof is the single term

```lean
existenceStatement_of_dynamic_and_ambient parabolicDynamic selfNormalizingProperAmbient
```

All three names are published Library results:

- `Langlands.GroupScheme.RelativeParabolicQuotient.existenceStatement_of_dynamic_and_ambient`
  (module `Langlands.GroupScheme.RelativeParabolicQuotientConstruction`). It proves
  `ExistenceStatement.{u}` from `ParabolicDynamicStatement.{u}` and
  `SelfNormalizingProperAmbientStatement.{u}`.
- `Langlands.GroupScheme.parabolicDynamic : ParabolicDynamicStatement.{u}` (module
  `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`). Over a field, a closed subgroup of a
  connected reductive group is parabolic exactly when it is the dynamic subgroup `P(χ)` of a
  cocharacter `χ` defined over that field (Milne, Theorem 25.1).
- `Langlands.GroupScheme.selfNormalizingProperAmbient : SelfNormalizingProperAmbientStatement.{u}`
  (module `Langlands.GroupScheme.SelfNormalizingProperAmbientProof`). Take a smooth affine group
  `G` over `Spec R` with geometrically connected fibres. Let `H` be a smooth closed subgroup with
  geometrically connected fibres that equals its own normalizer on all tests. Then there is a
  map `r : G.X ⟶ Y` into a proper, locally finitely presented `Y` over `Spec R` whose fibres on
  every test scheme are exactly the right cosets of `H`.

### What the reduction does

This module only applies the reduction. For the reviewer, here is how the published reduction
uses the two inputs. Each module named below has its own Markdown.

1. `RelativeParabolicQuotient.existenceStatement_of_dynamic_and_ambient` passes the two inputs on
   to `RelativeParabolicQuotientReduction.existenceStatement_of_dynamic_and_ambient`. It also
   supplies the published generic properness criterion `properAmbientCriterion_holds`, from
   `Langlands.AlgebraicGeometry.ProperOfFibres.ProperAmbientCriterionProof`.
2. That reduction calls `RelativeParabolicQuotient.existenceStatement_of_statements` (module
   `Langlands.GroupScheme.RelativeParabolicQuotientAssembly`) with five inputs:
   - the relative self-normalizer criterion `relativeSelfNormalizer`;
   - the field self-normalizer theorem
     `fieldSelfNormalizer_of_parabolicDynamic parabolicDynamic`, which is
     `parabolicSelfNormalizerStatement_of_rational_descent` applied to `borelConjugacy`,
     `borelNormalizer`, `parabolicDynamic` and `dynamicConnected`;
   - `parabolicDynamic`;
   - `selfNormalizingProperAmbient`;
   - `properAmbientCriterion_holds`.
3. Fix `R`, `G`, `P` and `i` satisfying the hypotheses. The assembly runs in four steps.
   - **Ambient map.** `RelativeParabolicNormalizerReduction.properAmbientOfStatements` gives
     the ambient map. The fibres of `P` are geometrically connected: at a field point the base
     change of `P` is parabolic, so `parabolicDynamic` writes it as some `P(χ)`, and
     `dynamicConnected` shows that `P(χ)` is connected. `P` equals its own normalizer on all
     tests: `relativeSelfNormalizer` reduces this to field points, where the field
     self-normalizer theorem applies. With these facts `selfNormalizingProperAmbient` gives a
     proper, locally finitely presented `Y` and a map `r : G.X ⟶ Y` with exact right-coset
     fibres.
   - **Quotient.** `RelativeHomogeneousQuotient.quotientEmbeddingOfMapKernel` builds an actual
     homogeneous quotient `Q` of `G` by `P` from `r`. It also gives a monomorphism `Q ⟶ Y` over
     `Spec R` through which `r` factors. To do this it calls
     `SmoothRelationQuotient.schemeQuotientOfMapKernel` on the right-coset relation of `P` in
     `G` (`HomogeneousQuotientFromEmbedding.relation_iff`). On every test object the classes of
     that relation are the right cosets of `P`. That construction
     (`exists_scheme_quotient_of_map_kernel`, module
     `Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientEmbedding`) does three
     things:
     - It forms the quotient sheaf `quotientSheaf`, the sheafification for the étale topology
       over `Spec R` of the presheaf of pointwise relation classes. The published theorem
       `smoothRelationQuotient` shows that this sheaf is an algebraic space and that the map
       from `G.X` to it is smooth and surjective.
     - The fibres of `r` are exactly the cosets, so `r` induces a monomorphism from the
       quotient sheaf into the functor of points of `Y` (`mono_quotientSheafDesc`).
     - The published theorem `monomorphismLocallyFiniteTypeScheme` represents the algebraic
       space by a scheme. It applies to an algebraic space with a monomorphism into a scheme and
       an étale surjective cover by a scheme that is locally of finite type over that scheme.
       The representing scheme is `Q`.

     The projection `G.X ⟶ Q` is smooth, surjective and quasi-compact. `Q` is separated over
     `Spec R` because `Y` is. It is quasi-compact over `Spec R` because `G.X` is and the
     projection is surjective.
   - **Properness.** `RelativeParabolicQuotientFibers.smooth` shows that `Q` is smooth over
     `Spec R`. At each field point, `proper_fieldBaseChange` shows that the fibre of `Q` is
     proper; it uses the published field result `parabolicSubgroupQuotientProper`. The fibre is
     connected by `connectedSpace_fieldBaseChange`. `properAmbientCriterion_holds` then proves
     that `Q` is proper over `Spec R`.
   - **Conclusion.** The projection is smooth, hence flat. The homogeneous quotient records
     surjectivity, quasi-compactness and the exact right-coset criterion on every test object.
     These are the conclusions of `ExistenceStatement`.

## Relation to the literature

The statement is a derived form of Brian Conrad, *Reductive group schemes* (2014), literature
id `conrad-2014-reductive-group-schemes`, Corollary 5.2.8 (pp. 155–156) together with
Theorem 2.3.6 (pp. 72–73), as explained in the statement's Markdown. In the proof of
Corollary 5.2.8 (p. 156), Conrad shows that `P` equals its own normalizer and then applies
Theorem 2.3.6. Part (1) of that theorem represents the étale quotient sheaf `G/P` by a smooth
scheme. Part (2) makes it proper when the geometric fibres `G_s/P_s` are projective.

Conrad proves Theorem 2.3.6 on pp. 73–74. He first reduces to a Noetherian base. He then
finds an infinitesimal neighbourhood `P_n` of the identity whose normalizer is `P`. The orbit map
from `G` into a Grassmannian built from the jets `G_n` identifies the étale quotient sheaf `G/P`
with a subfunctor of a projective scheme. An argument with algebraic spaces and Zariski's Main
Theorem then shows that `G/P` is a smooth scheme. For part (2) he uses EGA IV_3 15.7.10: a
separated, flat, surjective map of finite type with proper, geometrically connected fibres is
proper. To prove it he reduces to a complete local Noetherian base and uses Grothendieck's
algebraization theorem.

The Lean route compares with this as follows:

- **Self-normalization.** It keeps this step.
- **Ambient map.** The proper ambient map comes from the finite-jet orbit construction of
  `selfNormalizingProperAmbient`. That construction follows Conrad's proof of
  Theorem 2.3.6(1) but makes no Noetherian reduction, as its own Markdown explains.
- **Quotient.** This step has the same shape as Conrad's. The étale sheafification of the
  pointwise coset quotient is shown to be an algebraic space. The ambient map induces a
  monomorphism from it into the proper ambient scheme, which proves that it is represented by
  a scheme.
- **Properness.** Here the Lean route differs from Conrad. It does not use EGA IV_3 15.7.10 or
  formal algebraization. It checks the existence part of the valuative criterion over
  arbitrary valuation rings. The inputs are smoothness, the proper and connected field fibres,
  and the monomorphism into the proper ambient scheme (`properAmbientCriterion_holds`). Field
  fibre properness comes from the published field result `parabolicSubgroupQuotientProper`,
  not from projectivity of the geometric fibres.

These are the routes of the published modules named above.
