# Renard VI.4.1, Proposition, for one summand: proof

`Langlands.CuspidalSupport.rationalSummandSmallProgenerator` proves exactly
`RationalSummandSmallProgeneratorStatement.{uF, uV}` (module
`Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement`),
with the field universe `uF` and the carrier universe `uV` independent and
arbitrary. [Statement](RationalSummandSmallProgeneratorStatement.md)

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: VI.4.1,
Proposition and its proof, printed p.149 / PDF p.155; VI.3.2, printed
pp.143–144 / PDF pp.149–150.

## What is proved

For every nonarchimedean local field `F`, connected reductive group `G` over
`F`, maximal split torus `i` and generic cocharacter `ν`, under the statement's
`StandardCocharacterStatement`, relative-root-system and
standard-unipotent-closedness premises and its local compactness,
nonarchimedean-group and Hausdorff instances on `H = G(F)`: let `π` be an
irreducible smooth complex representation of `H`, cuspidal in the sense of
`Aubert.General.IsCuspidal`, let `ρ` be an irreducible smooth representation of
the common norm kernel `H⁰ = Plancherel.rationalCommonNormKernel G`, and let
`j : ρ ⟶ SmoothRep.restrictSubgroup H⁰ π` be injective. Then
`Π = rationalNormKernelSummandInduction G ρ` satisfies
`IsRationalInertiaSmallProgenerator G π Π`: it lies in
`RationalInertiaBlock G (rationalInertiaBaseLift G π)`, lifts along every
epimorphism of the block, `preadditiveCoyonedaInt` of it is faithful, the block
has all coproducts indexed by `Type (max uF uV)`, and that Hom functor
preserves them.

The theorem has no hypotheses of its own. The statement's Lean/Markdown pair
and its imports are unchanged. No admissibility, compactness,
finite-dimensionality, splitness, characteristic, finite-length or abelianness
premise is added. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The Lean term is one application:

```
rationalSummandSmallProgenerator_of_jointBasis
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
  rationalNormKernelFiniteRestriction.{uF, uV}
  rationalNormKernelTwistEquivalence.{uF, max uF uV, max uF uV}
```

- `rationalSummandSmallProgenerator_of_jointBasis` (module
  `RationalSummandSmallProgeneratorReduction`,
  [Markdown](RationalSummandSmallProgeneratorReduction.md)) derives
  `RationalSummandSmallProgeneratorStatement.{uF, uV}` from
  `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`,
  `RationalNormKernelFiniteRestrictionStatement.{uF, uV}` and
  `RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}`.
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves the
  first input for every universe: Renard V.5.1–V.5.2 at one special vertex, a
  common apartment datum, point and torus centralizer satisfying the special
  compact properties, the Iwasawa and Cartan comparisons and the simultaneous
  standard basis.
  [Markdown](../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `rationalNormKernelFiniteRestriction` (module
  `RationalNormKernelFiniteRestrictionProof`) proves VI.3.2(ii): the
  restriction to `H⁰` of an irreducible smooth representation is semisimple,
  of finite length, and spanned by finitely many irreducible
  subrepresentations. [Markdown](RationalNormKernelFiniteRestrictionProof.md)
- `rationalNormKernelTwistEquivalence` (module
  `RationalNormKernelTwistEquivalenceProof`) proves VI.3.2(iii) for two
  independent carrier universes; here both are `max uF uV`, the carrier
  universe of the block. [Markdown](RationalNormKernelTwistEquivalenceProof.md)

The universe arguments are exactly those the reduction asks for, so the term
has the type of the target statement.

### The route inside the reduction

The reduction proves the Proposition as follows (details in its Markdown).

1. **Compact coefficients of `Res π`.** For the data of the statement, the
   joint basis gives an apartment datum, a special vertex and the special
   compact, simultaneous basis and finite Cartan covering properties of its
   subgroup (`rationalSpecialVertexCompactInputs_of_jointBasis`). The published
   VI.2.1 implication `Langlands.Aubert.General.rationalCuspidalCompactRestriction`
   turns these, the statement's standard-cocharacter, root-system and
   unipotent-closedness premises and the cuspidality of `π` into compact
   smooth-dual coefficients of the restriction of `π` to `H⁰`. This is the only
   use of cuspidality.
2. **Membership.** VI.3.2(ii) and (iii) and these compact coefficients put
   `Π₁ = ind_{H⁰}^{H}(Res π)` in the block
   (`rationalNormKernelCompactInduction_mem_of_restriction`). The compact
   induction of `j` is an injection `Π → Π₁`, and the block is closed under
   subquotients, so `Π` is in the block.
3. **Projectivity.** Compact coefficients pass from `Res π` to `ρ` along `j`,
   so `Π` is projective among smooth representations of `H`
   (`Induction.projective_compactInduced_of_compactCoefficients`), hence in the
   block (`rationalInertiaBlock_projective_of_projective`).
4. **Faithfulness.** By Frobenius reciprocity for the open subgroup `H⁰`,
   applied to `j` and the isomorphism of restrictions of unramified twists,
   `Π` maps nontrivially to every irreducible object of the block;
   `SmoothRep.faithful_preadditiveCoyonedaInt_of_projective_subquotients` then
   gives faithfulness.
5. **Coproducts and smallness.** The block has coproducts indexed by
   `Type (max uF uV)` (`rationalInertiaBlock_hasColimitsOfShape`). An
   irreducible `ρ` is cyclic, so `Π` is finitely generated
   (`Induction.finite_compactInduced_of_finite`), and
   `rationalInertiaBlockHom_preservesCoproducts_of_finite` gives preservation
   of these coproducts.

## Correspondence with Renard

Renard proves projectivity from the adjunction (VI.4.1.1) and semisimplicity
of restrictions to `⁰G`, generation from `Hom_G(Π, τ) ≠ 0`, finite type from
the functions `f_{i,w}` of (VI.4.1.2), and smallness from finite type. The
implemented route follows these four steps, with projectivity obtained from
compactness of `ρ` (inherited from compactness of `Res π`, which is where the
special-compact geometry and cuspidality enter) and with membership of `Π` in
the block, implicit in Renard, derived from that of `Π₁` through VI.3.2(ii) and
(iii). Renard's `ρ` is a summand of `Res π`; the statement takes any
irreducible `ρ` with an injective equivariant map into `Res π`, and the proof
uses only that injection.
