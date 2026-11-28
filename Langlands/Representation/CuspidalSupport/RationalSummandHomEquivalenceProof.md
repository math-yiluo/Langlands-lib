# Renard VI.4.1, Theorem, for one summand: proof

`Langlands.CuspidalSupport.rationalSummandHomEquivalence` proves exactly
`RationalSummandHomEquivalenceStatement.{uF, uV}` (module
`Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement`),
with the field universe `uF` and the carrier universe `uV` independent and
arbitrary. [Statement](RationalSummandHomEquivalenceStatement.md)

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: VI.4.1,
Proposition, (VI.4.1.3) and Theorem with its proof, printed pp.149–151 / PDF
pp.155–157; A.VIII.2, printed pp.266–267 / PDF pp.272–273; VI.3.2, printed
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
`j : ρ ⟶ SmoothRep.restrictSubgroup H⁰ π` be injective. Then the compact
induction `Π` of `ρ` from `H⁰` lies in
`RationalInertiaBlock G (rationalInertiaBaseLift G π)`, and for the resulting
object `P` of the block, `preadditiveCoyonedaObj P` is an equivalence from the
block to `ModuleCat (End P)ᵐᵒᵖ`, the category of unital right `End P`-modules
with carriers in `Type (max uF uV)`.

The theorem has no hypotheses of its own. No admissibility, compactness,
finite-dimensionality, splitness, characteristic, finite-length or abelianness
premise is added; the abelian structure of the block used in the proof is
constructed, not assumed. The quasi-inverse is not identified with
`M ↦ M ⊗_R V_Π`, and the statement does not ask for it. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Proof

The Lean term is one application:

```
rationalSummandHomEquivalence_of_jointBasis
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
  rationalNormKernelFiniteRestriction.{uF, uV}
  rationalNormKernelTwistEquivalence.{uF, max uF uV, max uF uV}
```

- `rationalSummandHomEquivalence_of_jointBasis` (module
  `RationalSummandSmallProgeneratorReduction`,
  [Markdown](RationalSummandSmallProgeneratorReduction.md)) derives
  `RationalSummandHomEquivalenceStatement.{uF, uV}` from
  `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`,
  `RationalNormKernelFiniteRestrictionStatement.{uF, uV}` and
  `RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}`.
  It is `rationalSummandHomEquivalence_of_smallProgenerator` applied to
  `rationalSummandSmallProgenerator_of_jointBasis` of the same three inputs.
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves the
  first input for every universe: Renard V.5.1–V.5.2 at one special vertex.
  [Markdown](../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `rationalNormKernelFiniteRestriction` (module
  `RationalNormKernelFiniteRestrictionProof`) proves VI.3.2(ii).
  [Markdown](RationalNormKernelFiniteRestrictionProof.md)
- `rationalNormKernelTwistEquivalence` (module
  `RationalNormKernelTwistEquivalenceProof`) proves VI.3.2(iii) for two
  independent carrier universes; here both are `max uF uV`, the carrier
  universe of the block. [Markdown](RationalNormKernelTwistEquivalenceProof.md)

The universe arguments are exactly those the reduction asks for, so the term
has the type of the target statement.

### The route inside the reductions

1. **The Proposition.** `rationalSummandSmallProgenerator_of_jointBasis`
   proves `RationalSummandSmallProgeneratorStatement.{uF, uV}` from the three
   inputs: the joint basis and cuspidality give compact smooth-dual
   coefficients of `Res π` (through the published VI.2.1 implication
   `Langlands.Aubert.General.rationalCuspidalCompactRestriction`); with
   VI.3.2(ii) and (iii) this puts `Π₁ = ind_{H⁰}^{H}(Res π)`, hence its
   subrepresentation `Π`, in the block; compactness of `ρ` gives projectivity;
   Frobenius reciprocity along `j` gives faithfulness of the Hom functor; and
   finite generation of `Π` gives preservation of coproducts indexed by
   `Type (max uF uV)`, which the block has. The steps are described in the
   reduction's Markdown.
2. **From the Proposition to the Theorem.**
   `rationalSummandHomEquivalence_of_smallProgenerator` (module
   `RationalSummandHomEquivalenceReduction`,
   [Markdown](RationalSummandHomEquivalenceReduction.md)) applies, for the
   same data, the objectwise
   `isEquivalence_preadditiveCoyonedaObj_of_isRationalInertiaSmallProgenerator`.
   The block carries Mathlib's abelian structure of a full subcategory closed
   under kernels, cokernels and finite products (the Serre-class and
   finite-product closure of `rationalInertiaBlockProperty`), whose additive
   structure is the full-subcategory one (`rationalSummandBlock_abelian`). The
   lifting condition is Mathlib's `Projective` in the block, which
   `Langlands.Renard.homProjectiveComparison` turns into exactness of the
   integer Hom functor; with faithfulness and coproduct preservation this is
   `Langlands.Renard.HomSmallProgenerator.{max uF uV}`. The published proof of
   A.VIII.2,
   `Langlands.Renard.preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator`,
   then makes `preadditiveCoyonedaObj P` an equivalence.

## Correspondence with Renard

Renard deduces the Theorem from the Proposition through the functors
`F_Π = Hom_G(Π, •)` and `G_Π = • ⊗_R V_Π`, right exactness, compatibility with
direct sums and presentations by direct sums of copies of `V_Π` and of `R`.
The implemented route instead applies the general A.VIII.2 equivalence for a
small progenerator of an abelian category with coproducts, which shows directly
that `F_Π` is faithful, full and essentially surjective. The functor is
Renard's `F_Π` of (VI.4.1.3): `End P` acts on `P ⟶ Y` by precomposition
through `(End P)ᵐᵒᵖ`. Renard's `ρ` is a summand of `Res π`; the statement takes
any irreducible `ρ` with an injective equivariant map into `Res π`, and the
proof uses only that injection.
