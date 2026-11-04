# Reduction of the double-sharp isomorphism to the class formula and involutivity

Authors: Worker 984 and Worker 923, task `9d570c9e-e376-4437-8d15-3cbe9e9a0027`.
Worker 984 wrote the generic reduction. Worker 923 wrote the standard-family
inputs of the rational theorem (module `RationalStandardParabolicTransport`) and
observed that irreducibility follows from cuspidal-series retention.

This module reduces Aubert's Corollaire 3.9 (c), `(E#)# ≅ E` for `E ∈ 𝔈(I)`,
to named inputs, at two levels:

- for an abstract standard family indexed by `Finset ι`
  (`SharpInvolutionTarget` of `SharpConsequenceStatements`), and
- for the actual rational-point family (`RationalSharpInvolutionStatement` of
  `RationalSharpConsequenceTargets`).

Every input of the rational theorem is a published proposition of the Library.
None is proved here. The module does not prove `SharpInvolutionTarget` or
`RationalSharpInvolutionStatement` outright: the closing theorems are
conditional reductions, and their inputs remain separate obligations.

## Source and provenance

Aubert 1995 (registered source `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`),
Corollaire 3.9 and its proof, printed p.2189 / PDF p.11. The statement is
"(c) `(E#)#` est isomorphe à `E` comme `G`-module". The whole proof of (c) is
"L'assertion (c) résulte du fait que `D_G` est une involution
(cf. th. 1.7, assertion (3))". The Lean proof spells out this step along the
route recorded in `notes/aubert/support-filtration-consequences-source-map.md`,
item 5 (c):

1. `E#` lies in some `𝔈(I')` with `I'` associated to `I`, and `(E#)#` (at `I'`)
   lies in some `𝔈(I'')`. In particular both are irreducible.
2. Associated subsets have the same cardinality, so the cokernel at `I'` is
   the cokernel at `I`.
3. The class formula (a), applied to `E` at `I` and to `E#` at `I'`, together
   with `D_G ∘ D_G = id`, gives `[(E#)#] = [E]`.
4. Two irreducible representations with the same exact Grothendieck class are
   isomorphic.

The source map derives irreducibility of `E#` from (b) before it derives
cuspidal-series retention. Here cuspidal-series retention is taken as the input.
Membership in a cuspidal series includes irreducibility, so (b) is not a
separate hypothesis. This is a reorganization of inputs, not a different
argument.

The rational theorem needs the premises `hP`, `hproj`, `hiFl`, `hrFl` of the
published `RationalInvolutivityStatement` for the actual standard family. The
target does not supply them. They are derived (see the rational section) from
`hStandard`, from published topology results and from the published
`DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement`
(module `PrerequisiteStatements`). The Library attributes those two to Renard
VI.6.2 and VI.6.4.

## Generic reduction

The section variables are those of `SharpConsequenceStatements`: an index type
`ι` with `[LinearOrder ι] [Fintype ι]`, a locally compact nonarchimedean group
`G`, families `P M U : Finset ι → Subgroup G` with decompositions `h`, radical
closedness `hclosed`, unimodularity `hδ`, monotonicity `hP` and `hU`, Levi
closedness `hM`, the Levi decompositions `hL`, and an association relation
`IsAssociate : Finset ι → Finset ι → G → Prop`. Carriers live in
`Type (max uI uG uV)`.

- `doubleSharpObject P M U h hclosed hδ hP hU E I`: the double terminal
  cokernel `(E#)#`, that is
  `StandardComplex.sharpObject … (StandardComplex.sharpObject … E I) I`. Both
  cokernels are taken at the same index `I`, so at degree `|S| − |I|`. This is
  the object in `SharpInvolutionTarget`. Nothing else in the module uses the
  definition. It names the construction for readers.
- `sharpObject_eq_of_card_eq A hIJ`: if `I.card = J.card`, then
  `StandardComplex.sharpObject … A I = StandardComplex.sharpObject … A J`
  (equality of objects). The proof unfolds `StandardComplex.sharpObject`,
  `Complex.sharpObject` and `Complex.terminalDegree`. The index enters only
  through `Fintype.card ι - I.card`.
- `sharpInvolutionTarget_of_classFormula hfl hinv hrefl hcard hCF hCS`:
  `SharpInvolutionTarget … hM hL` holds under these hypotheses:
  - `hfl : ∀ J, ParabolicFiniteLength (h J) (hclosed J)`, one finite-length
    proof for the operator;
  - `hinv : D ∘ₗ D = LinearMap.id` for `D = alternatingOperator … hfl`
    (Theorem 1.7 (3));
  - `hrefl : ∀ I, IsAssociate I I 1`;
  - `hcard : ∀ I J n, IsAssociate I J n → I.card = J.card`;
  - `hCF : SharpClassFormulaTarget … IsAssociate` (Corollaire 3.9 (a));
  - `hCS : SharpCuspidalSeriesTarget … IsAssociate`.

  Proof. Let `E ∈ 𝔈(I)`. `hCS` gives `I'`, `n` with `IsAssociate I I' n` and
  `E# ∈ 𝔈(I')`. Applied again to `E#` at `I'`, it gives `(E#)# ∈ 𝔈(I'')`
  for some `I''`, where `(E#)#` is taken at `I'`. Then `hcard` gives
  `I.card = I'.card`, and `sharpObject_eq_of_card_eq` identifies the cokernel
  of `E#` at `I` with the one at `I'`. `E`, `E#` and `(E#)#` (at `I'`) are
  irreducible: membership in a cuspidal series starts with irreducibility.
  All three have finite length by `SmoothRep.hasFiniteLength_of_isIrreducible`.
  The published `IsInCuspidalSeries.isInSupportCategory` with `hrefl` puts `E`
  in `Alg({I})` and `E#` in `Alg({I'})`. `hCF hfl` gives
  `D [E] = (-1)^{|I|} • [E#]` and `D [E#] = (-1)^{|I'|} • [(E#)#]`. Applying
  `hinv` to `[E]` and rewriting with `map_zsmul`, `|I'| = |I|` and
  `(-1)^{2|I|} = 1` gives `[(E#)#] = [E]` in the exact finite-length
  Grothendieck group. The published
  `SmoothRep.ofRepresentation_eq_irreducible_iff`, with `E` irreducible,
  turns this into an equivalence of the underlying representations, and
  `SmoothRep.mkIso` turns that into an isomorphism in `SmoothRep`. Composing
  with `eqToIso` of the cokernel equality gives `Nonempty ((E#)# ≅ E)` with
  both cokernels at `I`.

Three Corollaire 3.9 targets are not hypotheses: the finite-length statement for
`E#` (`SharpFiniteLengthTarget`), support retention
(`SharpSupportRetentionTarget`) and irreducibility (`SharpIrreducibleTarget`).
Finite length of every object involved comes from irreducibility, and
irreducibility comes from cuspidal-series membership.

## Rational section

Namespace `Langlands.Aubert.General.RationalPointFamily`, universes `u`, `v`.

`rationalSharpInvolutionStatement_of_inputs hiDyn hrDyn hInv hCF hCS` proves
`RationalSharpInvolutionStatement.{u, v}` from

- `hiDyn : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`
  (normalized induction from `Z(χ)(F)` preserves finite length),
- `hrDyn : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`
  (the normalized Jacquet functor to `Z(χ)(F)` preserves finite length),
- `hInv : RationalInvolutivityStatement.{u, v}` (Theorem 1.7 (3)),
- `hCF : RationalSharpClassFormulaStatement.{u, v}` (Corollaire 3.9 (a)),
- `hCS : RationalSharpCuspidalSeriesStatement.{u, v}`.

Proof. Introduce the premises of the target, with `pointTopology` as a local
instance and the `Fintype (SimpleRoot i ν)` instance
`simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν`. That is the
instance fixed by the target and the one used by `rationalAlternatingOperator`.
Then:

- the published `rationalWeylComparison` gives `hN` and `hZ`, the association
  hypotheses of `hCF` and `hCS`;
- `hP := isClosed_standard_parabolic i ν hStandard hG hi hν`
  (`RationalStandardParabolicTransport`): every `parabolic i ν I` is closed;
- `hproj := continuous_standard_projection i ν hStandard hG hi hν` (published,
  `RationalStandardInductionNonzero`): every standard projection is continuous;
- `hiFl I := standard_induction_preservesFiniteLength i ν hStandard hG hi hν hiDyn I (hU I)`
  and
  `hrFl I := standard_jacquet_preservesFiniteLength i ν hStandard hG hi hν hrDyn I (hU I)`
  (`RationalStandardParabolicTransport`): the standard normalized induction and
  Jacquet functors preserve finite length.

Apply `sharpInvolutionTarget_of_classFormula` with

- `IsAssociate := rootAssociation i ν hN hZ`;
- `hfl := standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl`
  (published, `RationalAlternatingOperator`);
- `hinv` from `hInv` at the same premises (its operator
  `rationalAlternatingOperator` is by definition `alternatingOperator` with
  this `hfl`);
- `hrefl := rootAssociation_one i ν hN hZ` and
  `hcard := rootAssociation_card_eq i ν hN hZ` (published,
  `RootAssociationLaws`);
- `hCF` and `hCS` at the target's premises.

The target's binders `hOrder`, `hInter`, `hRoots`, `hU`, `hM`, `hUc` and the
`LinearOrder` instance are passed through unchanged. No binder is added to the
target.

## Declaration-level dependencies

Published or companion declarations used by the proofs, besides the
definitions that appear in the statements:

- `Langlands.SmoothRep.ofRepresentation_eq_irreducible_iff`
  (`Smooth.IrreducibleClassDetection`; composition multiplicities of the exact
  finite-length Grothendieck group, coefficient field arbitrary);
- `Langlands.SmoothRep.hasFiniteLength_of_isIrreducible`
  (`Smooth.IrreducibleRealization`);
- `Langlands.SmoothRep.mkIso` (`Category.Basic`);
- `Langlands.Aubert.General.IsInCuspidalSeries.isInSupportCategory`
  (`Aubert.General.SupportCategory`);
- `rationalWeylComparison` (`Aubert.General.RationalWeylComparisonProof`);
- `rootAssociation_one`, `rootAssociation_card_eq`
  (`Aubert.General.RootAssociationLaws`);
- `standardParabolicFiniteLength` (`Aubert.General.RationalAlternatingOperator`);
- `continuous_standard_projection` (`Aubert.General.RationalStandardInductionNonzero`);
- `isClosed_standard_parabolic`, `standard_induction_preservesFiniteLength`,
  `standard_jacquet_preservesFiniteLength`
  (`Aubert.General.RationalStandardParabolicTransport`, submitted together with
  this module). These use the published `exists_parabolic_eq_dynamic`
  (`RationalInductionDualityReduction`), `isClosed_dynamic_parabolic`
  (`DynamicInductionExactness`) and `BruhatTits.localField_t2Space`.

The paired Markdown of each of these modules records its own inputs:

- `RationalWeylComparisonProof.md`: no representation-theoretic theorem, Langlands
  classification, character independence, geometric lemma, adjointness or
  cuspidal-support theorem. Its mathematical input is split-torus rational-point
  detection.
- `IrreducibleClassDetection.md`: no parabolic, Aubert or classification theorem
  input.
- `IrreducibleRealization.md`: no analytic, parabolic, Jacquet, Jordan–Hölder or
  classification theorem.
- `RootAssociationLaws.md`: deductions from the definitions of `rootAssociation`,
  `rootSet` and `weylCharacterAction`. It uses no Levi conjugation, geometric
  lemma, Jacquet nonvanishing or support detection.
- `RationalStandardInductionNonzero.md`: no classification, character
  independence, geometric lemma or adjointness.
- `DynamicInductionExactness.md`: no classification, geometric lemma or
  finite-length preservation theorem.
- `IsInCuspidalSeries.isInSupportCategory` takes the inducing cuspidal `σ` of the
  membership `E ∈ 𝔈(I)` and applies the published
  `isInSupportCategory_cuspidalInduction` and `IsInSupportCategory.of_isSubquotient`.
- `standardParabolicFiniteLength` takes the two finite-length premises. The
  exactness half of `ParabolicFiniteLength` comes from the published
  topological theorem `ParabolicFiniteLength.of_preservesFiniteLength`.
- `exists_parabolic_eq_dynamic` and `continuous_standard_projection` only unpack
  `hStandard` and transport along the resulting subgroup equalities.
  `isClosed_dynamic_parabolic` uses the closed-subgroup property of the
  dynamic parabolic subgroup scheme.

The proofs in this module and in `RationalStandardParabolicTransport` invoke no
Langlands classification, character independence, geometric lemma or
adjointness result. Aubert's Proposition 3.2 is not used.

The import closure has 508 workspace modules, all with nonempty paired
Markdown:

- the 428 modules of the closure of `RationalSharpConsequenceTargets`, that
  module included;
- `RationalInvolutivityTarget`, `RootAssociationLaws`,
  `RationalWeylComparisonProof`, and the 13 `GroupScheme.*` modules behind
  `RationalWeylComparisonProof`;
- 16 Jordan–Hölder and multiplicity modules `Representation.Filtration.*`, and
  `Smooth.IrreducibleClassDetection`, `Smooth.IrreducibleCompositionFactors`,
  `Smooth.IrreducibleRealization`;
- 45 more behind `RationalStandardParabolicTransport`: that module itself,
  `PrerequisiteStatements`, `DynamicInductionExactness`(`Statement`),
  `RationalInductionDuality{Reduction,Statement}`,
  `RationalStandardInductionNonzero`(`Statement`), and their point-topology,
  dynamic representability, locally profinite, contragredient and
  compact-pairing imports.

All proofs are complete. They use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

An unconditional proof of `RationalSharpInvolutionStatement` follows from
`rationalSharpInvolutionStatement_of_inputs` once these five published
propositions are proved:

- `DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}` and
  `DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`;
- `RationalInvolutivityStatement.{u, v}`;
- `RationalSharpClassFormulaStatement.{u, v}`;
- `RationalSharpCuspidalSeriesStatement.{u, v}`.
