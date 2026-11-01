# Source-rank recursion for actual mirabolic derivatives

This internal helper module adds equality-transport laws and a source-rank
recursion for the existing determinant-normalized derivative functors. It
preserves the supplied topology and independent field and carrier universes.

The source convention is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), registered source
`bernstein-zelevinsky-1977-induced-i`, §3.5 and footnote (2), printed p.452
(one-based PDF p.13), SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The footnote orders the successive minus functors from largest rank to
smallest rank. The formulas below are internal consequences of the existing
Lean definitions, without a new claim about source normalization.

For `h : a = b`, mirabolic rank transport composes transitively and cancels
with its reverse. Transport commutes with `psiMinus`, `phiMinus`, their
iteration, the target-indexed derivative, and the source-rank/order wrapper.
Each proof eliminates the rank equality and uses the identity-functor laws.
These are equalities of complete functors, so they include every morphism.

For `1 ≤ i ≤ N+1`, `mirabolicDerivativeOfOrder_succ` proves
that the order-`i+1` derivative on `mirabolic (N+1)` is `phiMinus T ψ N`
followed by the order-`i` derivative on `mirabolic N`, after the explicit
general-linear rank cast
`N+2-(i+1) = N+1-i`. Its proof writes `i=j+1`, uses the published
`mirabolicDerivative_succ`, and eliminates the equalities
`N = (N+1-i)+(i-1)` and the equal target ranks.
`mirabolicDerivativeOfOrderSuccIso` is the natural isomorphism induced by
this functor equality; its components and inverses are the identity after
equality elimination, and naturality follows for every morphism.

## Proof and source boundary

The proofs use only equality elimination, identity and associativity of functor
composition, `mirabolicDerivative_succ`, the defining equality
`mirabolicDerivativeOfOrder_eq`, and natural-number arithmetic (`omega`). The
wrapper recursion first rewrites both wrappers and then rewrites
`Functor.assoc`; this avoids unfolding the actions while comparing differently
associated compositions. No component of a mixed product is used here.

The equality-induced natural isomorphism has its forward and inverse maps
supplied by `eqToIso`. Eliminating all rank equalities reduces both to identity
intertwiners. The equality is between entire functors, so naturality includes
all morphisms rather than only an object comparison. Both `uF` and `uV` remain
independent. All constructions install the supplied `T.topology`.

This internal recursion preserves exactly the determinant-normalized functors
already defined in `MirabolicMinus`. It does not substitute a Haar modulus or
claim a new comparison with it; no modulus comparison is used in its proof.
The source citation records only the ordering convention. The registered
original was read at PDF pp.11–13, 18–19 and 32, including the rendered ordering
formula on PDF p.13. The source-specific errata file was absent at the supplied
public-notes and Library-notes paths; no exhaustive errata search is claimed.

## Complete project import closure

The sole direct import is `Langlands.Representation.Derivative.Homogeneity`.
At Library base `b22e185743f7c318f709e14e422801f4360105d5`, the complete transitive
project closure (excluding this new module, including that direct import) has
54 modules. Every Lean/Markdown pair in this closure was compared byte for byte
with that public base and is unchanged. The list is:

```text

Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```

The imported construction path is actual groups and rank maps; local-field
normalization; smooth categories, transfer and twists; algebraic localization;
and the minus-functor iteration and source-rank wrapper. The Whittaker modules
in this list provide algebraic characters, not coinvariant-finiteness results.
`Homogeneity` defines level and homogeneity predicates and proves elementary
wrapper laws; it supplies no mixed-product homogeneity or detection theorem.
The 54-module closure has no project import outside this list. A full source
scan for the excluded conclusion families found no occurrence in its Lean
files; the Markdown mentions of classification are explanatory independence
or downstream-reference passages, not imported mathematics.

## Condition-by-condition independence audit

Both complete exclusion sets in task
`7e19f753-4515-4d87-9256-f366b6fc5683` revision 1, including their application to
mathematical conclusions, proof successors and transitive dependencies, bind
this helper unchanged. The following records each excluded family against the
complete closure and the actual proof above. For every row, the named
conclusions, their proof successors and downstream mathematical consequences
are absent from the import and proof dependencies.

| Condition | Audit result |
| --- | --- |
| Ordered multisegment socle existence (`23189526-80b0-4828-a6d4-7ebec2cbeef5`) and socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle construction, existence or exhaustion input. |
| Analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`) | No segment or analytic classification module. |
| Unlinked segment-socle product irreducibility (`23e98d90-6055-4e35-91a9-b0f5d8a84961`) and final criterion (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`) | No irreducibility or product criterion. |
| `AdjacentUnlinkedSegmentSocleSwap` (`e3634665-571b-4852-9f4c-bab8a1053434`, successor `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`) | No adjacent commutation. |
| `TwoSegmentSocleCommutation` (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`) | No segment commutation. |
| Special-head product criterion (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`) | No head or product irreducibility input. |
| Special-head exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`) | No multisegment or exhaustion result. |
| Ordered special/strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`) | No head existence input. |
| Quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`) | Only the actual localization construction, no quotient coverage theorem. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`) | No tempered result. |
| `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`) | No square-integrable classification. |
| Square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`) and regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`) | No exhaustion result. |
| `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`) | No generic-product or uniqueness input. |
| Ordered special-segment conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No conversion input. |
| Forward special-segment essential square-integrability (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No square-integrability theorem. |
| Combined Ze80 §5.4 reduction and strong-indecomposability consumers (`ff4738d8-47e3-433b-bedc-629bc2d492a7`) | No indecomposability or reduction theorem. |
| Nonadjacent two-supercuspidal irreducibility (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`) and full product structure (`ab61f565-1427-4746-ba77-46097563e962`), including adjacent composition/Jacquet clauses | No supercuspidal or two-factor structure input. |
| Individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No head or socle existence. |
| Full segment Jacquet formula (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), head formula (`55ad1e10-62d8-46b7-a081-909ef0056426`), socle formula (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`) and special exponent formula (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`) | Algebraic localization is present, but no segment Jacquet formula or exponent result. |
| Ze80 §3.5 and §9.6 segment derivative formulas, and the segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | No segment derivative theorem; only defining recursion of general BZ77 functors. |
| Ze80 4.2/9.7 product criteria, 9.3 analytic/square-integrability, classification and exhaustion | None imported or used; no circular use of Ze80 §2/Proposition 1.11. |
| Linked segment reverse-product structure (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`) and pair reducibility (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`) | No linked-pair result. |
| Juxtaposed reverse-product structure / quotient hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No such product or quotient-hom input. |
| `LinkedSegmentSocleGluing` (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`) | No gluing input. |
| Parent six-statement segment results (b), (d), (e), (f) | No segment statement or proof module. |
| `SupercuspidalCoinvariantFinitenessStatement` and all-character single-block conclusion (`62de5903-b616-4b5c-88eb-a066b77c5467`) | Neither occurs in the closure. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), and mirabolic finite length via `5428fe2c-013c-482d-aa6e-7df43e7191aa` | No finiteness or finite-length input. |
| Ze80 6.2 consumer (`b711af72-fdf9-4b32-a450-937911426822`), left-product homogeneity (`49d8eea3-1f52-4505-bfce-d76bf8ed5b8a`, successor `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4`), GL Leibniz (`3238f371-e9a2-42ce-8b5d-9c4d3400ff55`) | No consumer conclusion or theorem; the similarly named `Homogeneity` import is only the elementary wrapper module described above. |
| Operator-paused minus exactness (`b65bc667-6951-4bd5-82af-10fb7046df7f`) and Worker 127 controls | No exactness theorem is needed; the task was neither resumed nor bypassed, and Worker 127 was not contacted. |
| Unproved propositions, citations, drafts, conditional assemblies or pending tasks as proof evidence | None used as a proved input. Every non-arithmetic proof step is an equality law in the public Library or Mathlib, or proved in this module. |

This is a focused recursion contribution, not a proof of the mixed-product
derivative target. It does not duplicate 4.13(b,c) or assert any of its clauses.
