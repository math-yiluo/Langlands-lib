# Partial derivative of an exterior tensor product

Authors: Worker 288 and Worker 1004. Worker 288 constructed the binary tensor
quotient comparison and the final assembly. Worker 1004 constructed the
all-rank normalized top-localization adapter reused in that assembly.

The theorem `Langlands.Derivative.partialDerivativeTensor` proves exactly
`Langlands.Derivative.PartialDerivativeTensorStatement.{uF,uV} F T`, with outer
telescope

```text
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData).
```

After installing `T.topology`, the proposition quantifies every bundled unitary
additive character `ψ` with that topology and every `k m : ℕ`. It gives

```text
Nonempty (exteriorTensor.{uF,uV} T k m ⋙ partialDerivative T ψ k m ≅
  firstFactorTopDerivative T ψ k m).
```

This is a natural isomorphism of actual functors from
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) ×
 SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)` to
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier)`.
The same topology and the same character occur on both sides. The field and
module universes remain independent and every carrier stays in `Type uV`.
There are no added positivity, finite-length, admissibility, irreducibility,
genericity, nonzero-object or finite-dimension assumptions. The bundled
character retains its existing continuity, unitarity and nontriviality.

The target and its full dependency closure are unchanged. In particular the
right-hand second factor is the entire carrier of the published

```text
topDerivative T ψ m = generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙
  generalLinearRankCast T (Nat.sub_self m),
```

with its actual determinant-normalized minus functors and exact rank cast.

## Implemented components, inverses and both-variable naturality

Write `Q_m` for `PartialTensor.upperCoinvariantsFunctor ψ.complex m`. For a
smooth representation `B` of `GL_m`, its carrier is the quotient of `B` by the
span of `B(u)w - θ(u)w`, where `u` belongs to the actual full upper-unipotent
subgroup and `θ = Whittaker.entrywiseCharacter ψ.complex m`. It carries the
trivial action of the actual `GL_0` group and retains the whole quotient
module. Write `α_B` for the component of the published natural isomorphism
`TopLocalization.topLocalizationIso T ψ m : Q_m ≅ topDerivative T ψ m`.

The first comparison is the published
`PartialTensor.localizationTensorIso ψ.complex k m`. Its source is the exact
raw exterior tensor followed by partial localization; its target is
`(𝟭 _).prod Q_m ⋙ PartialTensor.firstFactorFunctor`. On representatives its
forward map is

```text
[v ⊗ w] ↦ v ⊗ [w],
```

and its inverse sends `v ⊗ [w]` back to `[v ⊗ w]`. These are genuine quotient
maps: `localizationToTensor` descends `id ⊗ quotient`, while
`tensorToLocalization` first descends the second variable of the
quotient-valued bilinear map and then uses `TensorProduct.lift`. Their two
composites are proved to be the identity using quotient hom extensionality,
tensor extensionality and surjectivity of the quotient map. The actual
`GL_k`-action is descended from `(g,1)`; those same formulas prove equivariance.
The published `localizationTensorEquiv_natural` treats any pair of arbitrary
intertwiners, and `NatIso.ofComponents` packages that proof in the smooth
category. This construction uses the raw binary `TensorProduct`; the indexed
`PiTensorProduct` API in `FiniteTensor.characterLocalizationEquiv` would require
extra group and tensor regrouping transports and is not used.

The second comparison is

```text
Functor.isoWhiskerRight
  (NatIso.prod (Iso.refl (𝟭 _)) (TopLocalization.topLocalizationIso T ψ m))
  PartialTensor.firstFactorFunctor.
```

`NatIso.prod` keeps the identity natural isomorphism on the first representation
and uses the actual adapter on the second. Applying `firstFactorFunctor`
sends its component to `id_A ⊗ α_B`; the inverse component is
`id_A ⊗ α_B⁻¹`. These are equivariant smooth maps because `GL_k` acts on the
first factor only and the adapter maps are linear on the entire second carrier.
The functor preserves their inverse laws.

The Lean proof composes these two natural isomorphisms and supplies the result
to `Nonempty`. Thus at `(A,B)` the final forward formula is

```text
[v ⊗ w] ↦ v ⊗ α_B([w]).
```

Its inverse is first `id_A ⊗ α_B⁻¹`, then the tensor-to-localization map.
Every element of the ordinary tensor product is a finite sum of pure tensors,
so these formulas and the published linear maps determine both directions on
the whole carrier. The inverse laws hold on the whole quotients; no dimension
or surjectivity-only argument substitutes for an inverse.

For any morphism `(f,g) : (A,B) ⟶ (A',B')`, the tensor quotient comparison
sends the class of `v ⊗ w` to `f(v) ⊗ [g(w)]` along either route. Adapter
naturality gives
`D_m(g)(α_B([w])) = α_B'([g(w)])`. Hence the two final composites agree as
actual intertwiners; the target morphism is precisely
`f ⊗ D_m(g)`. In Lean this naturality and the inverse naturality are preserved
by `NatIso.prod`, `Functor.isoWhiskerRight` and composition. The theorem
quantifies all morphisms of the product category at once.

## Normalization, iteration and boundary ranks

The reused adapter constructs both maps of the full-upper quotient comparison,
rather than assuming an unproved derivative theorem. For `m = n+1` it first
identifies the full-upper quotient with the same quotient after actual
restriction to the mirabolic subgroup. It then iterates the proved normalized
one-step `TopLocalization.stepIso` in the inverse direction, taking the largest
rank first. Each step sends a full-upper class to the smaller-upper class of
the radical class of the same vector; its inverse flattens the classes.
The underlying `LocalizationTower` uses two quotient lifts and proves both
inverse laws. `TopLocalizationData` proves the actual subgroup join, positive
character restrictions and determinant-one identities. These identities make
the published inverse-half twist trivial on the next upper subgroup, so the
same relation span and the same positive character are retained.

The iteration follows exactly `phiMinusIterate T ψ 0 n`, then attaches the
proved terminal `mirabolicZeroIso`, whose output is the actual normalized
`Mirabolic.psiMinus T 0`. Rank transport uses equality elimination on the
published `generalLinearRankCast`; the exact
`generalLinearDerivative_top_succ` equation accounts for the final cast from
`m-m` to zero. No untwisted replacement, new rank convention or Haar-modulus
identification is introduced. Naturality of every lower map is preserved by
this iteration and transport.

All boundary ranks are included by the same final composition:

- At `m = 0`, `topDerivative T ψ 0` is the identity. The published adapter
  uses the rank-zero equivalence, with forward map `[w] ↦ w` and inverse the
  quotient map. The final formula is `[v ⊗ w] ↦ v ⊗ w`. The actual partial
  quotient retains the whole carrier, as also recorded by the unchanged
  `partialDerivativeZeroIso`. The final proof does not require a separate
  call to that boundary theorem.
- At `m = 1`, the upper group is trivial. There are zero Phi-minus steps
  and the actual normalized Psi-minus after restriction to `P_1`. The
  terminal proof identifies the actual upper and radical subgroups of `P_1`
  and uses their quotient universal properties, preserving the whole `B`
  carrier and all its multiplicities.
- At `k = 0`, `A` is an arbitrary smooth representation of the subsingleton
  group `GL_0`. Its carrier is unrestricted. Tensoring with the identity of
  `A` keeps every tensor multiplicity, including when `k = m = 0`.

A subsingleton acting group only forces its action to be the identity. Neither
`A` nor `D_m(B)` is assumed to have a subsingleton or one-dimensional carrier.
All actual smooth categories use `SmoothRep.{0,uF,uV}` without `ULift` or
saturating the carrier universe to `max uF uV`.

## Sources and proof provenance

The source statement is Zelevinsky, *Induced representations of reductive
p-adic groups II. Irreducible representations of GL(n)* (1980), registered
`zelevinsky-1980-induced-ii`, original PDF SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Proposition 3.7(a), printed p.182 / PDF p.19, uses ordinary exterior tensor
products and the top derivative. Its page was read, including the surrounding
partial-localization definition and the cited BZ77 1.9(c),(g). Formalizing its
equality as a natural isomorphism of actual functors is the existing target's
internal categorical packaging.

The quotient conventions are Bernstein–Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), registered
`bernstein-zelevinsky-1977-induced-i`, original PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original was read at §1.8(b), printed pp.444–445 / PDF pp.5–6, for the
relation-span quotient and negative inverse-half factor; Proposition 1.9(c),(g),
printed p.445 / PDF p.6, for transitivity and commuting with tensoring;
§3.1, printed p.450 / PDF p.11, for the actual mirabolic and radical;
§3.5 with footnote 2, printed p.452 / PDF p.13, for the decreasing-rank
Phi-minus iteration ending in Psi-minus; and §4.3, printed p.454 / PDF p.15,
for the zeroth derivative and restriction from GL. The negative exponent was
also visually checked. The supplied originals' hashes were verified; the
previous bounded search found no source-specific errata in the supplied
literature/index/notes.

The proof follows those quotient constructions through independently accepted
and published internal helpers. It does not assume the source derivative or
transitivity claims as Lean premises. The binary tensor helper proves its
maps directly. The normalized adapter specializes the proved generic
supplied-twist localization tower and composes its actual inverses. The final
Lean code adds only the identity/product natural isomorphism, application of
the actual first-factor tensor functor, composition and the `Nonempty`
constructor. There is no additional general derivative hypothesis.

The following independently accepted and published modules were checked before
reuse. The complete paired helper bodies, source conventions and full exclusion
audits were inspected; the current pairs agree with those audited publications.
They are imported by Lean name.

| Module under `Langlands.Representation` | Accepted supporting publication | Use in this proof chain |
| --- | --- | --- |
| `Derivative.PartialDerivativeTensorLocalization` | Worker 288, Reviewer 5331; Library `7d8c1355c088b76a992b0af1690748d5ae7147b5` | The two binary tensor quotient lifts, inverse laws, equivariance and both-variable naturality |
| `Derivative.TopLocalizationComparison` | Worker 1004, Reviewer 5777; Library `6cb15022e66f7f1f171e7e8d563e74b92072e5ba` | All-rank adapter used by the final composition |
| `Derivative.TopLocalizationStep` | Worker 1004, Reviewer 5706; Library `42ebad9dec7efaf48307e0b6085168e104486dfb` | Actual normalized one-step quotient comparison |
| `Derivative.TopLocalizationMirabolicZero` | Worker 1004, Reviewer 5719; Library `c5eebf94883144ce00adc4e252995c28082f08a7` | Terminal normalized Psi-minus comparison |
| `Derivative.TopLocalizationBoundary` and `Derivative.TopLocalizationRestriction` | Library `47d510a700120ee55273befb9e9cfbff513b1eb4` | Rank-zero full-carrier boundary and actual GL-to-mirabolic subgroup-copy equivalence |
| `Derivative.TopLocalizationData` | Accepted and published before the one-step construction | Elementary matrix subgroups, characters and determinant identities |
| `Jacquet.LocalizationTower` | Reviewer 5607; Library `a471b56846d22482cc30a47a96315f2d487b8c01` | Nested/single quotient inverse lifts and supplied-twist compatibility |
| `Jacquet.LocalizationTransport` | Accepted and published before the tower and concrete adapters | Inverse quotient lifts under subgroup and character transport |

## Import and condition-by-condition independence audit

The direct project imports are `Derivative.PartialDerivativeTensorLocalization`
and `Derivative.TopLocalizationComparison`. Recursive traversal of actual import
declarations gives exactly 93 project imports, excluding this final entry
module; the complete list appears below. At Library
`2d873b3cb17c7405c7a7212a3744ed724403d313`, every imported Lean/Markdown pair
matches the workspace byte for byte and is unchanged from the completed audit
at `6cb15022e66f7f1f171e7e8d563e74b92072e5ba`. The adapter's 92 imports match the
previously completed helper audits unchanged, and the new adapter pair itself
matches its frozen reviewed and published files. Adding the direct tensor import
introduces no module beyond that closure. The target retains Lean SHA256
`30c22587bab476fab8c6a190841b30c41f8dfa20b9f40b0187254c3f53227f41` and
Markdown SHA256
`e21ce266515ce4c853255f63bd98c8dd5bb097ded93fec62c9c329415b5e8c15`.
Its entire 62-import closure is unchanged.

The actual mathematical chain consists of relation-span quotient universal
properties, tensor universal properties, induced linear maps, smooth restriction
and quotient transfer, elementary matrix/subgroup/character/determinant
identities, the supplied inverse-half characters in the unchanged minus
functors, their derivative recursion and rank equations, and elementary
categorical natural-isomorphism operations. The target packaging imports the
existing `Tensor.OneFactor` construction; no binary normalized-induction module
is needed. The entire target, Partial, Iteration, MirabolicMinus, OneFactor,
Finite and CharacterLocalization pairs were read in the earlier audits; their
used definitions and complete shared-helper proof bodies were checked.

Some imported modules contain generic finite-length/admissibility predicates,
arithmetic field/residue-degree finranks, the Fourier `IsSelfDual` proposition,
Whittaker prerequisite proposition definitions, or elementary linear functional
and matrix-coefficient definitions. None supplies an excluded representation
finiteness, representation duality or consumer conclusion. The measure results
in `MirabolicQuotientMeasure` are unused; only its elementary matrix facts feed
the data helper. `LocalizationTransport`'s scalar-vanishing theorem is unused.
The current `NormalizedCharacter` includes a published import of
`Topology.CompactNormCharacter`. That helper pair imports only Mathlib and
proves the compact-character result by bounded powers/inverses; its historical
`RankinSelberg.LastRowReduction` namespace introduces no consumer dependency.
The actual graph, including that addition, was checked.

All 38 distinct excluded task IDs from the full host objective are retained
below. Each exclusion applies to the mathematical conclusions, proof successors,
transitive prerequisites and downstream consequences, as specified by the host.
The source scan for excluded names and IDs has no hits in the Lean closure;
that corroborates the inspected proof bodies and provenance rather than
replacing their audit. No pending candidate, statement definition or private
draft is used as a proved premise.

| Excluded family and parent task references | Final proof and shared-helper audit |
| --- | --- |
| `SegmentHeadProductIrreducibility` (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`); `GenericSegmentProductUniqueness` (`30341ae4-65f2-4a0e-9283-763db01a409e`); individual special-head/reverse-socle (`67279e36-f3c2-42e3-9302-11729784042e`) and segment-socle/reverse-head (`4ca79bbd-589e-476b-9f65-661e799984b5`) existence | No segment, head or socle module occurs. The tensor inverse is a quotient-valued bilinear lift, and the adapter inverse uses quotient transport and the supplied-twist tower universal properties. |
| Multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion (`8252833d-c269-41a9-824c-5879e531b23b`) | No multisegment, ordering or coverage theorem occurs. The two maps send nested representatives to single representatives and back. |
| Tempered uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`), `SquareIntegrableLanglandsClassification` (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion (`bf433f0a-921a-428c-b0c0-6475438125ac`), analytic segment classification (`aca8805b-054f-4d56-8045-12db7f623404`), `SegmentSpecialEssentialSquareIntegrability` (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`) | No classification or square-integrability input occurs. Every original module carrier is arbitrary. |
| `UnlinkedSegmentSocleProductIrreducible` (`23e98d90-6055-4e35-91a9-b0f5d8a84961`), `LinkedSegmentSocleReverseProductStructure` (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`), `LinkedSegmentSoclePairReducible` (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`), `SegmentSocleProductIrreducibility` (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`), juxtaposed structure and quotient-Hom (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`) | No socle, representation product-structure, reducibility or quotient-Hom theorem occurs. |
| Adjacent socle commutation (`e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`), two-segment commutation (`426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`), linked gluing (`c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`), `OrderedMultisegmentSocleExistence` (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`) | No socle commutation, gluing or exhaustion module or theorem occurs. |
| `SegmentFullJacquetFormula` (`ed48ae06-964c-4c84-9e62-978f5a953ca7`), `SegmentHeadJacquetFormula` (`55ad1e10-62d8-46b7-a081-909ef0056426`), `SegmentSocleJacquetFormula` (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`), `SegmentSpecialJacquetExponentNormFormula` (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`); all segment derivative formulas and parent six-statement parts (b), (d), (e), (f) | No segment formula is used. General localization supplies the relation quotient, and ordinary restriction is its exact published definition. |
| `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), `TwoSupercuspidalProductStructure` (`ab61f565-1427-4746-ba77-46097563e962`); Ze80 §§3.5, 9.6, Theorems 4.2, 9.7 and 9.3 | No product criterion, segment derivative, analytic theorem or unproved BZ77 derivative result is used. No Haar bridge is needed. |
| `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc-d2b4-4072-80d1-6370870a4a26`), `LeviCuspidalCoinvariantFinitenessStatement` (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`), the dependent mirabolic finite-length route (`5428fe2c-013c-482d-aa6e-7df43e7191aa`), `SupercuspidalCoinvariantFinitenessStatement` (`62de5903-b616-4b5c-88eb-a066b77c5467`) | No representation-finiteness input occurs. The imported finite-length predicate and arithmetic degrees described above are unused. |
| Proper-derivative vanishing and finrank-one conclusions of `SupercuspidalDerivatives` (`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) | No classification module occurs. Neither UpperUnipotentCharacterFactorization nor TopDerivativeCoinvariantComparison, whose closure reaches the excluded host, is imported. No derivative dimension is used. |
| Plus, adjunction, representation duality, derivative filtration, pairing, or unproved general derivative comparisons | No such theorem is assumed. The tensor isomorphism and all-rank adapter are independently published; the latter is constructed from one-step, terminal, restriction and boundary equivalences using derivative recursion and categorical composition. The final proof tensors that adapter with the identity and composes it with the tensor isomorphism. The generic tower proves its own quotient lifts; no unproved general derivative result is a premise. |


No split weakens these exclusions. The tensor helper and adapter were submitted
and reviewed under the inherited full restrictions. In particular the separate
normalization bridge under the excluded two-supercuspidal product host is not
imported or used: this proof retains the published explicit inverse-half
characters and needs no Haar comparison. The all-character/degenerate-character
finiteness consumers, the positive two-block Jacquet comparison and every
segment consumer remain outside the mathematical dependency chain.

### Complete transitive project import list

The following list includes the two direct project imports and excludes
`Langlands.Representation.Derivative.PartialDerivativeTensorProof`.

```text
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
Langlands.Representation.Derivative.PartialDerivativeTensorStatement
Langlands.Representation.Derivative.TopLocalizationBoundary
Langlands.Representation.Derivative.TopLocalizationComparison
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.TopLocalizationMirabolicZero
Langlands.Representation.Derivative.TopLocalizationRestriction
Langlands.Representation.Derivative.TopLocalizationStep
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.OneFactor
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
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
