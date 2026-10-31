# Binary exterior tensors and partial localization

This internal construction is the tensor quotient step toward Zelevinsky 1980,
Proposition 3.7(a), printed page 182 (PDF page 19). It compares the published
partial localization of the raw binary exterior tensor with the first factor
tensored with the full upper-unipotent character coinvariants of the second
factor. It does not identify those coinvariants with the normalized top
derivative.

The forward map sends `[v ⊗ w]` to `v ⊗ [w]`. Its inverse sends
`v ⊗ [w]` to `[v ⊗ w]`. Both are constructed from the universal property of the
actual character quotient. The first map descends the tensor of the identity
with the second quotient map. The inverse first descends the second variable of
the quotient-valued bilinear tensor map and then applies the binary tensor
universal property. Their composites are the identity by quotient and tensor
extensionality. The same extensionality proves equivariance for `GL_k` and
naturality for an arbitrary pair of intertwiners.

These are direct constructions from the relation spans in
`Derivative.Partial` and the universal property in `Jacquet.Localization`,
implementing Bernstein–Zelevinsky 1977, Proposition 1.9(g), printed pages
444–445 (PDF pages 5–6), without using any derivative comparison as an input.
`Tensor.CharacterLocalization.characterLocalizationEquiv` uses
`PiTensorProduct` and a product of indexed groups; the present source is the
published binary `TensorProduct` representation of `GL_k × GL_m`. The direct
two-lift construction preserves that source without an additional regrouping
adapter.

The construction allows all natural ranks, all additive characters and arbitrary
module carriers in independent universes. No positivity, finiteness,
irreducibility or nonzero hypothesis is used.

Source files already registered in the project literature collection:
`Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`
and `Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

`upperCoinvariantsFunctor ψ m` bundles the full quotient carrier as a trivial
representation of `GL_0`; smoothness holds since the whole group fixes every
vector. Its morphisms are the actual induced quotient maps. The trivial action
forgets no carrier. `localizationTensorIso` bundles the equivariant components
as an isomorphism

```
exteriorFunctor ⋙ Partial.smoothFunctor ψ k m ≅
  (𝟭 _).prod (upperCoinvariantsFunctor ψ m) ⋙ firstFactorFunctor.
```

The product category has arbitrary pairs of morphisms. The implemented
naturality proof is precisely `localizationTensorEquiv_natural` for those two
intertwiners. Specializing the coefficient field topology and `ψ.complex` gives
the raw tensor-quotient step for the exact target, with independent `uF`, `uV`
and carriers remaining in `Type uV`. This construction by itself does not prove
`PartialDerivativeTensorStatement`.

## Dependency and independence audit

The sole direct project import is the unchanged published
`Derivative.PartialDerivativeTensorStatement`. Its definitions supply the raw
binary tensor source and first-factor target. Its `Iteration` import supplies
only definitions in this unit: no ordinary derivative theorem is invoked.

The mathematical proof dependencies are `Localization.lift`,
`mk_apply_subgroup`, `mk_surjective`, `hom_ext`, `mapLinear`,
`Partial.mk_unipotent`, the published `Partial.action` and induced maps,
`PartialTensor.exterior` and `firstFactor` constructions, and Mathlib tensor
and quotient universal properties. The referenced localization laws follow
from the exact relation span and linear quotient universal property, while the
partial law is their specialization to `(1,u)`. The inherited smooth functors
use continuous restriction and surjective transfer; the new output functor has
a trivial action. No comparison, derivative vanishing, dimension, finiteness,
classification or segment theorem enters any proof.

The project import graph was followed recursively from the source files, rather
than inferred from module titles. It has the 62 modules listed below (excluding
this new module). Each edge was read from the actual `import` declarations.
Every imported Library file is unchanged. The full task exclusion set binds
this internal helper and any consumer; the checks apply as follows.

| Binding exclusion | Import and proof dependency finding |
| --- | --- |
| Special-head and generic-segment product irreducibility and uniqueness | Neither their statement/proof modules nor their conclusions occur. |
| Multisegment, ordered strong-head, quotient coverage, ordered conversion, tempered, square-integrable, regular and socle exhaustion/classification | None occurs; no exhaustion or existence theorem is a proof input. |
| Individual segment head/socle existence, analytic segment classification and special square-integrability | None occurs; no segment construction is a proof input. |
| Unlinked/linked/adjacent/two-segment socle irreducibility, reducibility, commutation, gluing, juxtaposed structure, quotient-Hom and ordered multisegment socle existence | None occurs, directly or through any imported theorem. |
| Two-supercuspidal product structure/irreducibility, segment derivative formulas and all segment Jacquet or exponent formulas; excluded parent clauses (b),(d),(e),(f) | None occurs. The proof uses the actual localization definitions and proves its maps from their relation spans. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker coinvariant finiteness and the prohibited mirabolic finite-length route | None occurs; no finite-length or finite-dimension theorem is a proof input. |
| `SupercuspidalDerivatives` proper-derivative vanishing and finrank-one conclusions | Neither occurs, and no top-derivative comparison helper is imported here. |
| Pending or merely accepted but unpublished BZ77 derivative inputs | No such input is used. The construction is proved directly from published quotient and tensor APIs. |

The imported smooth admissibility and matrix-coefficient laws are elementary
infrastructure already in the fixed target closure. They supply no prohibited
consumer conclusion. In particular, the tensor proof does not use admissibility
or any finiteness claim. Ordinary derivative normalization, rank transport,
transitivity and the final top-derivative identification remain separate proof
obligations, outside this construction.

The complete project closure, relative to `Langlands/` and with `.lean` omitted,
is:

```text
Group/GL/Basic
Group/GL/Mirabolic
Group/GL/MirabolicRadical
Group/GL/Nonarchimedean
Group/GL/NonarchimedeanStatement
Group/GL/NormalizedCharacter
Group/GL/Padic
Group/GL/RankMaps
Group/GL/UpperUnipotent
HarmonicAnalysis/Basic
HarmonicAnalysis/CharacterTransport
LocalField/Canonical
LocalField/Definitions
LocalField/Normalization/Definitions
LocalField/Normalization/Proof
LocalField/Normalization/Statement
LocalField/Topology
Representation/Category/Basic
Representation/Category/Twist
Representation/Derivative/Iteration
Representation/Derivative/MirabolicCharacter
Representation/Derivative/MirabolicMinus
Representation/Derivative/Partial
Representation/Derivative/PartialDerivativeTensorStatement
Representation/Dual/Definitions
Representation/Jacquet/Coinvariants
Representation/Jacquet/Localization
Representation/Jacquet/SmoothTwist
Representation/MatrixCoefficient/Definitions
Representation/MatrixCoefficient/LawsProof
Representation/MatrixCoefficient/LawsStatement
Representation/Smooth/Admissibility/CofinalProof
Representation/Smooth/Admissibility/CofinalStatement
Representation/Smooth/Definitions
Representation/Smooth/SmoothPart/BasicProof
Representation/Smooth/SmoothPart/BasicStatement
Representation/Smooth/SmoothPart/Definitions
Representation/Smooth/Transfer/PullbackProof
Representation/Smooth/Transfer/PullbackStatement
Representation/Smooth/Transfer/SubquotientProof
Representation/Smooth/Transfer/SubquotientStatement
Representation/Tensor/OneFactor
Representation/Twist/AdmissibilityProof
Representation/Twist/AdmissibilityStatement
Representation/Twist/AlgebraProof
Representation/Twist/AlgebraStatement
Representation/Twist/ContinuousCharacterProof
Representation/Twist/ContinuousCharacterStatement
Representation/Twist/Definitions
Representation/Twist/RealPower
Representation/Twist/SmoothProof
Representation/Twist/SmoothStatement
Representation/Twist/SubquotientDefinitions
Representation/Twist/SubquotientProof
Representation/Twist/SubquotientStatement
Representation/Whittaker/Algebraic
Representation/Whittaker/CharacterChange
Representation/Whittaker/EntrywiseCharacter
Representation/Whittaker/GeneralLinear
Representation/Whittaker/PrerequisiteInterfaces
Representation/Whittaker/PrerequisitesStatement
Topology/Nonarchimedean/Subgroup
```
