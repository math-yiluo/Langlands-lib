# Proof of the Gelfand–Kazhdan realization of the smooth contragredient

Authors: Worker 249 and Worker 51. This module proves the published statement
`Langlands.GelfandKazhdanContragredientStatement.{uF,uV}` from
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement`. The
closing theorem is

```lean
theorem Langlands.gelfandKazhdanContragredient :
    GelfandKazhdanContragredientStatement.{uF,uV}
```

It is unapplied and keeps the statement's two independent universes: `uF` for
the p-adic field and `uV` for the carrier. It adds no hypotheses. So for every
prime `p`, every actual `F : PadicField.{uF} p` with the topology installed by
`F.canonicalNormedField`, every `n` (every positive rank `n + 1`, rank one
included), and every admissible irreducible complex representation `rho` of
`GL_(n+1)(F)` on an arbitrary `V : Type uV`, it gives an actual linear
equivalence `E : V ≃ₗ[ℂ] SmoothDual rho` with

`E (rho (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) v) = smoothContragredient rho g (E v)`

for all `g` and `v`. The theorem assumes no genericity, no supplied
equivalence, no equality of characters, and no finite-dimensionality of `V`.
The statement module is imported unchanged, and `SmoothDual rho` is the
Library's smooth part of the algebraic dual, not a renamed pullback.

## Inputs

The module imports three modules and adds no other declarations:

- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly`, by
  Worker 51, which is submitted together with this module. It contains the
  conditional theorem
  `Langlands.gelfandKazhdanContragredient_of_character_inputs`. Its two
  hypotheses are `CharacterSeparationStatement.{uF,uV,uV}` and
  `GeneralLinearConjugationDistributionTransposeStatement.{uF}`, and its
  conclusion is `GelfandKazhdanContragredientStatement.{uF,uV}`. Its paired
  Markdown describes the assembly in detail.
- `Langlands.Representation.Character.SeparationProof`, which provides the
  published theorem
  `Langlands.characterSeparation : CharacterSeparationStatement.{uG,uV,uW}`
  (Worker 203).
- `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`, which
  provides the published theorem
  `Langlands.generalLinearConjugationDistributionTranspose :
  GeneralLinearConjugationDistributionTransposeStatement.{uF}` (Worker 33).

## Implemented proof

The proof is the single term

```lean
gelfandKazhdanContragredient_of_character_inputs characterSeparation
  generalLinearConjugationDistributionTranspose
```

Here `characterSeparation` is used at the universes `.{uF,uV,uV}`. The group
`GL_(n+1)(F)` lives in `uF`, and both carriers, `V` and `SmoothDual rho`, live
in `uV`. `generalLinearConjugationDistributionTranspose` is used at `.{uF}`.
Lean infers both instantiations from the hypothesis types of the assembly.

The assembly proceeds as follows.

1. It installs the canonical field structure and the canonical topological
   structure of `GL_(n+1)(F)`: Borel measurable space, local compactness and
   the nonarchimedean group structure. It then takes the Library's normalized
   Haar measure `RankinSelberg.generalLinearHaar`, which is invariant under
   inversion, inverse transpose and conjugation by
   `RankinSelberg.generalLinearHaarSymmetries`.
2. `Langlands.characterTransport` shows that the smooth dual and the
   inverse-transpose pullback `rho.comp e` are admissible. Here `e` is the
   continuous group automorphism
   `GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier`. It also
   expresses both characters through the character of `rho`, the first by
   inverting the test function and the second by pulling it back along
   `e.symm`.
3. Irreducibility of the smooth dual comes from the published conditional
   transfer `isIrreducible_smoothContragredient_iff_of_bidual`. Its hypotheses
   are supplied by compact-open cofinality and by smooth-bidual injectivity and
   surjectivity. Irreducibility of the pullback comes from
   `isIrreducible_comp_continuousMulEquiv_iff`.
4. The character of `rho` is conjugation invariant, because the Haar measure
   is preserved by inner automorphisms. The transpose input makes it transpose
   invariant. The pullback of a test function `f` along `e.symm` equals the
   transpose pullback of the inverted `f`, so the two character formulas of
   step 2 agree. This gives
   `Character.distribution μ (rho.comp e) = Character.distribution μ (smoothContragredient rho)`.
5. The separation input turns this equality of characters of two irreducible
   admissible representations into a `GL_(n+1)(F)`-equivariant linear
   equivalence `V ≃ₗ[ℂ] SmoothDual rho`. Since the first representation is
   `rho.comp e`, the equivariance is exactly the displayed identity.

## Relation to the original source

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n, F), where F is a non-Archimedean local field* (1976),
`bernstein-zelevinsky-1976-representations-gln`, Theorem 7.3, printed/PDF
pages 57–58. The source proves that `rho^s` and the contragredient are
equivalent, where `s(g) = s_n (g^t)^(-1) s_n^(-1)`. By 2.15, 2.20 and 7.2 it
reduces this to the equality of traces. It then derives that equality from the
fact that a conjugation-invariant distribution is transpose invariant.

The implemented proof uses the inverse transpose itself, so the inner
conjugation by `s_n` never appears; the statement Markdown explains why this
convention is equivalent. The source's appeals to 2.20 and to the transpose
fact are taken by the two published inputs. The appeal to 7.2 and 2.15 is taken
by the irreducibility and admissibility arguments of steps 2 and 3. The trace
calculation is steps 2 and 4.

## Compilation

The workspace consists of the published Library commit
`910a6df80701415e9aa68c646393c66ac9bc7512` together with this pair and the
assembly pair. It was compiled in the project's pinned Lean environment,
artifact `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The local check
`cc75de6f-a869-4ef9-b5df-88fd72391cab` compiled the assembly module and then
this module with no errors and no warnings. Inspecting
`Langlands.gelfandKazhdanContragredient` showed a theorem with exactly the
universe parameters `uF` and `uV`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. Neither file contains `sorry`, `admit`
or a new axiom. The assembly Lean file is byte-identical to Worker 51's final
version (SHA-256
`7f8414c0bc83b9a99cd052171b41ec7bf7b5c9cb60735a924ff1a8bfb1df3726`).

## Exact-target validation

The closing theorem's type is the published
`GelfandKazhdanContragredientStatement.{uF,uV}`, unapplied. Neither the
statement pair `GelfandKazhdanStatement.{lean,md}` nor any module it imports
is changed. The official machine validation of this candidate is pending. It
checks the Lake build, the exact target, the unchanged statement and the
frozen inputs.

## Independent acceptance and publication

Both inputs were accepted by independent review and are published:

- Character separation: candidate `a68eef2b-3e88-46b5-ba92-6d95da98f52e`,
  version 1 (Worker 203, task `50357f3e-0d26-4004-8ca0-562b7c8c3045`). Its
  machine validation `a6327725-9d6e-41b2-93c2-fa2e9f366a01` passed the Lake
  build, exact-target, unchanged-statement and frozen-input checks. Reviewer
  2111 approved it in review `1cd9f168-e3ac-49b5-8962-3ef264ad30ac` (peer
  review `fecca99fdf80480c9e3937108c5f94a3`). It was published in Library
  commit `123284c0f07314aa4544e028a94932bf9eb256af`.
- Transpose invariance: candidate `a273f153-573e-4de5-a169-47a467c37f10`,
  version 1 (Worker 33, task `f9ba6d55-99f2-4ae7-93ad-0878f9bc7eb9`). Its
  machine validation `ec2986cb-a522-4258-a1eb-a1bb6f106588` passed the same
  four checks. Reviewer 3904 approved it in review
  `be0b16e9-53cb-4570-8d5d-3a401fa89e13` (peer review
  `cef360fb0bfe4637ad3ccfbd3b560988`). It was published in Library commit
  `910a6df80701415e9aa68c646393c66ac9bc7512`.

This module and the assembly have not yet been accepted. They await
independent semantic review. They have not yet been published either: only an
accepted candidate is published to the Library, by the Integrator.
