# The right source-rank-one boundary of BZ77 Proposition 4.13(c)

Author: Worker 837.

This pair proves the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiBoundary.{uF,uV} F T` of the
published statement `MirabolicProductMinusCompatibilityStatement`. The entry
theorem is

```lean
theorem Langlands.Derivative.MirabolicProductMinus.rightPhiBoundary
    (T : F.TopologicalData) : RightPhiBoundary.{uF, uV} F T
```

for every prime `p`, `F : PadicField.{uF} p` and `T : F.TopologicalData`, with
independent universes `uF` and `uV`. It has no further hypotheses. The pair
proves one of the six components; it does not prove the whole statement.

## Source and correspondence

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, source ID
`bernstein-zelevinsky-1977-induced-i`. Proposition 4.13(c) on printed p.458
(one-based PDF page 19) gives, for `τ` on `P_m` and `ρ` on `G_k`, the exact
sequence

```text
0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ|P) → 0.
```

The same page adopts `P_0 = ∅`. At `m = 1` the first term is therefore zero,
and the middle and last terms are isomorphic. The published clause
`RightPhiBoundary` states this as a natural isomorphism of functors on the
product category of smooth representations of `P_1` and `GL_(k+1)`:

```text
rightPhiProduct T ψ k 0 ≅ rightPhiQuotient T k 0.
```

The left side is `Φ⁻` of the right mixed product (BZ77 4.12, case (III)), after
the rank cast `(k+1)+0 = (k+0)+1`. The right side is the left mixed product
of `Ψ⁻τ` (a representation of `GL_0`) with the restriction of `ρ` to
`P_(k+1)`, after the rank cast `0+k = k+0`. The `GL_0` input carrier is kept
in full.

In §7.2 (printed p.471), BZ77 proves 4.13(c) for `Φ⁻` with the geometric
lemma, Theorem 5.2, and leaves the details to the reader. The Lean proof below
does not use the geometric lemma. At `m = 1` the case (III) subgroup `H` of
`P_(k+2)` meets the radical `V` only in the identity. The proof uses the
semidirect decomposition `P_(k+2) = V ⋊ GL_(k+1)` together with a
`θ_ψ`-twisted relative integral over `V`. This identifies the `θ_ψ`-localization
of the induced space directly with the inducing space.

## Normalizations

No scalar is dropped. For `h ∈ P_(k+1)`, write `l = h.val ∈ GL_(k+1)`. Three
scalars occur in the action, and their product is exactly `1`:

- the published inverse-half normalization of `Φ⁻`, `|det l|^(-1/2)`;
- the case (III) inducing factor of `rightMixedProductFunctor` at `r = 0`,
  `|det l|^(-1/2)` (published `rightLeviCharacter_zero_right_apply`);
- the inverse Haar modulus of conjugation by the Levi element `diag(l, 1)` on
  the radical, `|det l|`. This is `mulEquivHaarChar_conj_levi_inv`, from the
  published `leviRadical_haarCharacter`.

`half_mul_inv_inv_mul_half` proves that the product is `1`. The action on the
source therefore becomes `1 ⊗ ρ(l)`. The action of `g` on the target becomes
the same operator `1 ⊗ ρ(g)` (`rightBoundaryQuotientEquiv_action`).

## Generic transport lemmas

These are internal and derived; each is a short Mathlib or Library argument.

- `relations_congr`: the `θ`-relations depend only on the subgroup and on the
  character values.
- `compactOpenBasis_congr` and `compactOpenCover_congr` transport a compact open
  subgroup basis or cover along an equality of subgroups.
- `mulEquivHaarChar_normalizerConj_congr` transports the Haar modulus of the
  published normalizer conjugation along an equality of subgroups.
- `mulEquivHaarChar_of_subsingleton`: on a subsingleton group every topological
  automorphism has Haar modulus `1`.
- `localizationTrivialEquiv`: if `U` acts through `θ`, the localized quotient is
  the whole carrier. `coinvariantsTrivialEquiv` is the same for trivial
  actions, with naturality `coinvariantsTrivialEquiv_map`.
- `equivOfCommonModel`: two linear identifications with one model space that
  turn both actions into the same operators give an equivalence of
  representations. `symm_comp_natural` gives naturality of the composite.
- `half_mul_inv_inv_mul_half` and `smul_smul_smul_of_mul_eq_one` are the scalar
  identities above.

## Split kernels with trivial intersection

In the setting of `Induction/SplitKernelCharacter`, assume `hI : ∀ i : I, i = 1`.

- `trivialSplitKernelEquiv` is `splitKernelCharacterEquiv` followed by
  `coinvariantsTrivialEquiv`. It is a linear equivalence from the
  `θ`-localized quotient of `compactInduced H σ` onto `V`.
- `trivialSplitKernelEquiv_section`: if `θ` is invariant under the conjugation
  `α_l`, then the class of `s(l) • f` maps to
  `Δ_N(α_l)⁻¹ • σ(s l) (image of f)`. This comes from
  `splitKernelCharacterIntegral_section`, with `Δ_I(α_l) = 1` because `I` is a
  subsingleton.
- `trivialSplitKernelEquiv_natural`: naturality in the inducing representation.

## The rank cast

- `mirabolicCastHom h : mirabolic b R →* mirabolic a R` is the identity along a
  rank equality `a = b`, defined by `subst`. `mirabolicCastHom_apply` gives its
  entries through `Fin.cast`, and `continuous_mirabolicCastHom` its
  continuity.
- `leftUnitProjection_mirabolicCastHom`: for `k = 0`, the mirabolic block of
  the case (II) projection undoes this cast.
- `mirabolicRankCastIso`: the published rank transport
  `mirabolicRankCast T h` is isomorphic to pullback along `mirabolicCastHom h`
  (by `subst` and `Iso.refl`).

## The case (III) subgroup at `r = 0`

For a commutative ring `R`:

- `levi_mem_rightSubgroup_zero`: `diag(l, 1)` lies in `rightSubgroup m 0 R`.
- `rightProjection_levi_zero`: its case (III) projection is `(1, l)`.
- `eq_one_of_mem_rightSubgroup_zero`: an element of `rightSubgroup m 0 R` in
  the kernel of `projection` is the identity. Such an element is in the radical
  (`ker_projection`), and its radical coordinates vanish by the entry
  description of the subgroup.

## p-adic inputs

- `radical_compactOpenBasis` and `radical_compactOpenCover`: the published
  radical boxes `Mirabolic.radicalBox` (compact open subgroups) form a basis at
  the identity and cover the radical. The proofs use `exists_latticeBox_subset`,
  `exists_mem_latticeBox`, `isCompact_radicalBox` and `mem_radicalBox`.
- `mulEquivHaarChar_conj_levi_inv`: conjugation by `diag(l, 1)⁻¹` scales Haar
  measure on the radical by `|det l|⁻¹`. This is the published
  `leviRadical_haarCharacter` (Group/GL/MirabolicModulusProof) evaluated at
  `l⁻¹`.
- `twist_rightInducing_levi_zero`: the normalized case (III) inducing action
  of `diag(l, 1)` at `r = 0` is `|det l|^(-1/2) (1 ⊗ ρ(l))`.

## The target side

- `rightBoundaryQuotient T k` is `rightPhiQuotient T k 0` with the rank cast
  replaced by pullback along `mirabolicCastHom`.
- `psiMinus_zero_trivial`: the radical of `P_1` is trivial, so it acts on every
  representation through the trivial character.
- `rightBoundaryTopEquiv`: evaluation at `1`, from the published
  `compactInducedTopEquiv`. At `r = 0` the case (II) subgroup of `P_(0+k+1)` is
  the whole group.
- `rightBoundaryQuotientEquiv`: the carrier of `(rightBoundaryQuotient T k).obj X`
  is linearly equivalent to `X.1 ⊗ X.2`, by evaluation at `1` followed by
  `localizationTrivialEquiv` on the first factor.
  `rightBoundaryQuotientEquiv_action` shows that `g` acts as `1 ⊗ ρ(g)`. It
  uses `leftMixedEval_covariant`, `leftLeviCharacter_zero_left` (the case (II)
  character is trivial at GL rank `0`), the triviality of `GL_0` and
  `leftUnitProjection_mirabolicCastHom`. `rightBoundaryQuotientEquiv_natural`
  gives naturality in both inputs.

## The boundary clause

`rightPhiBoundary`: fix `ψ` and `k`.

1. The split data are `G = P_(k+2)` (Lean `mirabolic (k + 1 + 0)`),
   `r = projection`, `s = levi`, and `H = rightSubgroup (k + 1) 0`. `H` is
   closed (`rightSubgroup_isClosed`) and contains the Levi elements.
   `θ` is `θ_ψ` on `r.ker = radical` (`ker_projection`). Its kernel is open
   (`mirabolicTheta_isOpen_ker`). `I = H ∩ r.ker` is trivial.
2. Measures: Borel structures on `r.ker`, `I` and `I\r.ker`. The radical box
   basis and cover give the compact open subgroup basis. The published
   `Haar.compactOpenCoverUnimodularity` makes the Haar measures `μN`, `μI` right
   invariant. The published `QuotientIntegration.compatibleMeasureExists`
   supplies a compatible quotient measure `ν`. The proof states no measure
   premise.
3. `hHaar`: `Δ(α_l) = |det l|⁻¹` for every `l`, from
   `mulEquivHaarChar_conj_levi_inv`. `hθl`: `θ_ψ` is invariant under
   conjugation by the Levi image of `P_(k+1)`, from the published
   `theta_isInvariant`.
4. For each pair `X`, the source identification
   `E X : (rightPhiProduct T ψ k 0).obj X ≃ₗ[ℂ] X.1 ⊗ X.2` is
   `Submodule.quotEquivOfEq` (by `relations_congr`, radical against
   `r.ker`) followed by `trivialSplitKernelEquiv`.
5. `hE`: `E X` turns the action of `h` into `1 ⊗ ρ(h.val)`. The published
   `phiMinus` action contributes `|det|^(-1/2)` and translation by
   `levi h.val`. `trivialSplitKernelEquiv_section` contributes `|det|`, and
   `twist_rightInducing_levi_zero` gives `|det|^(-1/2) (1 ⊗ ρ(l))`. The three
   scalars multiply to `1` (`half_mul_inv_inv_mul_half`).
   `hEnat`: `E` is natural, by `trivialSplitKernelEquiv_natural` applied to the
   published product map.
6. `equivOfCommonModel` with model `X.1 ⊗ X.2` and the operators
   `1 ⊗ ρ(g)` gives isomorphisms
   `(rightPhiProduct T ψ k 0).obj X ≅ (rightBoundaryQuotient T k).obj X`.
   They are natural by `symm_comp_natural` and the published
   `MixedProductTensor.smoothRep_hom_ext`.
7. Whiskering with the inverse of `mirabolicRankCastIso` returns to the
   published `rightPhiQuotient T k 0`.

The theorem uses `set_option maxHeartbeats 400000`, twice the default, for
elaboration of this single proof.

## Imports and complete import closure

Direct imports:
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`,
`Langlands.Representation.Induction.SplitKernelCharacter`,
`Langlands.Representation.Derivative.MinusVanishing` (only for `radicalBox`,
`isCompact_radicalBox`, `mem_radicalBox` and `exists_mem_latticeBox`),
`Langlands.Analysis.Local.QuotientMeasureExistence`,
`Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof` and
`Langlands.Group.GL.MirabolicModulusProof`.

The complete project import closure has 143 modules besides this one. It
contains the closures of `SplitKernelCharacter` and of
`MirabolicProductMinusBoundary` (except that module itself):

- `Langlands.Analysis.Local`: CompactOpenCoverUnimodularityProof,
  CompactOpenCoverUnimodularityStatement, QuotientAutomorphismProof,
  QuotientAutomorphismStatement, QuotientAverageReal, QuotientAveragingKernel,
  QuotientComplex, QuotientFunctional, QuotientMass, QuotientMeasure,
  QuotientMeasureExistence, QuotientMeasureExistenceStatement,
  QuotientMeasurePrerequisites, QuotientPositiveLifting, QuotientTopology,
  QuotientTranslation, SplitKernelQuotient.
- `Langlands.Group`: HaarModulus.
- `Langlands.Group.GL`: Basic, BlockModulus, Blocks, Maps, Mirabolic,
  MirabolicMixedProductSubgroups, MirabolicModulusProof,
  MirabolicModulusStatement, MirabolicOppositeIntersection, MirabolicProjection,
  MirabolicRadical, Nonarchimedean, NonarchimedeanStatement,
  NormalizedCharacter, OppositeBlocks, Padic, PadicBlocks, PadicOppositeBlocks,
  RankMaps, RankReindex, ReverseBlocks, UpperUnipotent.
- `Langlands.HarmonicAnalysis`: AlgebraicIntegral, AlgebraicIntegrand, Basic,
  Conductor, PadicAdditiveConductorProof, PadicHaarScalingStatement,
  PadicLatticeTopology, PadicRectangularHaarScalingProof,
  PadicScalarHaarScalingProof.
- `Langlands.LocalFactor.Harmonic`: Statement.
- `Langlands.LocalField`: Canonical, Definitions, Topology.
- `Langlands.LocalField.Normalization`: Definitions, Proof, Statement.
- `Langlands.Representation.Category`: Basic, Subquotients, Twist.
- `Langlands.Representation.Compact`: Definitions, FiniteMean,
  OrbitMeanTranslation, ProjectionProof, ProjectionStatement.
- `Langlands.Representation.Derivative`: Homogeneity, Iteration, MinusVanishing,
  MirabolicCharacter, MirabolicLatticeBox, MirabolicMinus,
  MirabolicProductMinusCompatibilityStatement.
- `Langlands.Representation.Dual`: Definitions.
- `Langlands.Representation.Induction`: BinaryProduct, BlockFactors,
  CharacterTwistProof, CompactAutomorphism, CompactAutomorphismIntegralProof,
  CompactAutomorphismIntegralStatement, CompactCoinvariantBijectivityProof,
  CompactCoinvariantBijectivityStatement, CompactCoinvariantIntegral,
  CompactCoinvariantLocalInverseProof, CompactCoinvariantLocalInverseStatement,
  CompactLocalSection, CompactLocalSectionSpanningProof,
  CompactLocalSectionSpanningStatement, CompactLocallyConstant,
  CompactQuotientProof, Definitions, InverseTranspose, OppositeParabolic,
  Parabolic, SplitKernelCharacter (this unit), SplitKernelCompact,
  SplitKernelCovariance, SplitKernelIntegral, StructuralStatement.
- `Langlands.Representation.Jacquet`: CharacterAveraging, Coinvariants,
  Localization, PositiveCharacter, SmoothTwist.
- `Langlands.Representation.MatrixCoefficient`: Definitions, LawsProof,
  LawsStatement.
- `Langlands.Representation.Mirabolic`: MixedProducts.
- `Langlands.Representation.RankinSelberg`: LastRowCompactOrbitProof,
  LastRowCompactOrbitStatement, QuotientIntegrals, ZeroRowLastRowCutoffProof,
  ZeroRowLastRowCutoffStatement.
- `Langlands.Representation.Smooth`: Definitions.
- `Langlands.Representation.Smooth.Admissibility`: CofinalProof,
  CofinalStatement.
- `Langlands.Representation.Smooth.SmoothPart`: BasicProof, BasicStatement,
  Definitions.
- `Langlands.Representation.Smooth.Transfer`: PullbackProof, PullbackStatement,
  SubquotientProof, SubquotientStatement.
- `Langlands.Representation.Tensor`: Finite, OneFactor.
- `Langlands.Representation.Twist`: AdmissibilityProof, AdmissibilityStatement,
  AlgebraProof, AlgebraStatement, ContinuousCharacterProof,
  ContinuousCharacterStatement, Definitions, RealPower, SmoothProof,
  SmoothStatement, SubquotientDefinitions, SubquotientProof,
  SubquotientStatement.
- `Langlands.Representation.Whittaker`: Algebraic, GeneralLinear.
- `Langlands.Topology`: CompactNormCharacter.
- `Langlands.Topology.CompactOpen`: ConjugationStabilizer, NeighborhoodBasis,
  NeighborhoodBasisStatement.
- `Langlands.Topology.Nonarchimedean`: Subgroup.

Every module except `SplitKernelCharacter` is a published Library module at
base `6cb15022`.

## Dependency audit

The mathematical proof dependencies are the published constructions and
theorems named above, `SplitKernelCharacter`, and Mathlib. Condition by
condition:

- Plus functors, adjunction, §4.13(d) submodule detection, general Leibniz
  proofs, filtrations, arbitrary-character finiteness, and supercuspidal and
  segment conclusions are not used. No closure module states or proves a plus
  functor, a derivative adjunction, 4.13(d), a Leibniz rule or a finite-length
  result. `Induction/StructuralStatement` (compact-induction Frobenius clauses)
  and the `*Statement` modules are imported only as proposition definitions
  through their published proofs. None is used as a hypothesis.
  `Category/Basic` defines `HasFiniteLength`, which is not used.
- `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
  `IrreducibleCoinvariantFinitenessStatement`,
  `LeviCuspidalCoinvariantFinitenessStatement` and their tasks are not in the
  closure. `Whittaker/Algebraic` and `Whittaker/GeneralLinear` contain only
  Whittaker character and coefficient-model definitions, which enter through
  the lattice-box lemmas and are not used here.
- `Derivative/MinusVanishing` is a published proof. Only its radical-box
  definitions and lemmas are used; its vanishing theorem is not used. No other
  clause of the target statement is used. The statement module is imported
  only for `rightPhiProduct`, `rightPhiQuotient` and `RightPhiBoundary`.
- No segment, socle, head, Jacquet-formula, classification or exhaustion
  result is used. No module or task in the independence lists appears in the
  closure, and Worker 127's work is not used.
- The inputs are arbitrary smooth representations. The `GL_0` carrier of
  `Ψ⁻τ` is kept in full, and no positive-rank `GL` factor is replaced by a
  rank-zero factor or a chosen unit. Every rank transport is the published
  `mirabolicRankCast` along the proved equalities `Nat.succ_add k 0` and
  `Nat.add_comm 0 k`.

Axioms: `propext`, `Classical.choice` and `Quot.sound`; universe parameters
`[uF, uV]`.
