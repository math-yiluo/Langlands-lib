# Homogeneity of left mixed products

Authors: Worker 1070 (Lean statement and draft Markdown) and Worker 1129
(independent source and Library check, revised Markdown, import closure audit
at Library commit `a9fde2164dfeae002c8c27324c18bdcd395f447d`).

This module states one proposition and proves nothing. It records
Zelevinsky's proposition that the left mixed product of an arbitrary
representation of `GL_k` with a homogeneous representation of a mirabolic
group is again homogeneous. It is an unproved assertion.

## The declaration

The module `Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`
imports only `Langlands.Representation.Derivative.Homogeneity` and
`Langlands.Representation.Mirabolic.MixedProducts`. It declares, in the
namespace `Langlands.Derivative`,

```lean
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

def LeftMixedProductHomogeneity : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r : ℕ) (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic r F.Carrier)),
    IsHomogeneous T ψ τ →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ))
```

Its full name is `Langlands.Derivative.LeftMixedProductHomogeneity.{uF,uV} F T`.
The universe parameters are exactly `uF` (the field) and `uV` (the input
carriers), in that order, and they are independent. The prime `p`, the p-adic
field `F` and the topology datum `T` are arbitrary. The proposition installs
the supplied topology `T.topology`; no canonical topology is substituted.

For every unitary additive character `ψ` of `F`, all ranks `k r : ℕ`, every
smooth complex representation `ρ` of `GL_k(F)` and every smooth complex
representation `τ` of `GeneralLinear.mirabolic r F.Carrier` (the source's
`P_(r+1)`), both with carriers in `Type uV`: if `τ` is homogeneous for `ψ`,
then the actual left mixed product
`(T.leftMixedProductFunctor k r).obj (ρ, τ)`, a representation of
`mirabolic (k + r)` (the source's `P_(k+r+1)`) with carrier in
`Type (max uF uV)`, is homogeneous for the same `ψ`.

There are no other premises. The rank `k = 0` is included, and `ρ` and `τ`
may be zero, reducible, of infinite length or infinite-dimensional. No
admissibility, finite length, irreducibility, nonvanishing, exactness,
derivative-detection, plus-functor or classification hypothesis appears.

## The ingredients

All ingredients are published Library declarations; none is redefined here.

- `UnitaryAdditiveCharacter` bundles continuity and nontriviality, so `ψ`
  ranges over the nontrivial continuous unitary additive characters of `F`
  for the topology `T.topology`. Bernstein–Zelevinsky fix one such character
  in BZ77 §3.1; the proposition quantifies over every choice. The same `ψ`
  is used on both sides.
- `GeneralLinear k F.Carrier` is `GL_k(F)`. `GeneralLinear.mirabolic r F.Carrier`
  is the subgroup of `GL_(r+1)(F)` of matrices with last row `(0, …, 0, 1)`,
  the source's `P_n` for `n = r + 1`. There is no `P_0`.
- `T.leftMixedProductFunctor k r`
  (`Langlands.Representation.Mirabolic.MixedProducts`) is the published actual
  functor `GL_k × P_(r+1) ⥤ P_(k+r+1)` of BZ77 §4.12 case (II). On objects it
  is normalized compact induction, from the inducing subgroup of block
  matrices `[a Z; 0 p]` with `a ∈ GL_k`, `p ∈ P_(r+1)`, of the external tensor
  product `ρ ⊠ τ`, twisted by the total source character
  `χ_L(a,p) = ν_k(a)^((r+1)/2) ν_(r+1)(p)^(-k/2)` with `ν_n = |det|_F`. In
  case (II) the source twist is `ε = 1`, and no extra twist is added. The
  target carrier universe is `max uF uV`. No definition branches on `k` or
  `r`; at `k = 0` the inducing subgroup is the whole group and `χ_L = 1`.
- `level T ψ A` (`Derivative.Homogeneity`), for a representation `A` of
  `mirabolic N`, is `Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1)`:
  the greatest order `j` with `0 < j ≤ N + 1` whose derivative
  `(mirabolicDerivativeOfOrder T ψ N j _).obj A` has a nontrivial carrier, or
  zero if there is none. The derivative of order `j` is `j - 1` applications
  of the published determinant-normalized `Φ⁻` followed by `Ψ⁻`, after the
  equality transport of the source rank. This is the source's
  `τ^(j) = Ψ⁻ (Φ⁻)^(j-1) τ`.
- `IsHomogeneous T ψ A` says that every nonbottom invariant subspace `U` of
  `A` satisfies `level T ψ (SmoothRep.subrepresentation A U) = level T ψ A`,
  where `SmoothRep.subrepresentation A U` is `U` with its restricted smooth
  action. On the conclusion side it is applied at carrier universe
  `max uF uV`; the definitions of level and homogeneity are
  universe-polymorphic.

## Original sources

The proposition is A. V. Zelevinsky, *Induced representations of reductive
p-adic groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4)
13 (1980), 165–210 (literature ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`), file
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
Printed page = one-based PDF page + 163.

- §4.3, printed p. 184 / PDF page 21: the level `λ(τ)` of `τ ∈ Alg P_n` is
  the maximal `k` with `τ^(k) ≠ 0`.
- §5.1, printed p. 187 / PDF page 24: `τ ∈ Alg P` is homogeneous if
  `λ(σ) = λ(τ)` for each nonzero submodule `σ ⊂ τ`. This is
  `IsHomogeneous`.
- §5.3, printed pp. 187–188 / PDF pages 24–25: "PROPOSITION. — Let
  `τ ∈ Alg P_n` be homogeneous and `ρ ∈ Alg G_m`. Then the representation
  `ρ × τ ∈ Alg P_(n+m)` is homogeneous (for the definition of `ρ × τ` see
  [1], 4.12)." Here `[1]` is BZ77. The proposition of this module is this
  statement with the source's `m` renamed `k` and `n = r + 1`.

The lower source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472 (literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).
Printed page = one-based PDF page + 439.

- §4.12, printed pp. 456–458 / PDF pages 17–19: case (II) defines
  `ρ × τ ∈ Alg P_(k+m)` for `ρ ∈ Alg G_k`, `τ ∈ Alg P_m`, with `ε = 1`.
- §4.14(a), printed p. 458 / PDF page 19: `(ρ × τ)^(i) = ρ × τ^(i)` for
  `i ≥ 1`.
- §1.8(a), printed p. 444 / PDF page 5: `I_(U,θ)` is induction by all smooth
  functions with the stated transformation law, and the compactly induced
  `i_(U,θ)` is its subrepresentation on the functions compactly supported
  modulo `P = MU`.
- §3.2, printed p. 451 / PDF page 12: `Ψ⁻ = r_(V,1)`, `Φ⁻ = r_(V,θ)`,
  `Ψ⁺ = i_(V,1)`, `Φ⁺ = i_(V,θ)` and `Φ̂⁺ = I_(V,θ)`. Proposition (a): all of
  `Ψ⁻, Ψ⁺, Φ⁻, Φ⁺, Φ̂⁺` are exact. (b): `Ψ⁻` is left adjoint to `Ψ⁺`, and
  `Φ⁺` is left adjoint to `Φ⁻`. (c): `Φ⁻` is left adjoint to `Φ̂⁺`. (f): in
  `Id → Φ⁻Φ⁺ → Φ⁻Φ̂⁺ → Id`, built from the adjunction maps of (b) and (c)
  and the map induced by the natural embedding `Φ⁺ → Φ̂⁺`, all three maps
  are isomorphisms and the composite is the identity. So the
  compact-induction functor `Φ⁺` and the smooth-induction functor `Φ̂⁺` are
  different functors, adjoint to `Φ⁻` on opposite sides.

The Library already states BZ77 §4.14(a) for the same functor as
`Langlands.Derivative.LeftMixedProductDerivative`
(`Langlands.Representation.Derivative.MixedProductDerivativeStatement`,
task `f9454f68-5916-40af-9970-3425330b4a97`). At Library commit `a9fde216`
that statement has no published proof, and this module does not import it.

Worker 1070 compared text extraction of Ze80 pp. 187–188 with the page images
for the statement and proof of §5.3. Worker 1129 independently read the text
extraction of Ze80 pp. 170 and 187–188 and BZ77 pp. 444, 451 and 456–458,
and checked rendered page images of Ze80 pp. 187–188 and BZ77 p. 451 for the
hats and arrows quoted below. At Library commit `a9fde216` there is no
`notes/errata/` tree, and the project literature collection has no errata
file for either source. This reports that bounded search only.

**Source proof (documentation, not formalized here).** Zelevinsky's
argument uses the smooth-induction functor `Φ̂⁺` of BZ77 §3.2, not the
compact-induction functor `Φ⁺`, at every step below. Write `l` for the level
(Zelevinsky writes `k`).

- Ze80 §5.1, printed p. 187. For `τ ∈ Alg P` with `λ(τ) = l`, condition (1),
  "`τ` is homogeneous", is equivalent to condition (3), "`τ` may be embedded
  into `(Φ̂⁺)^(l-1) ∘ Ψ⁺(τ^(l))`". The proof rests on the formula, from
  BZ77 §3.2(b) and (c),
  `(★) Hom(σ, (Φ̂⁺)^(l-1) ∘ Ψ⁺(τ^(l))) = Hom(σ^(l), τ^(l))` for any
  `σ ∈ Alg P`. Here `σ^(l) = Ψ⁻(Φ⁻)^(l-1)(σ)`, and (★) uses the right
  adjunction `Φ⁻ ⊣ Φ̂⁺` `l - 1` times and `Ψ⁻ ⊣ Ψ⁺` once. The compact
  `Φ⁺` is left adjoint to `Φ⁻` instead, so these adjunctions do not give (★)
  with `Φ⁺`. The unhatted `Φ⁺` occurs in §5.1 only in condition (2), through
  the submodule `τ_l = (Φ⁺)^(l-1) ∘ Ψ⁺(τ^(l)) ⊂ τ` of BZ77 §3.5. §5.3 does not
  use that condition. For (3) ⇒ (1): if `0 ≠ σ ⊂ τ`, then the left side of
  (★) is nonzero, so `σ^(l) ≠ 0`. Exactness of the derivative gives
  `σ^(j) ⊂ τ^(j)`, so `λ(σ) ≤ λ(τ) = l`; hence `λ(σ) = l`. The direction
  (1) ⇒ (3) also uses BZ77 §3.2(f).
- Ze80 §5.3, printed pp. 187–188. Let `ρ ≠ 0`. By BZ77 §4.14(a),
  `(ρ × τ)^(i) = ρ × τ^(i)` for `i ≥ 1`, "so `λ(ρ × τ) = λ(τ)`". This also
  needs `ρ × θ ≠ 0` for nonzero `θ`, which the source leaves implicit. By
  §5.1(3), `τ ↪ (Φ̂⁺)^(l-1) ∘ Ψ⁺(τ^(l))`, hence
  `ρ × τ ↪ ρ × (Φ̂⁺)^(l-1) ∘ Ψ⁺(τ^(l))`. Zelevinsky then notes the
  embedding `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)` for each `σ ∈ Alg P_N` ("the proof of
  this is straightforward"). In the source this is an embedding, not an
  isomorphism. It follows that
  `ρ × (Φ̂⁺)^(l-1) ∘ Ψ⁺(τ^(l)) ↪ (Φ̂⁺)^(l-1) ∘ Ψ⁺(ρ × τ^(l)) = (Φ̂⁺)^(l-1) ∘ Ψ⁺((ρ × τ)^(l))`.
  This step applies the displayed embedding `l - 1` times and uses that
  `Φ̂⁺` preserves embeddings. It also needs a comparison of `ρ × Ψ⁺(θ)` with
  `Ψ⁺(ρ × θ)` for `θ ∈ Alg G_(n-l)`, where the second product is the product
  of general linear representations. The source does not state this
  comparison separately. So `ρ × τ` embeds into
  `(Φ̂⁺)^(l-1) ∘ Ψ⁺((ρ × τ)^(l))`, and §5.1, (3) ⇒ (1), concludes.

None of these inputs is asserted, assumed or imported by this module; each
is an obligation of the proof task. The Library's published
`Langlands.Derivative.Mirabolic.phiPlus`
(`Langlands.Representation.Derivative.MirabolicPlusNormalization`, not
imported here) is the normalized compact-induction functor `Φ⁺`. At Library
commit `a9fde216` there is no mirabolic `Φ̂⁺`. There is only the generic
smooth induction `Langlands.Induction.smoothInductionFunctor`
(`Langlands.Representation.Induction.Definitions`). A proof that follows the
source route must therefore construct `Φ̂⁺` with the source normalization.
It must also prove the right adjunction `Φ⁻ ⊣ Φ̂⁺` for the published `Φ⁻`,
that `Φ̂⁺` preserves embeddings, and the two product comparisons above.
Otherwise it must use a different, fully proved route.

## Normalization

The imported `Φ⁻` and `Ψ⁻` are the published determinant-normalized minus
functors. They twist by the absolute value of the determinant to the power
`-1/2`, where the source uses `mod_U^(-1/2)` (BZ77 §1.8). The published
module `Langlands.Representation.Derivative.MirabolicMinusNormalization`
proves that these determinant characters equal the inverse half of the actual
radical Haar character (`psiMinusHaarInverseHalf_eq`,
`phiMinusHaarInverseHalf_eq`). It also proves that each functor equals the
corresponding unnormalized functor followed by the twist by that Haar
character (`psiMinus_haarNormalization`, `phiMinus_haarNormalization`).
This module does not import those results. They only confirm that the
derivatives in `level` carry the source normalization.

The left mixed product uses the source-prescribed determinant character `χ_L`
in place of the source's Haar modulus. `MixedProducts.md` derives `χ_L` from
the determinant of the conjugation action on the unipotent radical as
documentation, and asserts no formal Haar-modulus identity. This proposition
neither assumes nor supplies such an identity. A twist by a character does
not change which carriers are nonzero, nor the invariant-subspace lattice.
So the normalization does not change the meaning of homogeneity. This
remark explains the convention and is not proved in this module.

## Boundary cases

- **Zero inputs.** If `ρ` or `τ` has a zero carrier, the inducing tensor
  product is zero, so the product has a zero carrier and is homogeneous
  vacuously. This is why Zelevinsky's proof begins "Let `ρ ≠ 0`". The
  proposition covers these cases without a separate premise; they are not
  proved here.
- **`k = 0`.** `GL_0` is the trivial group, `χ_L = 1` and the inducing
  subgroup is all of `P_(r+1)` (`mem_leftSubgroup_zero`). Mathematically the
  product is then `τ` tensored with the carrier of `ρ`, transported along the
  published bijection `leftUnitProjection r`; this identification is not
  formalized here. In this case the proposition says that such a
  multiplicity space of a homogeneous `τ` is homogeneous. Ze80 fixes
  `G_n = GL(n, F)` for `n > 0` and `G_0 = {e}` (§1.1, printed p. 170 / PDF
  page 7), so §5.3 with `ρ ∈ Alg G_0` covers `k = 0`. The BZ77 §4.12
  notation itself assumes `1 ≤ k`. The §6.2 consumer uses `k = 0`.
- **`r = 0`.** `P_1` is the trivial group, and the product lands in
  `mirabolic k`, the source's `P_(k+1)`. No separate clause treats this
  case.

## Scope and dependencies

The proposition supplies no proof. Statement publication proves no analytic
assertion. Whatever a proof route needs from the following list is an
obligation of the proof task, not a hidden hypothesis of this proposition:
BZ77 §3.2 (exactness, and the adjunctions `Ψ⁻ ⊣ Ψ⁺` and `Φ⁻ ⊣ Φ̂⁺` for a
constructed smooth-induction `Φ̂⁺`), §4.14(a), Ze80 §5.1, the embedding
`ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)`, the `Ψ⁺` comparison, and any comparison of `χ_L`
with a Haar modulus.

This statement is a lower input to the Ze80 §6.2 homogeneity proof task
`b711af72-fdf9-4b32-a450-937911426822`, itself a lower input to ordered-socle
existence task `23189526-80b0-4828-a6d4-7ebec2cbeef5`. It uses no
conclusion, proof successor or transitive proof dependency of that task, of
socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, of analytic segment
classification `aca8805b-054f-4d56-8045-12db7f623404`, of segment-socle
product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`, of the final
segment-socle irreducibility criterion
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, of `AdjacentUnlinkedSegmentSocleSwap`
or `TwoSegmentSocleCommutation`, of the special-head product criterion
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, special-head exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`,
`SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`, `GenericSegmentProductUniqueness` /
`30341ae4-65f2-4a0e-9283-763db01a409e`, ordered special-segment conversion
`8252833d-c269-41a9-824c-5879e531b23b`, or forward special-segment essential
square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`. It uses no
segment, cuspidal or supercuspidal derivative formula (Ze80 §3.5 or §9.6),
no segment Jacquet formula and no Whittaker-finiteness result. Later proof
tasks and lower splits must preserve this exclusion set, the shared upstream
restrictions of GL Leibniz task `3238f371-e9a2-42ce-8b5d-9c4d3400ff55`
revision 2 (as carried by task `f9454f68`), and the further exclusions
recorded in their contracts.

### Import closure audit

The complete transitive project import closure was traversed in Library
commit `a9fde2164dfeae002c8c27324c18bdcd395f447d`, the base of this
contribution. It has the 73 project modules listed below. Every one has a
nonempty Markdown pair, and every pair is byte-identical between that
Library tree, the earlier Library commit `6cb15022` and the submitting
workspace. The derivative branch contains
group and functor constructions, quotient carriers, rank transports, the
finite-maximum level and the invariant-subspace homogeneity definition, with
elementary laws about them. The mixed-product branch adds the block
subgroups, determinant characters, normalized compact induction, the binary
normalized product and the external tensor product.
`Langlands.Topology.CompactNormCharacter`, imported through
`Langlands.Group.GL.NormalizedCharacter`, proves that a continuous
homomorphism to `ℝ≥0ˣ` is one on every compact subgroup. The closure contains no
socle, segment, classification, commutation, exhaustion, coverage,
derivative-filtration, derivative-detection, derivative-exactness or
Whittaker-finiteness result, and no module of any excluded task above. The
`Proof` modules in the closure prove p-adic arithmetic normalization
interfaces, matrix-coefficient laws, smooth-part laws, smoothness and
admissibility transfer, and character-twist laws; none concerns derivatives,
socles or classification.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
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
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
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
Langlands.Representation.Tensor.Finite
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
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```

### Development checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, on a
workspace equal to Library commit `a9fde216` plus this pair (diagnostic
`de799c01-9509-426a-b0fe-1e26243a77bb`), compiled the module with no errors
or warnings. The same Lean file had compiled the same way at Library commits
`6cb15022` (diagnostic `a5bd3ae8-fec6-4840-acce-e68e37627518`) and
`ddf3850e` (diagnostic `f3419807-e97c-4820-b218-634e8f15acb7`). Inspection of the declaration reported
`statement_returns_prop: true`, level parameters `uF, uV`, and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. These checks
establish elaboration and proposition kind only; they are not semantic
acceptance.
