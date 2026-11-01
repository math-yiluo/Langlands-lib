# The right `Ψ⁻` compatibility of BZ77 4.13(c) for source `P_1`

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPsiCompatibility.{uF,uV} F T`
of the published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`.
It proves the source-rank-one case `r = 0` and supplies the explicit rank cast
used in both cases. The final clause is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsi`.

## Source and provenance

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, source ID
`bernstein-zelevinsky-1977-induced-i`. Proposition 4.13(c) on printed p.458
(one-based PDF page 19) states `Ψ⁻(τ × ρ) ≅ Ψ⁻(τ) × ρ` for `τ` on `P_m` and
`ρ` on `G_k`, functorially. Here `m = 1`: `τ` is a representation of
`P_1 = mirabolic 0`, and `Ψ⁻τ` is a representation of `GL_0` whose carrier is
all of `τ`. The product `τ × ρ` is case (III) of BZ77 §4.12 (printed
pp.456–458).

The declarations below and their proofs are derived internal content. The
proof does not follow BZ77 §7.2 (printed p.471), which refers to the
geometric lemma. It computes the radical coinvariants directly with the
published split-kernel integral.

## The explicit rank cast of the general linear group

- `generalLinearCastHom h : GL_b → GL_a` is the identity along a rank equality
  `h : a = b`, defined by `subst`. `generalLinearCastHom_apply` gives its
  entries through `Fin.cast`, and `continuous_generalLinearCastHom` gives its
  continuity.
- `reindex_generalLinearCastHom_zero`: the reindexing used by the published
  rank-zero model of the binary product undoes the cast
  `GL_(m+0) → GL_(0+m)`.
- `generalLinearRankCastIso T h`: the published rank transport
  `generalLinearRankCast T h` is isomorphic to pullback along
  `generalLinearCastHom h` (by `subst` and `Iso.refl`). The proof of the
  clause uses this to replace the published rank transport by an explicit
  pullback, in both cases.

## The target side at `r = 0`

- `rightPsiZeroTarget T k` is the target functor at `r = 0`. It applies
  `(psiMinus T 0).prod 𝟭`, then the published rank-zero model
  `binaryLeftZeroTensorFunctor (a := 0) (b := k+1) rfl` of the binary product,
  then pullback along `generalLinearCastHom (Nat.add_comm 0 (k+1))`.
  `binaryNormalizedProductFunctor 0 (k+1)` is this rank-zero model by
  definition.
- `rightPsiZeroTargetEquiv T k X` is a linear equivalence from the carrier of
  `(rightPsiZeroTarget T k).obj X` onto `X.1 ⊗ X.2`. It removes the universe
  lift. It identifies `Ψ⁻X.1` with `X.1`, because the radical of `P_1` acts
  trivially (published `psiMinus_zero_trivial`, `localizationTrivialEquiv`).
- `rightPsiZeroTargetEquiv_action`: it turns the action of
  `g ∈ GL_((k+1)+0)` into `1 ⊗ ρ(g)`.
- `rightPsiZeroTargetEquiv_natural`: for a pair morphism `φ = (φ₁, φ₂)` it
  turns the target map into `φ₁ ⊗ φ₂`.

## The clause at `r = 0`

`rightPsiCompatibility_zero T k` proves the exact clause instance

```text
Nonempty (rightMixedProductFunctor (k+1) 0 ⋙ psiMinus ((k+1)+0)
  ≅ (psiMinus 0).prod 𝟭 ⋙ binaryNormalizedProductFunctor 0 (k+1)
      ⋙ generalLinearRankCast (Nat.add_comm 0 (k+1))).
```

The proof works with these data:

- the source group `G = P_(k+2) = mirabolic (k+1+0)`;
- `r = projection : G → GL_(k+1)` and its section `s = levi`;
- the case (III) subgroup `H = rightSubgroup (k+1) 0`;
- the coefficient `σ = twist χ_R (τ ⊠ ρ)`, where `χ_R` is the published case
  (III) character.

The mixed product is `compactInduced H σ`.

1. The intersection of `H` with the radical `ker r` is trivial
   (`eq_one_of_mem_rightSubgroup_zero`). The published
   `trivialSplitKernelEquiv`, with the trivial character `θ = 1`, identifies
   the `ker r`-coinvariants of `compactInduced H σ` with `τ ⊗ ρ`. The
   `Ψ⁻` quotient is the localization at `(radical, 1)`. Its relations equal
   those of `(ker r, θ)` by `relations_congr`, since `ker r = radical`
   (`ker_projection`). The composite is `E X`.
2. The action (`hE`). For `g ∈ GL_(k+1)` the source acts by
   `|det g|^(-1/2)` (the published `Ψ⁻` normalization) times the action of
   `s(g) = diag(g, 1)`. By `trivialSplitKernelEquiv_section`, `s(g)` acts
   through `σ(s g)` and the inverse Haar modulus of conjugation on the radical.
   That modulus is `|det g|⁻¹` (published `mulEquivHaarChar_conj_levi_inv`),
   so its inverse is `|det g|`. `twist_rightInducing_levi_zero` gives
   `σ(s g) = |det g|^(-1/2) (1 ⊗ ρ(g))`. The three scalars multiply to `1`
   (`half_mul_inv_inv_mul_half`). Hence `g` acts by `1 ⊗ ρ(g)` on the model
   space. No scalar is dropped.
3. The measure data are the ones used for the published right boundary: Borel
   σ-algebras, local compactness from closedness, compact open bases and
   covers of the radical, unimodularity from
   `Haar.compactOpenCoverUnimodularity`, and a compatible quotient measure
   from `QuotientIntegration.compatibleMeasureExists`.
4. Naturality (`hEnat`) is `trivialSplitKernelEquiv_natural`. It is applied to
   the actual coefficient map of the mixed product,
   `twistIntertwining χ_R (pullbackMap rightProjection (externalMap φ₁ φ₂))`.
5. `equivOfCommonModel` combines `E X` and `rightPsiZeroTargetEquiv` into an
   equivalence of representations, because both turn the actions into
   `1 ⊗ ρ(g)`. `symm_comp_natural` gives naturality. `NatIso.ofComponents`
   with `SmoothRep.mkIso` and `MixedProductTensor.smoothRep_hom_ext` builds the
   natural isomorphism. The pullback is then replaced by
   `generalLinearRankCast` through `generalLinearRankCastIso`.

Both carriers are kept in full: the `GL_0` input `Ψ⁻τ` is the whole carrier
of `τ`, and `ρ` is an arbitrary smooth representation of `GL_(k+1)`. No unit
object or chosen vector is introduced. The theorem uses
`set_option maxHeartbeats 400000`, a finite bound.

## Imports

The only direct import is the published
`Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary`. It
supplies `trivialSplitKernelEquiv` and its section and naturality laws,
`relations_congr`, `localizationTrivialEquiv`, `psiMinus_zero_trivial`,
`twist_rightInducing_levi_zero`, `levi_mem_rightSubgroup_zero`,
`eq_one_of_mem_rightSubgroup_zero`, the radical bases and covers,
`mulEquivHaarChar_conj_levi_inv`, `equivOfCommonModel`, `symm_comp_natural`,
`half_mul_inv_inv_mul_half` and `smul_smul_smul_of_mul_eq_one`. The
transitive project import closure of this module has 144 modules: that import
and its 143 transitive project imports. The complete import closure of the clause
and its restriction audit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPsi.md`.
