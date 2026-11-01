# Left mixed products and the smooth plus functor

Author: Worker 1129. Module
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct`, namespace
`Langlands.Derivative.Mirabolic`. Main declarations: `leftPhiHatEmbedding`,
`leftPhiHatEmbedding_injective`, `leftPhiHatEmbeddingHom` and
`mono_leftPhiHatEmbeddingHom`.

This module constructs the embedding

```
ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)
```

for a smooth representation `ρ` of `GL_k` and a smooth representation `σ` of
the mirabolic group `P_(n+1)`. Both sides are representations of `P_(k+n+2)`.
Here `×` is the published left mixed product (BZ77 §4.12, case (II)), and
`Φ̂⁺` is Worker 749's published smooth-induction functor. The embedding is an
injective intertwiner, and a monomorphism of smooth representations.

The module states no exactness, derivative, level or homogeneity result and
assumes none. No theorem here has a proposition definition as a hypothesis.

## Source

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
source ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, §5.3,
printed pp.187–188 (PDF pp.24–25). Printed page = PDF page + 163. In the
proof of Proposition 5.3, Zelevinsky notes that for `ρ ∈ Alg G_m` and
`σ ∈ Alg P_N` one has an embedding `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)`, and says that
"the proof of this is straightforward". The source gives no proof and no
formula for the map. The source's `m` and `N` are `k` and `n + 1` here.

The functors are those of Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` (printed
page = PDF page + 439):

- §3.2, printed pp.450–451: `Φ⁻`, `Φ̂⁺ = I_(V,θ)`, and (c) `Φ⁻` is left
  adjoint to `Φ̂⁺`;
- §4.12, case (II), printed pp.456–458: the product `ρ × τ` for
  `ρ ∈ Alg G_k` and `τ ∈ Alg P_m`.

This module proves the embedding, with an explicit map. Provenance is
derived: the map and the auxiliary lemmas are not in the sources.

## Published inputs and normalizations

All objects are published Library objects, used unchanged.

- `phiHatPlus T ψ n : Rep P_(n+1) ⥤ Rep P_(n+2)`
  (`MirabolicSmoothPhiPlus`, Worker 749). Its vectors are determined by the
  values `phiHatPlusNormalizedEval T ψ n σ φ x ∈ σ` for `x ∈ P_(n+2)`
  (`phiHatPlusNormalizedEval_injective`). These satisfy
  `φ(successor g · x) = ν(g)^(1/2) σ(g) φ(x)` for `g ∈ P_(n+1)`, and
  `φ(u x) = θ(u) φ(x)` for `u` in the radical. The group acts by right
  translation. Here `ν = |det|` (`determinantNorm`), `ν^(1/2)` is
  `phiPlusCharacter`, `successor g = diag(g, 1)`, and `θ` is the
  nondegenerate character `theta ψ n` (`T.mirabolicTheta ψ n`).
- `phiMinus T ψ n : Rep P_(n+2) ⥤ Rep P_(n+1)` (`MirabolicMinus`): the
  `(V, θ)`-coinvariants, with `h` acting by `ν(h)^(-1/2)` (`phiMinusCharacter`)
  times the action of `successor h`.
- `phiHatPlusAdjunction T ψ n A σ :
  Hom(A, Φ̂⁺σ) ≃ₗ[ℂ] Hom(Φ⁻A, σ)` (`MirabolicSmoothPhiPlusAdjunction`, Worker
  749). Its inverse sends `B` to `v ↦ (x ↦ B(q(x • v)))`
  (`phiHatPlusAdjunction_symm_eval`, `rfl`), where `q` is the quotient map
  `phiMinusQuotient`.
- `T.leftMixedProductFunctor k r` (`Mirabolic.MixedProducts`): a vector `f` of
  `ρ × τ` (with `τ` on `P_(r+1)`) is determined by its values
  `T.leftMixedEval (ρ, τ) f x ∈ ρ ⊗ τ` for `x ∈ P_(k+r+1)`. The values
  satisfy `f(h x) = χ_L(a, p) (ρ(a) ⊗ τ(p)) f(x)` for `h ∈ leftSubgroup k r`
  with diagonal blocks `(a, p) = leftProjection h`
  (`leftMixedEval_covariant`). Here
  `χ_L(a, p) = ν(a)^((r+1)/2) ν(p)^(-k/2)` (`leftLeviCharacter_apply`). The
  group acts by right translation (`leftMixedProductFunctor_action`).
  `leftMixedMk` builds a vector from a covariant function that is invariant
  under an open subgroup and has compact support modulo `leftSubgroup k r`.
- From `Mirabolic.LeftMixedProductSuccessor` (Worker 1129): `leftSuccessor`,
  `leftProjection_leftSuccessor`, `leftRadical` and its projection lemmas,
  `theta_leftProjection_leftRadical`, `determinantNorm_leftSubgroup`,
  `determinantNorm_successor`, `determinantNorm_radical'`,
  `compactSpace_leftQuotient`, `isCompact_quotientSupport_of_covariant`,
  `MixedProductTensor.eq_zero_of_forall_dual_rTensor` and
  `MixedProductTensor.lid_rTensor_lTensor`.

Universes: `ρ` and `σ` have carriers in a universe `max uF uV`. Then
`Φ̂⁺(σ)`, `ρ × Φ̂⁺(σ)`, `ρ × σ` and `Φ̂⁺(ρ × σ)` all have carriers in the same
universe, as the published functors require. The lemma statements give the
universes explicitly, as `.{uV, uF}`.

## Evaluation at a point

Section `EvalAt`, for `σ` on `P_(n+1)`:

- `phiHatPlusEvalAt T ψ n σ x : Φ̂⁺(σ) →ₗ[ℂ] σ` is evaluation at
  `x ∈ P_(n+2)`, `φ ↦ phiHatPlusNormalizedEval T ψ n σ φ x`
  (`phiHatPlusEvalAt_apply`, `rfl`).
- `phiHatPlusEvalAt_action`: `ev_x(g • φ) = ev_(x g)(φ)`.
- `phiHatPlusEvalAt_one_successor`:
  `ev_1(successor g • φ) = ν(g)^(1/2) σ(g) (ev_1 φ)`.
- `phiHatPlusEvalAt_one_radical`: `ev_1(u • φ) = θ(u) ev_1(φ)` for `u` in
  the radical of `P_(n+2)`.

On a tensor product `V ⊗ Φ̂⁺(σ)`, with `(ev_x).lTensor V = id ⊗ ev_x`:

- `lTensor_evalAt_one_map_successor`:
  `(id ⊗ ev_1) ∘ (L ⊗ Φ̂⁺σ(successor g)) = ν(g)^(1/2) (L ⊗ σ(g)) ∘ (id ⊗ ev_1)`;
- `lTensor_evalAt_one_map_radical`:
  `(id ⊗ ev_1) ∘ (1 ⊗ Φ̂⁺σ(u)) = θ(u) (id ⊗ ev_1)`;
- `lTensor_evalAt_one_map`: `(id ⊗ ev_1) ∘ (1 ⊗ Φ̂⁺σ(z)) = id ⊗ ev_z`.

Each is proved on pure tensors and extended by additivity.

## The character identity

`phiMinusCharacter_mul_leftLeviCharacter_successor`: for
`h ∈ leftSubgroup k n` with blocks `(a, p)`,

```
ν(h)^(-1/2) · χ_L^(k, n+1)(a, successor p) · ν(p)^(1/2) = χ_L^(k, n)(a, p).
```

Proof: `ν(h) = ν(a) ν(p)` and `ν(successor p) = ν(p)`. The left side is
`ν(a)^(-1/2 + (n+2)/2) · ν(p)^(-1/2 - k/2 + 1/2) = ν(a)^((n+1)/2) ν(p)^(-k/2)`.
The Lean proof does this computation with real powers of the positive reals
`ν(a)`, `ν(p)`.

## The value map

Section `Product`. Fix `ρ` on `GL_k` and `σ` on `P_(n+1)`. Let
`leftPhiHatSource T ψ ρ σ` be `ρ × Φ̂⁺(σ)`, a representation of `P_(k+n+2)`
(an `abbrev`). For `f` in it and `y ∈ P_(k+n+1)`, the value map is

```
leftPhiHatValue f y = ν(y)^(-1/2) • (id ⊗ ev_1)(f(successor y)) ∈ ρ ⊗ σ.
```

- `leftMixedEval_successor_mul`: for `h ∈ leftSubgroup k n` with blocks
  `(a, p)`, `f(successor(h y)) = χ_L(a, successor p) (ρ(a) ⊗ Φ̂⁺σ(successor p)) f(successor y)`.
  This is covariance for `leftSuccessor h`, whose blocks are
  `(a, successor p)`.
- `leftPhiHatValue_covariant`: the value map is covariant for the inducing
  data of `ρ × σ`:
  `b(f)(h y) = χ_L^(k,n)(a, p) (ρ(a) ⊗ σ(p)) b(f)(y)`. The algebra is in
  `leftPhiHatValue_covariant_aux`: apply `lTensor_evalAt_one_map_successor`
  and then the character identity.
- `leftLeviCharacter_leftRadical`: `χ_L(leftRadical u) = 1`, since the
  `GL_k` block is `1` and the mirabolic block is a radical element, with
  `ν = 1`.
- `leftPhiHatValue_radical`: for `u` in the radical of `P_(k+n+2)`,
  `b(u • f) = θ(u) b(f)`. Write `successor(y) u = w successor(y)`, where
  `w = successor(y) u successor(y)⁻¹` is in the radical
  (`Jacquet.Localization.conjugate`). Then `w ∈ leftSubgroup k (n+1)` has
  `GL_k` block `1`, `χ_L(w) = 1`, and mirabolic block `p_w` in the radical
  of `P_(n+2)`. So `f(successor(y) u) = (1 ⊗ Φ̂⁺σ(p_w)) f(successor y)`. By
  `lTensor_evalAt_one_map_radical`, applying `id ⊗ ev_1` multiplies by
  `θ_n(p_w)`. This equals `θ_(k+n)(w)` (`theta_leftProjection_leftRadical`),
  which equals `θ_(k+n)(u)`, because `θ` is invariant under conjugation by
  `successor y` (`theta_isInvariant`).
- `leftPhiHatValue_exists_openSubgroup`: the value map is invariant under right
  translation by the open subgroup
  `successor⁻¹(K₀) ∩ ker(ν^(-1/2))`, where `K₀` fixes `f`.
- `leftPhiHatValue_isCompact`: its support is compact modulo
  `leftSubgroup k n`. The coset space is compact
  (`compactSpace_leftQuotient`), and a covariant, right-invariant function has
  closed projected support (`isCompact_quotientSupport_of_covariant`).
- `leftPhiHatMap T ψ ρ σ : ρ × Φ̂⁺(σ) →ₗ[ℂ] ρ × σ` is `f ↦ leftMixedMk (b(f))`,
  with values `leftPhiHatMap_eval` (`rfl`).
- `leftPhiHatMap_radical`: `leftPhiHatMap (u • f) = θ(u) • leftPhiHatMap f`.
- `leftPhiHatMap_successor`:
  `ν(h)^(-1/2) • leftPhiHatMap (successor h • f) = h • leftPhiHatMap f` for
  `h ∈ P_(k+n+1)`. Both sides have value
  `ν(y h)^(-1/2) (id ⊗ ev_1)(f(successor(y h)))` at `y`.

## Descent and the embedding

- `leftPhiHatDescent T ψ ρ σ : Φ⁻(ρ × Φ̂⁺(σ)) → ρ × σ` is the intertwiner
  induced by `leftPhiHatMap` on the coinvariants
  (`Jacquet.Localization.lift`, using `leftPhiHatMap_radical`). It is
  equivariant for the normalized `Φ⁻` action by `leftPhiHatMap_successor` and
  `phiMinus_action`.
- `leftPhiHatEmbedding T ψ ρ σ : ρ × Φ̂⁺(σ) → Φ̂⁺(ρ × σ)` is
  `(phiHatPlusAdjunction T ψ (k + n) (ρ × Φ̂⁺σ) (ρ × σ)).symm (leftPhiHatDescent T ψ ρ σ)`.
  Its intertwining property and smoothness come from the published adjunction.
  `leftPhiHatEmbedding_eval` (`rfl`): the value of `leftPhiHatEmbedding f` at
  `x ∈ P_(k+n+2)` is `leftPhiHatMap (x • f)`.
- `leftPhiHatSource_eq_zero`: if `(id ⊗ ev_1)(f(x)) = 0` for every
  `x ∈ P_(k+n+2)`, then `f = 0`. Proof: fix `x` and `z ∈ P_(n+2)`. The case
  (II) matrix `h = leftMatrix 1 z 0` has blocks `(1, z)`. So
  `f(h x) = χ_L(1, z) (1 ⊗ Φ̂⁺σ(z)) f(x)`
  (`leftMixedEval_leftMatrix_mul`). Applying `id ⊗ ev_1` and
  `lTensor_evalAt_one_map` gives `χ_L(1, z) (id ⊗ ev_z)(f(x)) = 0`. The
  character value is a unit, so `(id ⊗ ev_z)(f(x)) = 0` for every `z`. For a
  functional `g` on `ρ`, the vector `φ = lid ((g ⊗ id) f(x))` of `Φ̂⁺(σ)`
  has value `lid ((g ⊗ id)((id ⊗ ev_z) f(x))) = 0` at every `z`
  (`lid_rTensor_lTensor`), so `φ = 0`. Hence `f(x) = 0`
  (`eq_zero_of_forall_dual_rTensor`) for every `x`, and `f = 0`.
- `leftPhiHatEmbedding_injective`: if `leftPhiHatEmbedding f = 0`, then for
  every `x`, the value at `1` of `leftPhiHatMap (x • f)` is `0`. That value is
  `ν(1)^(-1/2) (id ⊗ ev_1)(f(successor(1) x)) = (id ⊗ ev_1)(f(x))`. So
  `f = 0` by `leftPhiHatSource_eq_zero`.
- `leftPhiHatEmbeddingHom T ψ ρ σ` is the embedding as a morphism of smooth
  representations (`SmoothRep.ofHom`), and `mono_leftPhiHatEmbeddingHom`
  states that it is a monomorphism (`SmoothRep.mono_iff_injective`). This is
  the embedding of Ze80 §5.3.

## Import inventory and exclusion audit

Direct imports: `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`
(for `Φ̂⁺`, its evaluation interface and `phiHatPlusAdjunction`) and
`Langlands.Representation.Mirabolic.LeftMixedProductSuccessor` (for the case
(II) successor, radical, compactness and tensor lemmas). No existing Library
file is changed.

The transitive project import closure at Library commit
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb` has 99 modules besides this one
(all prefixed by `Langlands.`):

`Group.GL`: `Basic`, `BlockModulus`, `Blocks`, `Mirabolic`,
`MirabolicMixedProductSubgroups`, `MirabolicModulusProof`,
`MirabolicModulusStatement`, `MirabolicOppositeIntersection`,
`MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`,
`NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`,
`PadicBlocks`, `RankMaps`, `RankReindex`, `TriangularParabolic`,
`UpperUnipotent`. `Group.HaarModulus`. `HarmonicAnalysis`: `Basic`,
`PadicHaarScalingStatement`, `PadicRectangularHaarScalingProof`,
`PadicScalarHaarScalingProof`. `LocalField`: `Canonical`, `Definitions`,
`Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`,
`Topology`. `Representation`: `Category.Abelian`, `Category.Basic`,
`Category.Twist`, `Conductor.Congruence`, `Derivative.MirabolicCharacter`,
`Derivative.MirabolicMinus`, `Derivative.MirabolicMinusNormalization`,
`Derivative.MirabolicPlus`, `Derivative.MirabolicPlusNormalization`,
`Derivative.MirabolicSmoothPhiPlus`, `Derivative.MirabolicSmoothPhiPlusAdjunction`,
`Dual.Definitions`, `Filtration.Definitions`, `Filtration.IsoTransport`,
`Geometric.ClosedSubgroupDefinitions`, `Geometric.CompactSmoothComparison`,
`Geometric.SmoothSupportFiltration`, `Induction.BinaryProduct`,
`Induction.BlockFactors`, `Induction.CompactQuotientProof`,
`Induction.Definitions`, `Induction.Equivalences`, `Induction.Parabolic`,
`Induction.StructuralStatement`, `Jacquet.Coinvariants`,
`Jacquet.Localization`, `Jacquet.PositiveCharacter`, `Jacquet.SmoothTwist`,
`MatrixCoefficient.Definitions`, `MatrixCoefficient.LawsProof`,
`MatrixCoefficient.LawsStatement`, `Mirabolic.LeftMixedProductSuccessor`,
`Mirabolic.MixedProducts`, `Parabolic.GeometricPrerequisitesStatement`,
`Parabolic.QuotientCompactProof`, `Smooth.Admissibility.CofinalProof`,
`Smooth.Admissibility.CofinalStatement`, `Smooth.Definitions`,
`Smooth.SmoothPart.BasicProof`, `Smooth.SmoothPart.BasicStatement`,
`Smooth.SmoothPart.Definitions`, `Smooth.Transfer.PullbackProof`,
`Smooth.Transfer.PullbackStatement`, `Smooth.Transfer.SubquotientProof`,
`Smooth.Transfer.SubquotientStatement`, `Tensor.Finite`, `Tensor.OneFactor`,
`Twist.AdmissibilityProof`, `Twist.AdmissibilityStatement`,
`Twist.AlgebraProof`, `Twist.AlgebraStatement`,
`Twist.ContinuousCharacterProof`, `Twist.ContinuousCharacterStatement`,
`Twist.Definitions`, `Twist.RealPower`, `Twist.SmoothProof`,
`Twist.SmoothStatement`, `Twist.SubquotientDefinitions`,
`Twist.SubquotientProof`, `Twist.SubquotientStatement`,
`Whittaker.Algebraic`, `Whittaker.GeneralLinear`, `Whittaker.Iwasawa`.
`Topology`: `CompactNormCharacter`, `CompactOpen.ConjugationStabilizer`,
`CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`,
`Nonarchimedean.Subgroup`.

These are foundational modules: groups and their Haar moduli, local fields,
smooth representations, induction, twists, Jacquet coinvariants, the
published `Ψ⁻`, `Φ⁻`, `Ψ⁺`, `Φ⁺` and `Φ̂⁺` with their normalizations, the
`Φ⁻ ⊣ Φ̂⁺` and `Ψ⁻ ⊣ Ψ⁺` adjunctions, Whittaker characters and the Iwasawa
decomposition. The closure contains none of the modules or conclusions
excluded by task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` (the inherited sets
of `b711af72`, `3238f371` revision 2, `2e5183b1` revision 2 and the
Whittaker-finiteness clause). In particular, it contains no segment,
socle, head, classification, exhaustion, square-integrability or Jacquet
formula result, and no Ze80 §3.5 or §9.6 derivative formula. It contains
neither `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`
nor `IrreducibleCoinvariantFinitenessStatement` nor
`LeviCuspidalCoinvariantFinitenessStatement`. It contains no derivative
exactness, Leibniz, 4.14(a), highest-layer, level or homogeneity result.
Minus exactness task `b65bc667` is neither used nor resumed.
The `lean_check` inspection of `mono_leftPhiHatEmbeddingHom` reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`.
