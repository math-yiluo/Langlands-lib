# Successor and radical lemmas for the case (II) mixed products

Author: Worker 1129. Main declarations:
`Langlands.GeneralLinear.Mirabolic.MixedProduct.leftSuccessor`,
`Langlands.GeneralLinear.Mirabolic.MixedProduct.leftRadical` and
`Langlands.PadicField.TopologicalData.compactSpace_leftQuotient`.

This module collects elementary group, topological and linear-algebra facts
about the published case (II) mixed-product subgroup. They are needed to build
the embedding `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)` in the proof of Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), §5.3 (printed
p.188, PDF p.25; source ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`). The source
calls that embedding "straightforward" and gives no proof. The subgroup is that
of Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §4.12 case (II) (printed pp.456–458, PDF pp.17–19; source ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).

The module defines no new representation and states no theorem of the
sources. It contains two group homomorphisms (`leftSuccessor`, `leftRadical`),
which are restrictions of published homomorphisms, and lemmas about them and
about published objects. Provenance is derived: each statement is a direct
matrix, topological or tensor computation about objects that the sources use
in §4.12(II) and §5.3. None of them adds a hypothesis.

## Conventions

The published case (II) objects in `Langlands.Group.GL.MirabolicMixedProductSubgroups`
are used unchanged. `leftSubgroup k r R` is a subgroup of `mirabolic (k + r) R`,
the mirabolic group `P_(k+r+1)` of rank `k + r + 1`. Its elements are the
mirabolic matrices whose entries in rows `leftIndex k r (inr i)` and columns
`leftIndex k r (inl j)` vanish (`mem_leftSubgroup_iff_entry`). Here
`leftIndex k r : Fin k ⊕ Fin (r + 1) ≃ Fin (k + r + 1)` sends `inl j` to `j`
and `inr i` to `k + i`. `leftProjection : leftSubgroup k r R →* GL_k × P_(r+1)`
takes the two diagonal blocks. In the source's notation `G = P_n`,
`M₁ = GL_k`, `M₂ = P_m`, with `n = k + m` and Lean rank `r = m - 1`.

The other published inputs are these.

* `successor : mirabolic n R →* mirabolic (n + 1) R` is `levi ∘ subtype`:
  `h ↦ diag(h, 1)`.
* `radical n R ≤ mirabolic n R` is the actual unipotent radical of
  `P_(n+1)`: its first `n` columns are those of the identity matrix, and only
  its last column is free.
* `Derivative.Mirabolic.theta ψ n : radical (n + 1) R →* ℂˣ` sends `u` to
  `ψ` of its last radical coordinate, the entry just above the bottom-right
  corner.
* `determinantNorm m : GL_m →* ℝ≥0ˣ` is the normalized absolute value of the
  determinant.
* `Induction.LeftQuotient H` is the coset space `H \ G`, and
  `Induction.quotientSupport H f` is the image in it of `Function.support f`.

## Index lemmas

These lemmas (namespace `Langlands.GeneralLinear.Mirabolic.MixedProduct`, for a
commutative ring `R`) compare the index equivalences of consecutive ranks.

* `leftIndex_inr_castSucc` and `leftIndex_inl_castSucc`: for
  `i : Fin (n + 1)` and `j : Fin k`, the rank `n + 1` index of `inr i.castSucc`
  (respectively `inl j`) is the `castSucc` of the rank `n` index of `inr i`
  (respectively `inl j`).
* `leftIndex_inl_ne_last`: `leftIndex k n (inl j) ≠ Fin.last (k + n)`.
* `leftIndex_inr_eq_last_iff`: `leftIndex k n (inr j) = Fin.last (k + n)`
  if and only if `j = Fin.last n`.
* `leftIndex_inr_ne_inl`: `leftIndex k n (inr i) ≠ leftIndex k n (inl j)`.
* `leftIndex_inl_eq_castSucc`: `leftIndex k n (inl j)` is the `castSucc` of
  `⟨j, _⟩ : Fin (k + n)`. So the `GL_k` coordinates are among the first
  `k + n` columns, which are the identity columns of a radical element.

## Successor embedding

* `successor_mem_leftSubgroup`: for `h ∈ leftSubgroup k n R`,
  `successor h ∈ leftSubgroup k (n + 1) R`.
* `leftSuccessor : leftSubgroup k n R →* leftSubgroup k (n + 1) R` is
  `successor` restricted and corestricted. `leftSuccessor_val` states
  `(leftSuccessor h : mirabolic (k + (n + 1)) R) = successor h` (`rfl`).
* `leftProjection_leftSuccessor`: if `leftProjection h = (a, p)`, then
  `leftProjection (leftSuccessor h) = (a, successor p)`. Thus `diag(h, 1)` has
  the same `GL_k` block, and its mirabolic block is `diag(p, 1)`.

## Radical

* `radical_mem_leftSubgroup`: every `u ∈ radical (k + n) R` lies in
  `leftSubgroup k n R`.
* `leftRadical : radical (k + n) R →* leftSubgroup k n R` is the inclusion.
  `leftRadical_val` states that it is the identity on underlying elements
  (`rfl`).
* `leftProjection_leftRadical_fst`: the `GL_k` block of `leftRadical u` is `1`.
* `leftProjection_leftRadical_snd_mem`: the mirabolic block of
  `leftRadical u` lies in `radical n R`.
* `theta_leftProjection_leftRadical`: for a topological ring `R`, a unitary
  additive character `ψ` and `u ∈ radical (k + (n + 1)) R`,
  `theta ψ n` of the mirabolic block of `leftRadical u` equals
  `theta ψ (k + n) u`. The block keeps the last radical coordinate. Hence the
  non-degenerate character of the radical of `P_(k+n+2)` restricts, through
  the case (II) projection, to that of `P_(n+2)`.

## Determinants and the Levi part

* `det_leftSubgroup`: for `g ∈ leftSubgroup k n R`, `det g` is the product of
  the determinants of its two diagonal blocks. The proof reindexes along
  `leftIndex` and uses `Matrix.det_fromBlocks_zero₂₁`.
* `levi_mem_leftSubgroup_of_isUpperTriangular`: if `m ∈ GL_(k+n)(R)` is upper
  triangular, then `levi m = diag(m, 1)` lies in `leftSubgroup k n R`.

Namespace `Langlands.PadicField.TopologicalData`, for `T : F.TopologicalData`
over `F : PadicField.{uF} p`:

* `determinantNorm_leftSubgroup`: for `g ∈ leftSubgroup k n F` with blocks
  `(a, p)`, `ν_(k+n+1)(g) = ν_k(a) · ν_(n+1)(p)`.
* `det_radical`: radical elements have determinant `1`. Their matrices are
  upper unipotent (`radical_le_upperUnipotent`), and the determinant of an
  upper triangular matrix is the product of its diagonal.
* `determinantNorm_radical'`: radical elements have `ν = 1`. This is the same
  statement as the published `Langlands.Derivative.Mirabolic.determinantNorm_radical`
  in `MirabolicHighestDerivativeDescent`, here in the `TopologicalData`
  namespace. It is reproved so that this module does not import that larger
  module. The prime only separates the name from the published one.
* `determinantNorm_successor`: `ν_(n+2)(successor h) = ν_(n+1)(h)`. This is
  the published `determinantNorm_levi` computation, specialized to mirabolic
  arguments.

## Compactness of the case (II) coset space

* `quotientMap_leftSubgroup_image_levi_integralRange`: the image of
  `levi(GL_(k+n)(O))` in `leftSubgroup k n \ P_(k+n+1)` is everything. Here
  `GL_(k+n)(O)` is `Iwasawa.integralRange` for the valuation of
  `T.valuativeRel`. Proof: write `g = u · levi(m)` with `u` in the radical
  (`eq_radicalElement_mul_levi`). Choose `κ ∈ GL_(k+n)(O)` with `m κ` upper
  triangular (`Iwasawa.exists_mul_upperTriangular`). Then
  `g · levi(κ⁻¹)⁻¹ = u · levi(m κ)` lies in `leftSubgroup k n` by the two
  membership lemmas above. So `g` and `levi(κ⁻¹)` have the same coset.
* `compactSpace_leftQuotient`: with `T.topology`, the coset space
  `Induction.LeftQuotient (leftSubgroup k n F)` is compact. It is the
  continuous image of the compact set `levi(GL_(k+n)(O))`
  (`Parabolic.isCompact_integralRange`, `continuous_levi`). This is a
  theorem, not an instance; use it with `haveI`.

## Closed and compact projected supports

Namespace `Langlands.Induction`. `G` is a topological group, `H ≤ G`,
`σ : Representation R H V`, and `f : G → V` satisfies
`f (h * x) = σ h (f x)` for all `h ∈ H` and `x ∈ G`. Also
`f (x * u) = f x` for all `x` and all `u` in one open subgroup `K`.

* `isClosed_quotientSupport_of_covariant`: `quotientSupport H f` is closed.
  The right invariance makes `f` locally constant. Covariance makes the
  preimage of the projected support equal to `Function.support f`. That set is
  the complement of the open fiber `f⁻¹{0}`, so it is closed. The projection
  `G → H \ G` is a quotient map, so the projected support is closed.
* `isCompact_quotientSupport_of_covariant`: if moreover `H \ G` is compact,
  `quotientSupport H f` is compact.

These are the compact-support condition of BZ77 §1.8 for `f`, obtained without
a separate support argument. The module states them directly, because
`Induction.CompactLocallyConstant` is not in its import closure.

## Vanishing of tensors

Namespace `Langlands.MixedProductTensor`, over `ℂ`:

* `eq_zero_of_forall_dual_rTensor`: if `t : V ⊗ M` satisfies
  `lid (g.rTensor M t) = 0` for every `g : Module.Dual ℂ V`, then `t = 0`.
  Choose a basis of `V` (`Module.Basis.ofVectorSpace`). The coordinates of
  `t` under `TensorProduct.equivFinsuppOfBasisLeft` are the values of
  `lid ∘ rTensor` at the coordinate functionals, so they all vanish.
* `lid_rTensor_lTensor`: `lid (g.rTensor N (e.lTensor V t)) = e (lid (g.rTensor M t))`
  for linear `e : M → N`. The proof is induction on `t`.

## Import inventory and exclusion audit

Direct imports: `Langlands.Representation.Derivative.MirabolicCharacter` (for
`theta`), `Langlands.Representation.Mirabolic.MixedProducts` (the case (II)
subgroup, `successor`, `levi`, `radical`, `determinantNorm`, induction
supports) and `Langlands.Representation.Parabolic.QuotientCompactProof` (for
`Parabolic.isCompact_integralRange` and the Iwasawa input). The transitive
project import closure at Library commit
`b22e185743f7c318f709e14e422801f4360105d5` has 64 modules besides this one:

`Group.GL`: `Basic`, `BlockModulus`, `Blocks`, `Mirabolic`,
`MirabolicMixedProductSubgroups`, `MirabolicOppositeIntersection`,
`MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`,
`NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`,
`PadicBlocks`, `RankMaps`, `RankReindex`, `TriangularParabolic`,
`UpperUnipotent`. `HarmonicAnalysis.Basic`. `LocalField`: `Canonical`,
`Definitions`, `Normalization.Definitions`, `Normalization.Proof`,
`Normalization.Statement`, `Topology`. `Representation`: `Category.Basic`,
`Conductor.Congruence`, `Derivative.MirabolicCharacter`, `Dual.Definitions`,
`Induction.BinaryProduct`, `Induction.BlockFactors`, `Induction.Definitions`,
`Induction.Parabolic`, `Jacquet.Coinvariants`, `Jacquet.Localization`,
`Jacquet.PositiveCharacter`, `Jacquet.SmoothTwist`,
`MatrixCoefficient.Definitions`, `MatrixCoefficient.LawsProof`,
`MatrixCoefficient.LawsStatement`, `Mirabolic.MixedProducts`,
`Parabolic.GeometricPrerequisitesStatement`, `Parabolic.QuotientCompactProof`,
`Smooth.Definitions`, `Smooth.SmoothPart.BasicProof`,
`Smooth.SmoothPart.BasicStatement`, `Smooth.SmoothPart.Definitions`,
`Smooth.Transfer.PullbackProof`, `Smooth.Transfer.PullbackStatement`,
`Smooth.Transfer.SubquotientProof`, `Smooth.Transfer.SubquotientStatement`,
`Tensor.Finite`, `Tensor.OneFactor`, `Twist.ContinuousCharacterProof`,
`Twist.ContinuousCharacterStatement`, `Twist.Definitions`, `Twist.RealPower`,
`Twist.SmoothProof`, `Twist.SmoothStatement`, `Whittaker.Algebraic`,
`Whittaker.GeneralLinear`, `Whittaker.Iwasawa`. `Topology`:
`CompactNormCharacter`, `Nonarchimedean.Subgroup`. (All are prefixed by
`Langlands.`.)

These are foundational modules: groups, local fields, smooth representations,
induction, twists, Jacquet coinvariants, Whittaker characters and the Iwasawa
decomposition. The closure contains none of the modules or conclusions excluded
by task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` (inherited from `b711af72` and
`3238f371` revision 2). In particular, it contains no segment, socle, head,
classification, exhaustion, square-integrability or Jacquet-formula result.
It contains neither `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`
nor `IrreducibleCoinvariantFinitenessStatement` nor
`LeviCuspidalCoinvariantFinitenessStatement`. It contains no derivative
exactness, Leibniz, highest-layer or level result. No lemma here takes a
proposition definition as a hypothesis.
The `lean_check` inspection of `compactSpace_leftQuotient` reports only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
