# Algebraic base change of a discrete valuation ring

Author: Worker 254.

This module is commutative algebra. It is used to show that the DVR lifting
property of pseudo-completeness descends along algebraic field extensions,
which is in `Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange`.
Everything lives in the namespace
`Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange` and is
universe-polymorphic.

## Setting and main results

Let `k` be a field and `L` a field that is an algebraic `k`-algebra
(`[Algebra.IsAlgebraic k L]`). Let `R` be a discrete valuation ring and a
`k`-algebra, with residue field `κ = IsLocalRing.ResidueField R` satisfying
`Algebra.IsGeometricallyReduced k κ`. Fix a uniformizer `ϖ`
(`Irreducible ϖ`) and a prime ideal `m` of `L ⊗[k] R` with
`(1 : L) ⊗ₜ ϖ ∈ m`. Write `R' = Localization.AtPrime m` and
`t` for the image of `1 ⊗ ϖ` in `R'`. The field `L` is the left tensor factor
throughout. The module proves:

- `exists_isPrime_tmul_mem`: such a prime `m` exists.
- `isDomain_localization`: `R'` is an integral domain.
- `isDiscreteValuationRing_localization`: `R'` is a discrete valuation ring.
  It takes the domain structure as an instance argument because Mathlib's
  `IsDiscreteValuationRing` presupposes `IsDomain`. Supply it with
  `isDomain_localization`.
- `toLocalization`: the `k`-algebra map `R → R'`, `r ↦ 1 ⊗ r`
  (`toLocalization_apply`). It is injective (`toLocalization_injective`) and
  local (`isLocalHom_toLocalization`).
- `isGeometricallyReduced_residueField`: the residue field of `R'` is
  geometrically reduced over `L`.

The uniformizer property of `t` is used inside the proof of the DVR result but
is not exported as a separate theorem. For general algebraic `L` this module
does not prove that `L ⊗[k] R` itself is a DVR, or that the residue field of
`R'` is a localization of `L ⊗[k] κ`.

When `L/k` is moreover purely inseparable (`[IsPurelyInseparable k L]`, which
Mathlib provides for every algebraic `L` when `k` is separably closed), no
localization is needed. Under that hypothesis and geometric reducedness of `κ`:

- `isLocalRing_tensor`: `L ⊗[k] R` is a local ring.
- `isDomain_tensor`: `L ⊗[k] R` is an integral domain.
- `isDiscreteValuationRing_tensor`: `L ⊗[k] R` is a discrete valuation ring
  (taking `IsDomain (L ⊗[k] R)` as an instance argument, as above).
- `irreducible_tmul`: `(1 : L) ⊗ₜ ϖ` is irreducible in `L ⊗[k] R`.
- `isLocalHom_includeRight`: the map `R → L ⊗[k] R`, `r ↦ 1 ⊗ r`
  (`Algebra.TensorProduct.includeRight`), is local.
- `isFractionRing_tensor`: `L ⊗[k] FractionRing R` is the fraction ring of
  `L ⊗[k] R`, for the algebra structure given by `toTensorFractionRing k L R`,
  the map `Algebra.TensorProduct.map` of the identity of `L` and
  `R → FractionRing R`.
- `isGeometricallyReduced_residueField_tensor`: the residue field of
  `L ⊗[k] R` is geometrically reduced over `L` (taking
  `IsLocalRing (L ⊗[k] R)` as an instance argument; supply it with
  `isLocalRing_tensor`).

Auxiliary results exported along the way: `toTensorFractionRing_injective`
(no purity hypothesis), `isField_tensor_of_isPurelyInseparable` (`L ⊗[k] F` is a
field for a purely inseparable `L` and a geometrically reduced field `F`),
`includeRight_isIntegral` and `ker_map_residue_le` (for integral `L`; every
maximal ideal of `L ⊗[k] R` contains `1 ⊗ ϖ`), `isUnit_iff_map_residue_ne_zero`,
`tmul_not_isUnit`, `tensor_eq_zero_or` (every element is `0` or
`(1 ⊗ ϖ) ^ j * u` with `u` a unit) and `tmul_pow_ne_zero`.

## Provenance

The construction follows Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), proof of Proposition C.1.2(2), printed pp.582–583
(PDF pp.608–609). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`. There, for an arbitrary field
extension `k'/k` and a uniformizer `t` of `R`, the authors localize
`A = R ⊗_k k'` at the prime over a minimal prime of `F ⊗_k k'`, where `F` is
the residue field. They note that the localization is a DVR with uniformizer
`t` whenever it is Noetherian, for example when `k'/k` is finitely generated.
The general case is a direct limit over finitely generated subextensions.

This module treats only algebraic `L/k`, which is the case needed for the
reduction of CGP Proposition C.1.6 to a separably closed ground field. For
such `L` the ring `L ⊗[k] κ` is zero-dimensional, so every prime containing
`1 ⊗ ϖ` lies over a minimal prime and any such prime may be used. The direct
limit of DVRs is replaced by an elementwise argument. Each fraction in `R'`
comes from a finite-dimensional intermediate field `E`, and the Noetherian
case is applied in `E ⊗[k] R`. The source's separability of the new residue
field is proved through Mathlib's geometric-reducedness criterion for field
extensions.

The purely inseparable results are internal to this project and have no
separate source statement. They serve the project's proof of CGP Proposition
C.1.6 (printed p.586, PDF p.612) over a separably closed field `k`. That proof
passes to the algebraic closure of `k`, which is purely inseparable over `k`,
and then compares points over the fraction field of `R` with points over `R`.
For such an extension the localization step of C.1.2(2) is not needed, because
`L ⊗[k] R` is already local.

## Implemented proof

**Unit-times-power criterion.** `isDomain_of_forall_eq_zero_or`: a nontrivial
ring where every element is `0` or `t ^ j * u` for a unit `u`, and all powers
of `t` are nonzero, is a domain. `isDiscreteValuationRing_of_forall_eq_zero_or`:
in such a domain, with `t` a nonzero nonunit, `t` is irreducible, and Mathlib's
`IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` applies.

**Krull intersection.** `localization_eq_zero_or_of_isNoetherianRing`: let
`A` be Noetherian, `n` a prime containing `t`, and suppose every `x ∈ n` has
`s ∉ n` with `s * x ∈ (t)`. Then the maximal ideal of `A_n` is generated by
`t`. Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`)
gives a least `N` with `y ∉ (t) ^ N` for each nonzero `y`. Thus `y = t ^ j * u`
with `j = N - 1`, and `u` is a unit by minimality of `N`.

**Zero-dimensional input.** `exists_notMem_mul_eq_zero`: in a reduced
zero-dimensional ring, an element of a prime `p` is killed by an element
outside `p`, because `p` is minimal and the localization at `p` is a field.
`krullDimLE_zero_tensor`: if `E` is an integral `k`-algebra and `F` a field,
`E ⊗[k] F` has dimension `0`. It is integral over `F`, so every prime is
maximal.

**Finite stages.** Let `E` be a finite-dimensional `k`-algebra. The reduction
map `E ⊗[k] R → E ⊗[k] κ` is surjective (`map_residue_surjective`). By right
exactness of the tensor product, its kernel is `(1 ⊗ ϖ)` (`ker_map_residue`).
For a prime `n` of `E ⊗[k] R` containing `1 ⊗ ϖ`, the image of `n` is prime.
When `E ⊗[k] κ` is zero-dimensional and reduced, `exists_notMem_mul_eq_zero`
lifts to `exists_notMem_mul_mem_span`. The ring `E ⊗[k] R` is a finite
`R`-module, hence Noetherian (`isNoetherianRing_tensor`), so
`stage_localization_eq_zero_or` follows from the Krull step.

**Passage to `L`.** `stageMap k L R E` is the map `E ⊗[k] R → L ⊗[k] R` for
an intermediate field `E` of `L`. By induction on tensors, every element of
`L ⊗[k] R` lies in the range for some finite-dimensional `E`. Any two elements
lie in a common range (`exists_finiteDimensional_mem_range`, `…₂`), using
`IntermediateField.adjoin` of one element and suprema of intermediate fields.
For `mk'_stage_eq_zero_or`, contract `m` to a prime `n` of `E ⊗[k] R`. That
`n` contains `1 ⊗ ϖ`, and `E ⊗[k] κ` is zero-dimensional
(`krullDimLE_zero_tensor`) and reduced (geometric reducedness of `κ`, since
the finite-dimensional field `E` is algebraic over `k`). Apply
the finite-stage result in `(E ⊗[k] R)_n` and push it forward along the local
map `Localization.localRingHom` into `R'`. `localization_eq_zero_or` writes an
arbitrary element of `R'` as such a fraction, so every element of `R'` is `0`
or `t ^ j * u` with `u` a unit.

**Domain and DVR.** Multiplication by `1 ⊗ ϖ` on `L ⊗[k] R` is
`LinearMap.lTensor L` of multiplication by `ϖ`. It is injective since `L` is
flat over `k` (`mul_tmul_injective`). Hence no power of `t` is zero in `R'`
(`algebraMap_pow_ne_zero`). Also `t` lies in the maximal ideal
(`algebraMap_mem_maximalIdeal`). The unit-times-power criterion gives
`isDomain_localization` and `isDiscreteValuationRing_localization`.

**The map `R → R'`.** A nonzero `r` is `u * ϖ ^ n` with `u` a unit, and its
image `unit * t ^ n` is nonzero, giving `toLocalization_injective`. A nonunit
`r` is `ϖ * c`, and its image lies in the maximal ideal, giving
`isLocalHom_toLocalization`.

**Existence of `m`.** `L ⊗[k] κ` is nontrivial (Mathlib's
`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`).
The preimage of a maximal ideal under the reduction map
`L ⊗[k] R → L ⊗[k] κ` is a prime. It contains `1 ⊗ ϖ` because `ϖ` has zero
residue.

**Residue field.** `isGeometricallyReduced_of_forall_mul_eq` is a general
lemma. Let `A` be a reduced zero-dimensional `L`-algebra with
`AlgebraicClosure L ⊗[L] A` reduced, and let `θ : A →ₐ[L] κ'` be a map to a
field such that every element of `κ'` has the form `θ a / θ s`. Then `κ'` is
the localization of `A` at the prime `ker θ`. The kernel condition uses
`exists_notMem_mul_eq_zero`. Thus `AlgebraicClosure L ⊗[L] κ'` is a
localization of a reduced ring
(`IsLocalization.tensorProductEquivOfMapIncludeRight`), and
`Algebra.isGeometricallyReduced_field_iff` concludes. In
`isGeometricallyReduced_residueField`, `A = L ⊗[k] κ` and `θ` is induced by
`L → κ(R')` and by `ResidueField.mapAlgHom` of the local map
`toLocalization`. A tensor induction shows that `θ` composed with the
reduction map is the residue map of `R'` on `L ⊗[k] R`. Hence every residue
class `b / s` equals `θ(π b) / θ(π s)`. Reducedness of
`AlgebraicClosure L ⊗[L] (L ⊗[k] κ)` comes from its isomorphism
(`Algebra.TensorProduct.cancelBaseChange`) with
`AlgebraicClosure L ⊗[k] κ`. That ring is reduced by Mathlib's instance
giving reducedness of `K ⊗[k] κ` for every algebraic field extension `K/k`
when `κ` is geometrically reduced over `k`; `AlgebraicClosure L` is
algebraic over `k` because `L/k` is. The same instance makes `L ⊗[k] κ` and
the finite stages `E ⊗[k] κ` reduced.

**Fraction ring map.** `toTensorFractionRing_injective`: the map
`L ⊗[k] R → L ⊗[k] FractionRing R` is `LinearMap.lTensor L` of the injective map
`R → FractionRing R`, so it is injective because `L` is flat over `k`.

**Purely inseparable extensions.** `isField_tensor_of_isPurelyInseparable`:
let `x ≠ 0` in `L ⊗[k] F`. Mathlib's
`IsPurelyInseparable.exists_pow_mem_range_tensorProduct`, applied after the
swap `L ⊗[k] F ≃ F ⊗[k] L`, gives `n > 0` and `c ∈ F` with `x ^ n = 1 ⊗ c`.
The ring is reduced since `F` is geometrically reduced, so `x ^ n ≠ 0` and
`c ≠ 0`. Hence `x ^ n` is a unit, and so is `x`. Nontriviality comes from
`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`.

**Locality.** `includeRight_isIntegral`: the map `R → L ⊗[k] R` is, up to the
swap isomorphism, the algebra map `R → R ⊗[k] L`, which is integral because
`L` is integral over `k`. By `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`,
every maximal ideal `M` of `L ⊗[k] R` contracts to the maximal ideal of `R`, so
`1 ⊗ ϖ ∈ M`. Since the kernel of the reduction map
`ρ : L ⊗[k] R → L ⊗[k] κ` is `(1 ⊗ ϖ)` (`ker_map_residue`), this gives
`ker_map_residue_le`. In `isUnit_iff_map_residue_ne_zero`, a unit has a unit,
hence nonzero, image in the field `L ⊗[k] κ`. Conversely, if `ρ x ≠ 0` and `x`
lies in a maximal ideal `M`, then `ρ(M)` is a prime ideal (surjectivity of `ρ`
and `ker ρ ≤ M`) containing the unit `ρ x`, which is impossible. Sums of
nonunits therefore map to `0`, and `isLocalRing_tensor` follows by
`IsLocalRing.of_nonunits_add`. The element `1 ⊗ ϖ` and every `1 ⊗ r` with `r`
a nonunit map to `0` under `ρ`, giving `tmul_not_isUnit` and
`isLocalHom_includeRight`.

**Domain, DVR and uniformizer.** A local ring is isomorphic to its
localization at its maximal ideal (`IsLocalization.atUnits`). Taking `m` to be
the maximal ideal in `localization_eq_zero_or` and transporting back along this
isomorphism gives `tensor_eq_zero_or`. `tmul_pow_ne_zero` is
`algebraMap_pow_ne_zero` for the same `m`. The unit-times-power criterion then
gives `isDomain_tensor` and `isDiscreteValuationRing_tensor`. For
`irreducible_tmul`, the maximal ideal of `L ⊗[k] R` is the set of nonunits,
which by `isUnit_iff_map_residue_ne_zero` is `ker ρ = (1 ⊗ ϖ)`, and
`IsDiscreteValuationRing.irreducible_iff_uniformizer` applies.

**Fraction ring.** `isFractionRing_tensor` checks the three conditions of
`IsLocalization` for the algebra structure of `toTensorFractionRing`. A nonzero
element of `L ⊗[k] R` is `(1 ⊗ ϖ) ^ j * u` with `u` a unit, and `1 ⊗ ϖ` maps
to the unit `1 ⊗ ϖ` of `L ⊗[k] FractionRing R`, so every non-zero-divisor maps
to a unit. Surjectivity is by induction on tensors: `l ⊗ (a / b)` is the image
of `l ⊗ a` divided by the image of `1 ⊗ b`, where `1 ⊗ b ≠ 0` by injectivity of
`Algebra.TensorProduct.includeRight`, and sums of fractions are combined over a
common denominator. The kernel condition is `toTensorFractionRing_injective`.

**Residue field.** `isGeometricallyReduced_residueField_tensor` reuses
`isGeometricallyReduced_of_forall_mul_eq` with `A = L ⊗[k] κ`. The map
`θ : L ⊗[k] κ → κ(L ⊗[k] R)` is induced by `L → κ(L ⊗[k] R)` and by
`ResidueField.mapAlgHom` of the local map `includeRight`. A tensor induction
shows that `θ ∘ ρ` is the residue map of `L ⊗[k] R`, so every residue class is
`θ(ρ y) / θ(1)`. Zero-dimensionality and the reducedness inputs are as in the
residue-field step for `R'` above.
