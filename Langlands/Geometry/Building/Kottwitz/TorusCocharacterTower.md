# Cocharacter evaluations in a tower of coefficient fields

Helper module for the proof of `TorusKottwitzExistenceStatement`
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Proposition 11.1.1).
KP's proof compares the maps `T(L) → X_*(T)` for different splitting fields `L`. It
evaluates a cocharacter `ν` at a unit `u` (the point `ν(u)`) and tracks how such points
behave under field extension, Galois conjugation and the norm. This module records these
compatibilities for the Library's objects:

- `coefficientEvaluation k L T : L^× ⊗ X_*(T_L) →+ T(L)` (Torus/PointsTensorGalois), whose
  value on `u ⊗ ν` is `ν(u)`;
- `extendGeometricCocharacters k L M T : X_*(T_L) →+ X_*(T_M)` (Kottwitz/TorusMap);
- the relative extension, conjugation and norm maps `relativeExtend`, `conjugate`,
  `relativeConjugate` and `relativeNorm` on coefficient points (GroupScheme/GaloisPoint*).

Everything here is derived internal infrastructure. It introduces no new mathematical
objects: `extendTestArrow` is an auxiliary morphism of test objects.

## Extension of pure evaluations (section `Tower`)

For a scalar tower `k → L → M` of fields and a commutative group scheme `T` over `k`:

- `extendTestArrow L M` is `Spec M → Spec L`, as a morphism of test objects over `Spec L`.
- `unitPoint_extend`: the `Gm`-point of `M^×` given by the image of `u ∈ L^×` is the pullback
  of the point `u` along `Spec M → Spec L`. The proof compares global sections through
  `Scheme.ΓSpecIso_naturality`.
- `relativeExtend_coefficientEvaluation_tmul`: extending coefficients from `L` to `M` sends
  `ν(u)` to `ν_M(u)`, where `ν_M = extendGeometricCocharacters k L M T ν`. Proof: apply the
  Library lemma `cocharacterLattice.baseChange_points` to the unit point and use
  `unitPoint_extend`. Then compose with the first projection of the fibre product through
  `towerBaseChangeIso_hom_fst`.
- `relativeExtend_conjugate`: if `τ ∈ Aut_k(M)` and `σ ∈ Aut_k(L)` agree on `L`, then
  extension intertwines `conjugate σ` and `conjugate τ`. Checked on coordinates.

## Evaluation at a non-torsion unit (section `Evaluation`)

Let `A` be a split torus over a field `K`.

- `cocharacterPoints_injective`: if `b ∈ K^×` has infinite order, then `ν ↦ ν(b)` is
  injective on `X_*(A)`. Proof: pair with every character `χ` through the perfect pairing
  `cocharacterDualEquiv`; `χ(ν(b)) = b^{⟨χ, ν⟩}`
  (`rationalCharacterEval_cocharacterPoints`), and `n ↦ b^n` is injective.
- `splitValuation_cocharacterPoints`: for an integer-valued valuation `v`, the Library's
  `splitValuation A hA v` sends `ν(b)` to `ord_v(b) • ν`, where
  `ord_v = IntegerValuation.orderUnits v`. Proof: compare pairings with characters through
  `splitValuation_pairing`.

## Pure tensors (section `PureTensor`)

- `coefficientEvaluation_tmul_eq` is the definitional unfolding of `ν(u)`.
- `coefficientEvaluation_tmul_injective`: for `T_L` split and `u` of infinite order, the
  map `ν ↦ ν(u)` is injective.
- `additive_ext_coefficientEvaluation`: when `T_L` is split, two additive maps out of `T(L)`
  that agree on all `ν(u)` are equal. Proof: `coefficientPointEquiv` identifies `T(L)` with
  `L^× ⊗ X_*(T_L)`, and pure tensors generate (`TensorProduct.inductionOn`).

## Galois compatibility (section `Compatibility`)

Let `k → L → M` be a scalar tower, `T_M` split, and `u₀ ∈ L^×` of infinite order.

- `extendGeometricCocharacters_galois`: if `τ ∈ Aut_k(M)` restricts on `L` to
  `σ ∈ Aut_k(L)`, then extension of cocharacters intertwines the Galois actions
  (`cocharacterLattice.galoisRepresentation`) of `σ` and `τ`. Proof: evaluate both sides at
  the image of `σ(u₀)` in `M` and use `coefficientEvaluation_galois_tmul`,
  `relativeExtend_coefficientEvaluation_tmul` and `relativeExtend_conjugate`. Conclude by
  `coefficientEvaluation_tmul_injective`.
- `extendGeometricCocharacters_relative`: elements of `Aut_L(M)` fix every extended
  cocharacter. This is the previous lemma with `σ = 1`.

## Norms (section `Norm`)

Assume in addition that `M/L` is finite Galois.

- `relativeNorm_coefficientEvaluation_tmul`: for `x ∈ M^×` and `ν ∈ X_*(T_L)`,
  `N_{M/L}(ν_M(x)) = ν(N_{M/L} x)`. Proof: after extending back to `M` (which is
  injective, `relativeExtend_injective`), the left side is `∏_σ σ(ν_M(x))`
  (`relativeExtend_norm`). By `extendGeometricCocharacters_relative` and
  `coefficientEvaluation_galois_tmul` each factor is `ν_M(σ x)`. Additivity in the unit
  then gives `ν_M(∏_σ σ x)`, and `∏_σ σ x` is the image of the field norm
  (`Algebra.norm_eq_prod_automorphisms`).

## Transitivity (section `TowerComposition`)

- `extendGeometricCocharacters_extend`: in a tower `k → L → M → E` with `T_E` split and
  `u₀ ∈ L^×` of infinite order, extending from `L` to `M` and then to `E` agrees with
  extending from `L` to `E`. Proof: evaluate at the image of `u₀` and use
  `relativeExtend_relativeExtend` (TorusNormCohomology).

## Bijectivity (section `Bijective`)

- `extendGeometricCocharacters_bijective`: if `T_L` is split, extension of cocharacters from
  `L` to any extension `E` is bijective. It is the composite of the Library's
  `IsSplitTorus.cocharacterLattice_baseChange_bijective` with an additive equivalence.
