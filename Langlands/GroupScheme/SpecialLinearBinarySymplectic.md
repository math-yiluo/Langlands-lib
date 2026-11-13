# The binary symplectic group is the binary special linear group

Author: Worker 170.

This helper module, `Langlands.GroupScheme.SpecialLinearBinarySymplectic`, identifies the
split symplectic group scheme `Sp_2` with the special linear group scheme `SL_2` over an
arbitrary commutative base ring, and deduces that `SL_2` over a field is simply connected.
All declarations live in the namespace
`Langlands.GroupScheme.SpecialLinear.BinarySymplectic`.

Provenance: this is derived, internal content. The mathematics is the classical identity
`Sp_2 = SL_2`: for every `2 × 2` matrix `g` over a commutative ring, `g J gᵀ = det(g) J`,
where `J = [[0, -1], [1, 0]]` is Mathlib's `Matrix.J (Fin 1) A` in the coordinates
`Fin 1 ⊕ Fin 1`. No literature source beyond this standard computation is used.

## Matrix identities

The coordinates `Fin 1 ⊕ Fin 1` of `Matrix.symplecticGroup (Fin 1) A` are matched with the
coordinates `Fin 2` of `Matrix.SpecialLinearGroup (Fin 2) A` by
`indexEquiv := finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2`. Here `A` is any commutative ring.

- `det_eq g`: for `g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A`,
  `det g = g₁₁ g₂₂ - g₁₂ g₂₁` (indices `inl 0`, `inr 0`). Proof: reindex along
  `indexEquiv` (`Matrix.det_reindex_self`) and use `Matrix.det_fin_two`.
- `mul_J_mul_transpose g`: `g * J * gᵀ = det g • J`. Proof: after `det_eq`, compare all
  four entries by `simp` with `Matrix.mul_apply`, `Fintype.sum_sum_type`, `Matrix.J`, and
  `ring`.
- `mem_symplecticGroup_iff g`: `g ∈ Matrix.symplecticGroup (Fin 1) A ↔ det g = 1`. Proof:
  by `SymplecticGroup.mem_iff` and the previous identity, membership says
  `det g • J = J`; the `(inl 0, inr 0)` entry of this equation is `det g = 1` (the entry
  of `J` there is `-1`), and conversely `det g = 1` gives `1 • J = J`.

## The group isomorphism

- `toSpecialLinear : Matrix.symplecticGroup (Fin 1) A ≃* Matrix.SpecialLinearGroup (Fin 2) A`
  sends `g` to `Matrix.reindex indexEquiv indexEquiv g`, with inverse reindexing along
  `indexEquiv.symm`. Both directions land in the right group by
  `mem_symplecticGroup_iff` and `Matrix.det_reindex_self`; multiplicativity is
  `Matrix.submatrix_mul_equiv`.
- `coe_toSpecialLinear` records the underlying matrix (by `rfl`).
- `toSpecialLinear_map f g`: for a ring homomorphism `f : A →+* B`,
  `toSpecialLinear (SymplecticMatrix.map (Fin 1) f g) =
  Matrix.SpecialLinearGroup.map f (toSpecialLinear g)`; entrywise this is `rfl`.

## The group-scheme isomorphism

Let `R : CommRingCat.{u}`.

- `symplecticPointsEquiv R T` composes the published point model
  `SymplecticMatrix.pointsEquiv (Fin 1) R T` (points of
  `SymplecticMatrix.groupScheme (Fin 1) R` over a test scheme `T` are symplectic matrices
  over `Γ(T.left, ⊤)`) with `toSpecialLinear`.
- `symplecticPointsEquiv_naturality` shows that this model is natural for restriction
  along `a : T' ⟶ T`, acting on matrices by `Matrix.SpecialLinearGroup.map
  a.left.appTop.hom`; it combines `SymplecticMatrix.pointsEquiv_naturality` with
  `toSpecialLinear_map`.
- `symplecticIso R : SymplecticMatrix.groupScheme (Fin 1) R ≅
  SpecialLinear.groupScheme (Fin 2) R` is the published `isoOfPointModels`
  (from `Langlands.GroupScheme.Torus.Split`) applied to the common point model
  `T ↦ Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)`, with the symplectic model above and
  the published special-linear model `SpecialLinear.pointsEquiv (Fin 2) R` and its
  naturality `SpecialLinear.pointsEquiv_naturality`.

## Simple connectedness of `SL_2`

`isSimplyConnected (k : Type u) [Field k] :
IsSimplyConnected (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))` is obtained from
the published `SymplecticMatrix.isSimplyConnected (Fin 1) k` (the split symplectic group
over a field is simply connected) by `IsSimplyConnected.of_iso` along
`(symplecticIso (CommRingCat.of k)).symm`. There is no restriction on the characteristic
of `k`, and both semisimplicity and the central-isogeny criterion are transported.
