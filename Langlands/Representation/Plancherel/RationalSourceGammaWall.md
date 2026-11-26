# The actual source gamma across one wall of a common Levi

This module proves that Waldspurger's common-compact constant `γ(P)`
does not change when a parabolic subgroup crosses one wall inside the
set of parabolics with a fixed Levi. It is the inductive step for the
independence of `γ(P)` from `P` in Remark (3) of I.1 of J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed pp.240–241
(PDF pp.6–7), registered as `waldspurger-2003-plancherel`.

Waldspurger evaluates `γ(P)` on one small compact open subgroup `H`
that factors along root subgroups for every semistandard `P`. He then
splits the indices of radicals into products over roots. The Lean proof
uses no root subgroups. It compares two parabolics `P(χ)` and `P(χ')`
with the same Levi `M` that differ across one wall, given by a third
cocharacter `φ` with Levi `L ⊇ M`. Here a wall is the face of `φ`: both
parabolics lie in `P(φ)`, and inside `L` their radicals are exchanged.
The face may lie on several root hyperplanes, so one such crossing can
change the signs of several non-proportional roots at once. For such a pair it builds a small
subgroup `H` adapted to both parabolics and to `P(φ)`. It then splits
the radical indices along the semidirect decompositions
`U(χ) = (U(χ) ∩ L) ⋉ U(φ)`. This route is derived and internal.

## Setting

`F` is a nonarchimedean local field of arbitrary characteristic, in an
arbitrary universe. The group scheme `G` over `F` is affine and locally
of finite type, and `IsConnectedReductive G` is a hypothesis of the main
theorem. Rational points carry the canonical topology
`rationalPointTopology F G.X`. For a cocharacter `ψ`, `P(ψ)`, `Z(ψ)` and
`U(ψ)` are the rational points of the published dynamic parabolic,
centralizer and unipotent subgroup functors, and `ψ⁻¹` is
`oppositeCocharacter ψ`. `gamma ψ K hK` is the published
`RationalDynamicSource.gamma`, with the original Haar measures that
give mass one to the intersections with the fixed compact open `K`.

## Declarations

- `SourceGammaIndexProduct.mem_iff_of_unique_factorization`: if
  `H = (H ∩ U)(H ∩ M)(H ∩ V)` with unique factors and `M` normalizes `U`,
  then `m u v ∈ H` exactly when `m, u, v ∈ H`. This is the argument of
  the private lemma used for `exists_gammaAuxiliarySubgroup` in
  `RationalSourceGammaOpposite`.
- `exists_limit_mul_unipotent`: every `x ∈ P(ψ)` is `l * n` with `l` its
  published dynamic limit `Dynamic.limitHom ψ` and `n ∈ U(ψ)`. This uses
  the published `dynamic_isSemidirectDecomposition` and
  `dynamic_projection_eq_limitHom`.
- `splitTrace_of_limit_stable`: if a subgroup `Y` is stable under the
  dynamic limit of `P(ψ)`, then for every subgroup `X ≤ P(ψ)` containing
  `U(ψ)`, `SplitTrace Y X Z(ψ) U(ψ)` holds.
- `sourceTraceIndex_eq_relIndex`: the published `sourceTraceIndex K H X`
  equals `(H ⊓ X).relIndex (K ⊓ X)`.
- `gamma_eq_of_wall`: the main theorem, below.

## The wall theorem

The hypotheses of `gamma_eq_of_wall` are:

- `Z(χ') = Z(χ) = M` and `M ≤ L = Z(φ)`;
- `U(φ) ≤ U(χ) ∩ U(χ')` and `U(φ⁻¹) ≤ U(χ⁻¹) ∩ U(χ'⁻¹)`;
- `U(χ), U(χ') ≤ P(φ)` and `U(χ⁻¹), U(χ'⁻¹) ≤ P(φ⁻¹)`;
- `U(χ) ∩ L = U(χ'⁻¹) ∩ L` and `U(χ⁻¹) ∩ L = U(χ') ∩ L`;
- `K` is stable under the dynamic limits of `P(χ)`, `P(χ')`, `P(φ)` and
  `P(φ⁻¹)`.

The conclusion is `gamma χ K hK = gamma χ' K hK`.

The proof has three steps.

1. *The small subgroup.* `H₁ = gammaAuxiliarySubgroup φ K hG` is the
   published compact open subgroup of `K` with Levi-first factorizations
   for `φ` in both radical orders (`gammaAuxiliarySubgroup_spec`). The
   published `StandardIntertwining.CommonLeviSplitting.exists_iwahoriCut` gives a compact open
   `H ⊆ H₁` with `H = (H ∩ U(χ⁻¹)) (H ∩ M) (H ∩ U(χ))`. It also gives a
   point `g ∈ M` such that `x ∈ U(χ)` lies in `H` exactly when
   `g^j x g^-j ∈ H₁` for all `j ≥ 0`, and a similar description of
   `H ∩ U(χ⁻¹)`.
2. *Factorizations of `H`.* Write `x ∈ H ∩ U(χ)` as `l n` with
   `l ∈ L` its `φ`-limit and `n ∈ U(φ)`. The point `g` lies in `L`, so
   conjugation by `g^j` preserves both factors. The factorization of
   `H₁` puts each conjugated factor in `H₁`, and the description of
   `H ∩ U(χ)` puts `l` and `n` in `H`. So the trace of `H` on `U(χ)`
   splits along `(L, U(φ))`, and likewise on `U(χ⁻¹)` along
   `(L, U(φ⁻¹))`.
   From the `χ`-factorization of `H` it follows that
   `H = (H ∩ U(φ)) (H ∩ L) (H ∩ U(φ⁻¹))`, with the `L`-part in the
   order `(U(χ) ∩ L)(M)(U(χ⁻¹) ∩ L)`. Uniqueness in the open cell of
   `φ` is the published `dynamic_opposite_factorization_unique` for
   `φ⁻¹`. It shows that `H` is stable under the dynamic limits of
   `P(φ)` and `P(φ⁻¹)`, and that `H ∩ L` factors in the order
   `(U(χ⁻¹) ∩ L)(M)(U(χ) ∩ L)`. The two identities between the parts of
   `L` then give `H = (H ∩ U(χ')) (H ∩ M) (H ∩ U(χ'⁻¹))`. With the
   published uniqueness for `χ'`, `mem_iff_of_unique_factorization`
   yields the local hypothesis of the published `gamma_eq_gammaIndex`
   for `χ'`, as for `χ`.
3. *Indices.* By `gamma_eq_gammaIndex`, both gammas are the published
   `gammaIndex` expressions at the same `H`. They share the factor
   `[K : H]`, and the Levi factor agrees because `Z(χ') = Z(χ)`. The
   traces of `K` split along `(L, U(φ))` and `(L, U(φ⁻¹))` by limit
   stability of `K` for `φ` and `φ⁻¹`. The traces of `H` split by
   step 2. `SourceGammaIndexProduct.relIndex_mul_eq_of_wall` equates the
   products of the two radical indices. The published
   `dynamic_parabolic_le_normalizer` supplies normality of `U(φ)` in
   `P(φ)`, and uniqueness in the open cell gives `L ∩ U(φ) = 1`.

The index evaluation in step 3 uses right invariance of the ambient Haar
measure along each opposite radical. The published
`gamma_eq_gammaIndex`, applied for `χ` and for `χ'`, evaluates the
published trace formula `lintegral_eq_levi_radical_of_limit_stable` on
the indicator of `H`. The proof of that formula uses invariance of the
ambient Haar measure under right translation by `U(χ⁻¹)`, respectively
`U(χ'⁻¹)`. The Library proves this invariance in
`map_mul_right_ambientHaar_of_unipotent`
(`RationalSourceGammaAmbientHaar`), so `gamma_eq_of_wall` has no
invariance hypothesis. Its explicit premises are the four
compact-limit stability premises for `P(χ)`, `P(χ')`, `P(φ)` and
`P(φ⁻¹)` and the group-level wall hypotheses. The argument of this
module uses no Iwasawa factorization and no root subgroups. The module
`RationalSourceGammaCommonLevi` derives the wall hypotheses from
relative-root signs.

The local instances have names with the `sourceGammaWall` prefix, so
that this module can be imported together with the other source-gamma
modules.
