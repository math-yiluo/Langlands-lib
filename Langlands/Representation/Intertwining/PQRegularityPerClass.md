# `PQ`-regularity, one strict predecessor at a time

Author: Worker 102. Module `Langlands.Representation.Intertwining.PQRegularityPerClass`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u` (the field)
and `v` (the representation).

This module restates the published definition `IsPQRegular` (Renard's `PQ`-regularity, in
`Langlands.Representation.Intertwining.PQRegularity`) one double coset at a time. It is used by
`PQCompositionRegularityReduction`. It adds no new `Prop`-valued definitions.

## Setting

`G` is a connected reductive group over a nonarchimedean local field `k`. `P = MN` and
`Q = MU` are parabolic subgroups with the same Levi embedding (`l ≫ p = lQ ≫ q`). The
morphism `a : A ⟶ M` is a split component of `M`, and `σ` is a smooth complex representation
of `M(F)`. Write

- `I_σ = splitComponentKernel l hl a σ`, the kernel in `ℂ[A(F)]` of `σ` along `a`;
- for an intersection datum `D` at `z ∈ G(F)` (`GeometricLemmaIntersectionDatum`),
  `pieceSplitComponentKernel a D σ` for the kernel in `ℂ[A(F)]` of the geometric-lemma piece
  `i^{L}_{Q'} ∘ w ∘ r^M_{P'}(σ)` of `D` along `a`. This is Renard's `I^{Q,w̄}_σ`, read on the full
  graded piece, as in the published `PQRegularity` module.

`IsPQRegular … a σ` means `I_σ ⊔ I^{PQ}_σ = ⊤`.

## Declarations

- `pieceSplitComponentKernel_cast`: transporting an intersection datum along an equality
  `z = z'` of representatives (by `cast`) leaves its piece kernel unchanged. Proof: `subst`,
  then `rfl`.

- `isPQRegular_iff_forall_piece` (theorem): with the hypotheses above, `σ` is `PQ`-regular if
  and only if

  for every `z ∈ G(F)` whose double coset `PzQ` is a strict Bruhat predecessor of the identity
  double coset (`Geometric.BruhatLT (pointImage p) (pointImage q) (DoubleCoset.mk … z)
  (identityParabolicDoubleCoset p q)`), and every intersection datum `D` at `z`,
  `I_σ ⊔ pieceSplitComponentKernel a D σ = ⊤`.

  Renard (VII.3.3, printed p.235) states regularity as `I_σ + ⋂_{w̄ < 1} I^{Q,w̄}_σ = ℂ[A_M]`,
  with one fixed representative per double coset. The right-hand side here quantifies over all
  representatives and all data, which is the form used in the proof of VII.3.5 (i).

## Proof of `isPQRegular_iff_forall_piece`

Two published results are used.

- `representedGeometricLemmaGeometry` supplies an enumeration `c` of the finitely many double
  cosets `P(F)\G(F)/Q(F)`, representatives `zg`, and one intersection datum `Dg i` at each
  `zg i`.
- The first clause of `pqRegularity_predecessorCriteria`: for any choice of representatives
  `zf w` of the double cosets `w` and data `Df w` at `zf w`, `σ` is `PQ`-regular if and only
  if `I_σ ⊔ ⨅_{w < 1} pieceSplitComponentKernel a (Df w) σ = ⊤`.

(⇒) Given `z` and `D`, choose representatives `zf` equal to `z` on the double coset of `z` and
to `zg (c⁻¹ w)` elsewhere. Choose data `Df` equal to `D` on that double coset (transported by
`cast`) and to `Dg` elsewhere. The criterion gives `I_σ ⊔ ⨅_w … = ⊤`. The infimum lies below
the kernel of `D` (`pieceSplitComponentKernel_cast`), so `I_σ ⊔ (kernel of D) = ⊤`.

(⇐) Use the representatives `zg` and data `Dg`. There are finitely many double cosets, so the
infimum is a finite one. `Ideal.sup_iInf_eq_top` reduces the goal to `I_σ ⊔ (kernel of
Dg w) = ⊤` for each `w < 1`, which is the hypothesis.

## Provenance

Derived. Renard's definition of `PQ`-regularity (VII.3.3, printed p.235 / PDF p.241) is the
one formalized in the published `IsPQRegular`. This module only reorganizes it through the
published criterion `pqRegularity_predecessorCriteria`. Source: David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
literature ID `renard-2026-representations-groupes-reductifs-padiques`.
