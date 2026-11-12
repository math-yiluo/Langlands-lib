# Bounded conjugation of dynamic parabolic points

Author: Worker 4712. Module `Langlands.BruhatTits.Unipotent.ParabolicPointContraction`,
namespace `Langlands.BruhatTits.DynamicUnipotentContainment`. This is a supporting
module for the necessity half of Casselman's criterion (Renard 2026, VII.1.2). It
extends the published contraction coordinates of
`Langlands/BruhatTits/Unipotent/CompactOpenContainmentProof.lean` from the dynamic
unipotent radical `U_G(χ)` to the dynamic parabolic `P_G(χ)`. No Bruhat–Tits
theory is used; the directory is where the coordinate API lives.

## The new definition

`parabolicPoints χ` (an `abbrev`), for a cocharacter
`χ : 𝔾_m ⟶ G` of a group scheme over a field `F`, is the subgroup of rational points
`(Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec F)))`, that is `P_G(χ)(F)`. It is
the parabolic analogue of the published `unipotentPoints χ`.

## Results

Assume `G` is affine over `F`. The published `conjCoord χ b t x` is the polynomial
`∑_{i ≤ degBound χ b} x((coaction χ b)ᵢ) tⁱ` in `t`.

- `mem_parabolicPoints_iff`: `x ∈ P_G(χ)(F)` iff `x` kills all coefficients of
  negative degree of the coaction. This specializes the published
  `DynamicLie.chart_mem_parabolic_iff`.
- `pointRing_conj_apply_of_mem_parabolic`: for `x ∈ P_G(χ)(F)` and `t ∈ Fˣ`, the
  coordinate `b` of `χ(t) x χ(t)⁻¹` is `conjCoord χ b t x`. The proof is that of
  the published `pointRing_conj_apply_of_mem` for `U_G(χ)`. It uses only the
  vanishing of the negative coefficients: the Laurent polynomial
  `t ↦ x(coaction χ b)(t)` is then a polynomial of degree at most `degBound χ b`.
- For a topological ring `F` and the published point topology on `G(F)`:
  - The published
    `Langlands.Aubert.General.RepresentedParabolic.ConeContraction.isInducing_pointRing`
    supplies that the coordinate map `x ↦ (b ↦ x(b))` into `Γ(G, ⊤) → F` is
    inducing. Its proof composes the point homeomorphisms with the embedding
    `AlgPoint.evaluation`.
  - `conjCoord_one`: `conjCoord χ b s 1 = 1(b)` for every `s`, from the published
    `pointRing_contraction` at the identity of `U_G(χ)`.
  - `exists_nhds_forall_conj_mem_of_parabolic` (main result): for a compact set
    `S ⊆ F` and an identity neighborhood `W`, there is an identity neighborhood
    `W'` such that `χ(t) y χ(t)⁻¹ ∈ W` for all `t ∈ Fˣ` with `t ∈ S` and all
    `y ∈ P_G(χ)(F) ∩ W'`.

## Proof of the main result

Because the coordinate map is inducing, `W` contains the preimage of a basic
product neighborhood: there are a finite set `I` of coordinates and neighborhoods
`tset b ∋ 1(b)`, `b ∈ I`. For each `b ∈ I`, the map `(y, s) ↦ conjCoord χ b s y`
is jointly continuous (published `continuous_conjCoord`) and takes the value
`1(b)` on `{1} × S`. Compactness of `S`
(`IsCompact.eventually_forall_of_forall_eventually`) then gives an identity
neighborhood on which `conjCoord χ b s y ∈ tset b` for all `s ∈ S`. Intersect
these neighborhoods over the finite set `I`. For parabolic `y`, the coordinates of
`χ(t) y χ(t)⁻¹` are `conjCoord χ b t y`, so the conjugate lies in `W`.

## Use and provenance

Derived. In the necessity proof, `S = {0} ∪ {tⁿ}` for a unit `t` with `tⁿ → 0`,
and the lemma gives the equicontinuity at `1` of conjugation by the powers
`λ(t)ⁿ` on `P_G(λ)(F)`. That is the weak-contraction input of
`exists_weakIwahoriBasis_of_contraction` (`WeakIwahoriBasis.md`). It replaces the
inclusion "`m K_N m⁻¹ ⊂ K_N` for `m ∈ M⁺`", which Renard takes from the Iwahori
decomposition of the Bruhat–Tits subgroups (VII.1.2, printed p.222 / PDF p.228).
Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`).
