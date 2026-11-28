# Transferring the projection criterion to a left coset space

**Setting.** `H` is a locally compact topological group with a measurable structure, `Γ` is a
subgroup, and `Γ \ H` is `LeftCosetSpace Γ` with its quotient topology and quotient measurable
structure. It is assumed Hausdorff, second countable and Borel, and it carries a regular
measure `μ`. An operator `Λ` on functions `H → ℂ` induces an operator on functions on `Γ \ H`:

`f ↦ (q ↦ Λ (f ∘ mk) q.out)`,

with `mk` the quotient map and `q.out` the chosen representative. This is the form in which
[`TruncationOrthogonalProjectionStatement`](ArthurTruncationL2Statement.md) evaluates
truncation on the rational quotients.

**Provenance.** This is a derived interface between the pointwise truncation statements, which are
phrased for left-invariant functions on adelic points, and the criterion of
[ArthurTruncationL2Criterion](ArthurTruncationL2Criterion.md), which is phrased on the
quotient. It involves no source-specific mathematics.

## Results on representatives

In `Langlands.Global.LeftCosetSpace`, two Library lemmas are used:

- `mk_out` (module `Langlands.Global.LeftCosetImageMajorant`): `mk Γ q.out = q`;
- `apply_out_mk` (module `Langlands.Global.LeftCosetUnfoldingBound`): a left
  `Γ`-invariant function takes the same value at `x` and at the chosen
  representative of the class of `x`.

This module adds:

- `exists_isCompact_image_superset`: every compact subset of `Γ \ H` lies in the image of a
  compact subset of `H`. Cover it by the open images of interiors of compact neighbourhoods
  and take a finite subcover. The quotient map is open by `isOpenQuotientMap_mk`.
- `bounded_out_of_invariant`, `bounded_comp_mk`: local boundedness passes in both directions
  between left `Γ`-invariant functions on `H` and functions on `Γ \ H`.
- `exists_compact_support_comp_mk`: the pullback of a compactly supported function on
  `Γ \ H` is supported on the `Γ`-saturation of a compact subset of `H`.
- `measurable_out_of_invariant_complex`: a measurable left `Γ`-invariant function `H → ℂ`
  gives a measurable function at the representatives. Its composite with the quotient map is
  the original function (Mathlib's `measurable_from_quotient`). The Library's
  `measurable_out_of_invariant` (module `Langlands.Global.AdelicInducedInnerProductIntegrable`)
  has general codomain but requires `H : Type`; this version allows `H` in any universe,
  which the adelic groups over a number field `F : Type u` need.

## The transfer

`Langlands.Global.ArthurTruncation.isOrthogonalL2Extension_leftCosetSpace` assumes the
following of `Λ`:

- for measurable, left `Γ`-invariant `φ` bounded on compact sets, `Λ φ` has the same three
  properties;
- `Λ (Λ φ) = Λ φ` for such `φ`;
- for such `φ₁` and continuous, left `Γ`-invariant `φ₂` supported on the `Γ`-saturation of a
  compact set, the function `y ↦ φ₁ y.out · (Λ φ₂ y.out)‾` is `μ`-integrable and
  `∫ Λ φ₁ (y.out) · φ₂(y.out)‾ dμ = ∫ φ₁(y.out) · (Λ φ₂ (y.out))‾ dμ`.

It concludes `IsOrthogonalL2Extension μ (fun f q => Λ (fun x => f (mk Γ x)) q.out)`.

**Proof.** Apply `isOrthogonalL2Extension_of_pairing` to the induced operator. If `f` on `Γ \ H` is
measurable and bounded on compact sets, then `f ∘ mk` is measurable, bounded on compact sets and
left `Γ`-invariant. The results above transport the conclusions for `Λ (f ∘ mk)` back to
the representatives. For idempotence, the pullback of the induced `Λ ψ` is `Λ (ψ ∘ mk)` by
invariance. A continuous compactly supported `ψ` on `Γ \ H` pulls back to a continuous
invariant function supported on the saturation of a compact set. Finally,
`(f ∘ mk)(y.out) = f y`, so the pairing hypothesis is the pairing hypothesis of the criterion.
