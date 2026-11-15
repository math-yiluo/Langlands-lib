# Saturated opens of the base change to the completion

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Saturation`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). Its only definition, `satOpen`, is internal to
that proof and is not meant to match a literature definition.

Setting: `R` is a local noetherian ring, `π := completionMap R : Spec R̂ ⟶ Spec R`, and
`U := puncturedSpectrum R`. Also given are
`e : (baseChange π F).RepresentableBy (Over.mk q')` for `q' : X' ⟶ Spec R̂`,
`eU : (baseChange U.ι F).RepresentableBy (Over.mk qU)` for `qU : X_U ⟶ U`, and
`σ : X' ×_S Spec R̂ ⟶ X'` with `hσ : σ ≫ q' = snd` and `hσpt : pt σ = pt fst`.
`puncι : P' ⟶ X'` and `puncMap : P' ⟶ X_U` are from `Puncture.md`, for this `π` and `U`.

## Points of `X' ×_S Spec R̂`

For a point `z` of `X' ×_S Spec R̂`:

- `resOver z : Over (Spec R)` is the spectrum of the residue field `κ(z)`, mapped to
  `Spec R` through `z`. `pt_res` says that `Spec κ(z) ⟶ X' ×_S Spec R̂` followed by
  `σ` and followed by `fst` give the same element of `F` (`pt_sigma`).
- `sigma_apply_comp`: `σ z` and `fst z` have the same image in `Spec R`.
- `sigma_apply_eq_of_closed`: if `fst z` lies over the closed point of `Spec R`, then
  `σ z = fst z`. Proof: let `ρ : Spec κ(z) ⟶ X' ×_S Spec R̂` be the residue field point.
  The morphisms `ρ ≫ fst ≫ q'` and `ρ ≫ σ ≫ q'` from the spectrum of a field to
  `Spec R̂` agree after `π`, and their point lies over the closed point. So they are
  equal by `eq_of_comp_completionMap_eq` (`Completion.md`). Together with `pt_res`,
  `pt_inj` gives `ρ ≫ σ = ρ ≫ fst`. Now evaluate at the point of `Spec κ(z)`.
- `mem_range_puncι`: a point of `X'` not over the closed point lies in the image of
  `puncι` (`Scheme.Pullback.range_fst`).
- `exists_puncMap_eq`: if `fst z` does not lie over the closed point, there are points
  `a`, `b` of `P'` with `puncι a = fst z`, `puncι b = σ z` and
  `puncMap a = puncMap b`. Proof: `ρ ≫ fst` and `ρ ≫ σ` land in the open `P'`
  (previous item and `sigma_apply_comp`), so they lift to `a₀, b₀ : Spec κ(z) ⟶ P'`.
  These have the same element of `F` through `X'` (`pt_res`), so
  `puncMap_eq_of_pt_eq` gives `a₀ ≫ puncMap = b₀ ≫ puncMap`. Evaluate at the point.

## Saturated opens

- `satOpen e eU O' M : X'.Opens` is the open `O' ∪ puncι(puncMap⁻¹ M)`, for
  `O' : X'.Opens` and `M : X_U.Opens`.
- `mem_satOpen`: if `puncMap(puncι⁻¹ O') ⊆ M` (hypothesis `hOM`) and
  `fst z ∈ satOpen O' M`, then `σ z ∈ satOpen O' M`. Proof: if `fst z` lies over the
  closed point, then `σ z = fst z`. Otherwise take `a`, `b` from `exists_puncMap_eq`.
  If `fst z ∈ O'`, then `puncMap b = puncMap a ∈ M` by `hOM`. If
  `fst z = puncι a'` with `puncMap a' ∈ M`, then `a' = a` by injectivity of the open
  immersion `puncι`. In both cases `σ z = puncι b` lies in the second part.
- `sat_satOpen`: the same statement in the form required by `ChartDatum.md`, with
  `range (satOpen O' M).ι` in place of `satOpen O' M`.
- `isCompact_satOpen`: if `O'` and `M` are compact, so is `satOpen O' M`. `puncMap` is
  affine (`isAffineHom_puncMap`, since `π` is a morphism of affine schemes), hence
  quasi-compact, so `puncMap⁻¹ M` is compact, and so is its image under `puncι`.
- `exists_satOpen`: assume `R̂` is noetherian and `q'` is locally of finite type. Then
  every compact `K ⊆ X'` lies in some `O'` with `O'` and `M` compact open and
  `puncMap(puncι⁻¹ O') ⊆ M`. Proof: the underlying space of every scheme is
  prespectral (Mathlib instance), so `K` lies in a compact open `O'`
  (`PrespectralSpace.exists_isCompact_and_isOpen_between`). `X'` is locally
  noetherian (`LocallyOfFiniteType.isLocallyNoetherian`), so the open immersion
  `puncι` into `X'` is quasi-compact. Hence `puncι⁻¹ O'` is compact, and so is its
  image under `puncMap`. In the same way, this image lies in a compact open `M` of
  `X_U`.
