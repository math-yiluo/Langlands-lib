# Arbitrarily small neighborhoods for finite morphisms

Author: Worker 36.

This module proves Berkovich's Lemma 3.1.2 for the finite morphisms of
`FullRecognitionFiniteMorphisms`: if a strong map of local-domain
enlargements is finite at a point, the neighborhoods can be chosen inside any
prescribed neighborhood of the point. As a consequence, quasifinite morphisms
compose (the composition part of Corollary 3.1.3). Along the way it constructs
the recognized piece of a recognized subset cut out by a relatively clopen
open set, and shows that restriction to it is a finite Banach map.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definition 3.1.1, printed p.54 / PDF p.51: finiteness at a point and
  quasifinite morphisms (formalized in `FullRecognitionFiniteMorphisms`);
- Lemma 3.1.2, printed pp.54–55 / PDF pp.51–52: "If a morphism `φ : Y → X` is
  finite at a point `y ∈ Y`, then the neighborhoods `𝒱` and `𝒲` from the
  Definition 3.1.1 can be found arbitrary small." The proof splits the
  preimage of a small neighborhood `𝒰` of `x = φ(y)` as `∐ᵢ 𝒱ᵢ` with
  `yᵢ ∈ 𝒱ᵢ`, and observes: "It follows that all of the morphisms `𝒱ᵢ → 𝒰` are
  finite, and the neighborhood `𝒱₁` of `y` is sufficiently small";
- Corollary 3.1.3, printed p.55 / PDF p.52: "Quasifinite morphisms are
  preserved under compositions, under any base change functor, and under any
  ground field extension functor."

`IsFiniteOver.exists_small` and `IsFiniteAt.exists_small` transcribe Lemma
3.1.2. As in the source, the target neighborhood `𝒰` lies inside the original
one and the source neighborhood is open. `IsQuasifinite.comp` is the
composition part of Corollary 3.1.3. Base change and ground field extension
are not treated. The proofs are derived. The source's "it follows that
`𝒱₁ → 𝒰` is finite" is proved here with the Shilov idempotent theorem of
`AffinoidIdempotents`. The finiteness of the fibre comes from
`FiniteMorphismFibres`, and the splitting from the separation theorem of
`FibreSeparation`. The Library's descent for affinoid domains supplies the
norm control.

## Finite Banach maps from norm-controlled lifts

- `BoundedAlgHom.isFiniteBanach_of_lift`: a bounded algebra map `f` such that
  every element `z` has a preimage `c` with `‖c‖ ≤ M ‖z‖` (`M > 0`) is a finite
  Banach map in the sense of `FullRecognitionFiniteMorphisms`, with the single
  generator `1`.
- `Represents.exists_lift_of_exists_lift`: let two bounded maps out of the
  same affinoid algebra represent the same subset of its spectrum. If one has
  norm-controlled preimages, so does the other. The universal properties
  give maps `ψ₁`, `ψ₂` between the two targets with `ψ₁ ∘ i₁ = i₂` and
  `ψ₂ ∘ i₂ = i₁`. Uniqueness gives `ψ₁ ∘ ψ₂ = id`. A preimage of `ψ₂ z` under
  `i₁` is then a preimage of `z` under `i₂`, and the bound of `ψ₂` enters the
  constant.
- `exists_lift_clopenRationalChart`: let `C` be a clopen subset of the
  spectrum of a presented affinoid algebra `B`. Its Weierstrass chart
  `clopenRationalChart C` (from `AffinoidIdempotents`) and that of the
  complement form a two-member finite cover of the whole spectrum. For an
  element `z` of the chart algebra, the family `(z, 0)` is compatible: a
  domain mapping to both charts has empty locus, so its algebra is the zero
  ring. Descent glues it to `c ∈ B` with `d.baseMap c = z`. The Library's
  `Domain.FiniteCover.norm_le_algebraRestrictionBound` gives
  `‖c‖ ≤ M max(‖z‖, ‖0‖) = M ‖z‖`.

## Clopen pieces of recognized subsets

Let `a` be an indexed affinoid atlas on `X` and `P` a recognized subset of its
full recognition. Let `O` be open with `P.locus ∩ closure O ⊆ O`.

- `isClopen_chart_preimage`: the preimage of `O` under the chart of `P` is
  clopen. It is open, and equals the preimage of `closure O` because the chart
  takes values in `P.locus`.
- `clopenPiece a P hO hcl` is the Library's recognized subset
  `fullRecognitionDomainRecognizedSubset` of the domain of `P.algebra` given
  by the Weierstrass chart of that clopen preimage.
- `clopenPiece_locus`: its locus is `P.locus ∩ O`, the chart image of the
  clopen preimage. `clopenPiece_subset` follows.
- `isFiniteBanach_restriction_clopenPiece`: the restriction from `P` to its
  clopen piece is a finite Banach map. The restriction represents the preimage
  of the piece's locus (Library's `restriction_represents`), which is the
  clopen preimage. The Weierstrass chart represents the same set and has
  norm-controlled preimages. Transfer them and apply
  `isFiniteBanach_of_lift`.

## Lemma 3.1.2

Let `g : StrongHom A.saturatedPresentation B.saturatedPresentation`.

`IsFiniteOver.finite_fibre`: if `g` is finite from `V` to `U` and `W ⊆ U` is a
recognized subset containing `x`, then `V ∩ g⁻¹{x}` is finite. Every such point
lies in the recognized piece `P` over `W` and is the chart image of a point
`s` of its spectrum. By the chart equation of the pair system, `s` lies in the
fibre of the finite Banach map `P(P, W)` over the point of `W` at `x`. That
fibre is finite (`BoundedAlgHom.finite_fibre`).

`IsFiniteOver.exists_small`: let `V`, `U` be open, `g` finite from `V` to `U`,
`y ∈ V` and `V₀` a neighborhood of `y`. Then there are open `V' ⊆ V₀ ∩ V` with
`y ∈ V'` and open `U' ⊆ U` such that `g` is finite from `V'` to `U'`.

1. Write `x = g(y)`. The target atlas is locally Hausdorff, so `x` has a
   neighborhood `H` with Hausdorff subspace topology.
   `exists_finite_recognized_nhds_subset` (from `FullRecognitionEtaleMorphisms`)
   gives finitely many recognized subsets `W` inside `interior H ∩ U`,
   containing `x`, with union a neighborhood of `x`. Their pieces
   `V ∩ g⁻¹(W)` are recognized subsets, hence compact and Hausdorff, and the
   fibre is finite.
2. `exists_isClopenOver_of_finite_fibre` gives open `O ⊆ V₀ ∩ V` containing
   `y` and open `𝒰 ∋ x` inside the union, with `O` relatively clopen in
   `V ∩ g⁻¹(𝒰)`. Set `V' = O ∩ g⁻¹(𝒰)` and `U' = 𝒰`.
3. For a recognized `W'' ⊆ 𝒰`, let `P''` be the old piece over `W''`. Since
   `P''.locus ⊆ V ∩ g⁻¹(𝒰)`, `O` is relatively clopen in `P''.locus`. The new
   piece is `clopenPiece P'' O`, with locus `V' ∩ g⁻¹(W'')`. The restriction
   law of the pair system writes its map as the restriction from `P''`
   composed with the old finite Banach map. Both are finite Banach, and finite
   Banach maps compose.

`IsFiniteAt.exists_small` is the pointwise form.

## Composition of quasifinite morphisms

- `IsFiniteOver.restrictTarget`: if `g` is finite from `V` to `U` and
  `U' ⊆ U`, then `g` is finite from `V ∩ g⁻¹(U')` to `U'`, with the same
  pieces.
- `IsFiniteAt.comp`: let `g` be finite from `V₁` to `U₁` at `y`, and `g'`
  finite at `g(y)`. Lemma 3.1.2 shrinks the source neighborhood of `g'` into
  `U₁`, so `g'` is finite from some `U₂ ⊆ U₁` to `T`. Restrict the target of
  `g` to `U₂` and compose (`IsFiniteOver.comp` of
  `FullRecognitionFiniteMorphisms`). The composite is the saturated composite.
- `IsQuasifinite.comp` applies this at every point.

## Scope

No Hausdorffness of the spaces, nontrivial valuation or strictness is assumed.
The following remain further work: composition of flat, unramified and étale
morphisms (Corollaries 3.2.6 and 3.3.8), which needs the independence of
pointwise flatness and unramifiedness from the chosen pieces; base change and
ground field extension; and the étale sites.
