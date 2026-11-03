# The actual adjoint real cocharacter and root-annihilator comparison

Author: Worker 1408.

`AdjointRealCocharacterComparisonStatement` is a Prop-valued statement
target. This file proves nothing. It quantifies over every field
`k : Type u`, with the universe `u` arbitrary, every pair of group schemes
`G` and `A` over `Spec k`, every pair of commutative group schemes `T` and
`T_ad`, and every quadruple of actual morphisms

- `q : G ⟶ A`,
- `i : T.toGrp ⟶ G`,
- `j : T_ad.toGrp ⟶ A`,
- `p : T ⟶ T_ad`,

satisfying the published `IsAdjointSplitTorusImage q i j p`. Under that
premise it asserts three conclusions:

1. `RealTorusSpace.cocharacterMapReal p : V T →ₗ[ℝ] V T_ad` is surjective.
2. `LinearMap.ker (cocharacterMapReal p) = RealTorusSpace.relativeCentralDirections i`.
3. There exists a real linear equivalence
   `e : Langlands.Geometry.Building.TranslationSpace i ≃ₗ[ℝ] V T_ad` with
   `e (Submodule.Quotient.mk v) = cocharacterMapReal p v` for every `v : V T`.

## Objects used

All objects are existing Library constructions, used by their Lean names.

- `IsAdjointSplitTorusImage q i j p` packages the following data:
  - `IsAdjointQuotient q`, an actual quotient of the connected reductive `G`
    by its full all-test centre.
  - Maximal splitness of `i` and of `j`.
  - The square `groupHom p ≫ j = i ≫ q`.
  - Flatness, surjectivity and local finite presentation of the scheme
    morphism underlying `p`.

  It contains no real-surjectivity field. In particular the statement does
  not assume `IsAdjointSplitTorusComparison` or its `realSurjective` field.
- `V T = ℝ ⊗[ℤ] X_*(T)` is the real cocharacter space.
  `cocharacterMapReal p` is the real scalar extension of actual
  postcomposition `ν ↦ ν ≫ p` on cocharacters.
- `relativeCentralDirections i` is the simultaneous annihilator in `V T` of
  all actual relative roots `relativeRoots i`. These roots are the nonzero
  characters of `T` with a nonzero weight space in the Lie algebra of `G`.
- `TranslationSpace i` is the existing apartment translation space
  `V T ⧸ rootAnnihilator i`, where `rootAnnihilator i` is by definition
  `relativeCentralDirections i`.

Both the root annihilator and the translation space need the instance
`IsAffineHom G.X.hom`. The statement obtains it from the original quotient,
as `h.isAdjointQuotient.isConnectedReductive.isAffineHom`. Neither
affineness nor any other instance is an extra premise.

The statement has no rank, local-field, characteristic, splitness-of-`G`,
finite-kernel, integral-surjectivity or primitive-lift premise. Rank zero is
retained. If `T` is central in `G` (no relative roots), then
`relativeCentralDirections i` is all of `V T`, and the conclusions say that
`V T_ad` is zero. The centre of `G` may be nonsmooth, and `p` is not required
to be finite. The adjoint quotient `q` is a reductive quotient by the full
centre. It is not a simply connected cover of the derived group, and no
central isogeny from a simply connected group appears.

Conclusion 3 follows from conclusions 1 and 2 by Mathlib's first isomorphism
theorem. It is included as a separate conjunct because the apartment
consumer needs exactly this map. Conclusion 1 together with the premise `h`
gives `IsAdjointSplitTorusComparison q i j p`. So the comparison interface
becomes a consequence of this target and is not one of its inputs.

## Provenance

The provenance is derived. No single cited result has these hypotheses and
this conclusion. The statement combines the following sources over an
arbitrary field. Below, "printed" pages are the source's own page numbers and
"PDF" pages are positions in the registered file.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §6.1(c),
printed pp.209–210 / PDF pp.240–241, treats a quasi-split reductive `G`. It
takes `S` a maximal `k`-split torus and `A_G` the maximal split central
torus. It gives the identifications (6.1.3)
`V(S′) = ℝ ⊗ X_*(T_sc)^Θ = ℝ ⊗ X_*(T_ad)^Θ = V(S/A_G)`, and states that the
action of `V(S)` on `A(S)` factors through the quotient map
`V(S) → V(S/A_G)`. The authors' corrections (version of 1 November 2024),
PDF p.32 (Chapter 6), replace the first two sentences of the third paragraph
of §6.1(c). The corrected text builds the apartment `A(S_ad)` from
valuations of the root datum of `(G_ad, S_ad)`. In Definition 6.1.27 the
corrections replace `S′` with `S_ad` and `G_der` with `G_ad`. This statement
follows the corrected version. Its translation target is `V` of the maximal
split torus of the adjoint group, not `V(S′)` for a torus of the derived
group. The Lean variable `T_ad` is KP's `S_ad` (the maximal split torus of
the adjoint group). It is not KP's maximal torus `T_ad`.

The Library's `TranslationSpace i` is `V(S)` modulo the common kernel of the
roots. `KPApartment.md` explains that this kernel is not identified there
with KP's `V(A_G)`. This statement therefore uses the root annihilator
directly and does not mention `A_G`. The identification of the root
annihilator with the split component is the separate published target
`RelativeSplitCentralDirectionsStatement` (in
`Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement`), whose
proof belongs to another task. This statement neither restates nor assumes
that identification.

The intended algebraic route, which the proof successor need not follow:

- Kernel of `p`. The published theorem
  `IsAdjointSplitTorusImage.mem_range_kernel_iff` identifies the actual
  kernel of `p` on all test schemes with `T ∩ Z(G)`.
- Kernel of `Ad` on a maximal torus. Milne, *Algebraic Groups* (2017),
  Proposition 21.7, printed p.427 / PDF p.443, shows that for a maximal torus
  `T′` of a reductive group, the centre `Z(G)` lies in `T′` and equals the
  kernel of `Ad : T′ → GL(𝔤)`. Corollary 21.9 (same page) gives the split
  case: the character group of `T′/Z(G)` is the root lattice `ℤΦ`.
- Passage to relative roots. Milne 25.13, printed p.548 / PDF p.564,
  decomposes `𝔤 = 𝔤_0 ⊕ ⊕ 𝔤_α` under a maximal split torus `S` and defines
  the relative roots. Its footnote 2 says that these are the restrictions to
  `S` of the absolute roots. Borel–Tits, *Groupes réductifs* (1965), proof of
  Théorème 5.3, printed p.96 / PDF p.43, uses that the adjoint representation
  has kernel `Z(G)`, together with the vanishing of absolute roots, to
  identify `(Z(G) ∩ S)°` with the connected common kernel of the `k`-roots.
  Here the comparison is needed scheme-theoretically: `T ∩ Z(G)` should be
  the intersection of the kernels of the relative roots, so that its
  character group is `X^*(T)/ℤΦ_k`.
- Characters of the image. Milne Theorem 12.9(b), printed pp.233–234 / PDF
  pp.249–250, says that `D` and `X` are exact on diagonalizable groups. The
  fppf map `p` then identifies `X^*(T_ad)` with the subgroup `ℤΦ_k` of
  `X^*(T)`.
- Real duals. Dualizing over `ℝ` gives a surjective map
  `V T → Hom(ℝΦ_k, ℝ)`, and its kernel is the annihilator of the relative
  roots.

Milne Corollary 17.62(e) and Remark 17.63, printed pp.372–373 / PDF
pp.388–389, describe the adjoint group as the quotient of a reductive group
by its centre. This matches the published `IsAdjointQuotient`. The official
Milne errata snapshot of 2026-11-02 has no correction to the cited Milne
passages.

KP state their results for quasi-split groups over their fields. The
arbitrary-field scope here is a derived algebraic formulation using Milne and
Borel–Tits. The statement compares actual morphisms and the published real
cocharacter map. It does not identify two abstract vector spaces of the same
dimension, and it claims nothing about integral cocharacter lattices.
