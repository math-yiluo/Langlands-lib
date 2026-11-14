# Central endomorphisms of `i_P σ` induced from `σ`: a criterion

Module `Langlands.Representation.CuspidalSupport.InducedCenterCriterion`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

This module is an internal helper. It is not a result of the literature as stated. It supports
the Lean proof `bernsteinInvariantCenterInclusion` of Renard 2026, VI.10.4, `ℨ_D^{W(D)} ⊂ ℨ_Ω`
(`CuspidalSupport/BernsteinBlockCenterFunctionsInvariantCenterProof`). Renard's route uses
second adjointness, the projectivity of `Π_D` and a bimodule filtration of `End_G(i_P Π_D)`.
This module replaces those inputs by ordinary Frobenius reciprocity
(`leviFrobeniusReciprocity`) and the support filtration of `r_P(i_P σ)` from the represented
geometric lemma, the setting already used by `InducedKernelVanishing`. It needs no conditional
input.

## The main theorem

`leviInduction_map_mem_center_of_twistedCommutation`. Let `k` be a non-archimedean local field,
`G` connected reductive (`hG`), `P = M N` an actual rational parabolic with data
`p, l, r, hp, hr, hl, hmul`, and `M(k)` with the Levi point topology. Let `σ` be a smooth
representation of `M(k)` (carriers in `Type (max u v)`) such that

- (`hsc`) `σ` is supercuspidal (`IsSupercuspidal`, for every proper represented parabolic);
- (`hfix`) no `t ∈ M(k)` with `tⁿ ∉ ⁰M(k)` for all `n > 0` fixes a nonzero vector of `σ`.

Let `ζ` be central in `End(σ)` (`hζc`), and assume (`hζ`): for every `w ∈ G(k)` and
automorphism `φ` of the group scheme `M` with `φ ≫ (l ≫ p) = (l ≫ p) ≫ Int(w)`, every
`ℂ`-linear `T : σ → σ` with `T(σ(m) v) = σ(φ(m)) (T v)` for all `m, v` satisfies
`T(ζ v) = ζ(T v)`. Then `i_P(ζ)` lies in the centre of `End(i_P σ)`, where `i_P` is
`leviInductionFunctor p l r hp hr hl hmul`.

## Generic helpers

- `map_comp_eq_comp_of_iso`: an identity `B(a) ≫ g = g ≫ β` for all maps `g` out of `B X`
  transfers to all maps out of `A X` along a natural isomorphism `A ≅ B`.
- `eq_zero_of_iso_subsingleton`: maps out of `A X` vanish when `A ≅ B` and `B X` is zero.
- `mulEquiv_apply_mem_center_iff`: a group isomorphism (any `MulEquivClass`) preserves and
  reflects membership in the centre.
- `centerEndomorphism σ c hc`: for `c` central, `σ(c)` as an endomorphism of `σ`;
  `centerEndomorphism_apply` is its value.

## Pieces of the support filtration

The support filtration of `r_P(i_P σ)` (`leviJacquetSupportFiltration`) is indexed by an
ordering of `P(k) \ G(k) / P(k)`. Its graded pieces are naturally isomorphic to the piece
functors `(E i).pieceFunctor` of intersection data `E i` at the inverse representatives
(`representedGeometricLemmaSupportGraded_of_orbitComparison`). A datum `D` is *full* when
`D.p'` is an isomorphism; then `D.q'` is one too (`isIso_q'_of_isIso_p'_of_iso`), `D` yields
an automorphism `φ_D` of `M` with `φ_D ≫ (l ≫ p) = (l ≫ p) ≫ Int(z⁻¹)` (`fullLeviConjugacy`),
its point map `ψ_D` (`fullLeviPointsEquiv`, with `ψ_D(m) = φ_D(m)` by
`fullLeviPointsEquiv_apply`), and a linear identification `E` of the piece at `σ` with `σ`,
on which `x ∈ M(k)` acts by `σ(ψ_D⁻¹ x)` (`fullPieceEquiv`), natural in `σ`
(`fullPieceEquiv_naturality`). When `D` is not full, the piece at a supercuspidal `σ` is zero
(`subsingleton_pieceFunctor_obj`).

- `fullPiece_hom_comm_of_twisted`: on a full piece, every map `g` to `σ` satisfies
  `piece(ζ) ≫ g = g ≫ ζ` if `ζ` commutes with the twisted maps along `φ_D`. Proof:
  `T = g ∘ E⁻¹` satisfies `T(σ(m) v) = σ(φ_D m)(T v)` (equivariance of `E⁻¹` and `g`), so
  `T ζ = ζ T`; by naturality `piece(ζ) = E⁻¹ ∘ ζ ∘ E`.
- `fullPiece_hom_comm_center`: on a full piece, for `c` central, every map `g` to `σ` satisfies
  `piece(σ(c)) ≫ g = g ≫ σ(ψ_D c)`. Proof: by naturality and the action formula,
  `piece(σ(c))` is the action of `ψ_D(c)` on the piece, and `g` is equivariant.
- `eq_zero_of_comp_centerEndomorphism_eq`: if `a, b` are central with `|χ|(b) ≠ |χ|(a)` for a
  rational character `χ`, then under `hfix` every map `d` into `σ` with
  `σ(b) ∘ d = σ(a) ∘ d` is zero. Proof: `t = b⁻¹ a` fixes every `d(y)`, and
  `|χ|(tⁿ) = (|χ|(b)⁻¹ |χ|(a))ⁿ ≠ 1` for `n > 0`, so `tⁿ ∉ ⁰M(k)`; then `hfix`.
- `not_mem_pointImage_of_ne`: for distinct orbits `j ≠ k` of an ordering,
  `w_j w_k⁻¹ ∉ M(k)`. Otherwise `P w_j⁻¹ = P w_k⁻¹ (w_j w_k⁻¹)⁻¹` lies in both orbits, which
  are disjoint.
- `exists_center_norm_ne_of_fullPieces`: for full data `D_j, D_k` at `z_j, z_k` with
  `z_j⁻¹ z_k ∉ M(k)`, some central `c` and rational character `χ` have
  `|χ|(ψ_j c) ≠ |χ|(ψ_k c)`. Proof: `φ = φ_k⁻¹ ≫ φ_j` satisfies
  `φ ≫ (l ≫ p) = (l ≫ p) ≫ Int(z_j⁻¹ z_k)` (`innerIso_mul_hom`, `innerIso_one_hom`). The
  contrapositive of Renard V.3.5 (`leviNormalizerNormFixing`) gives a central `a` and `χ` with
  `|χ|(φ a) ≠ |χ|(a)`. Take `c = φ_k⁻¹(a)`: then `ψ_k c = a` and `ψ_j c = φ(a)`.
- `leviJacquetSupportFiltration_graded_comm`: hypothesis `hA` of the dévissage: on every
  graded piece, every map to `σ` intertwines `ζ` (full pieces by
  `fullPiece_hom_comm_of_twisted` with `hζ` at `w = z⁻¹`, other pieces are zero).
- `fullPieces_separated`: for full data at `z_j, z_k` with `z_j⁻¹ z_k ∉ M(k)`, functors
  `A_j ≅` piece `j`, `A_k ≅` piece `k`, and `d : A_k σ → σ` satisfying the premise of `hB`,
  `d = 0`. Proof: with `c` from `exists_center_norm_ne_of_fullPieces`, the pair
  `(σ(c), σ(ψ_j c))` commutes with `ζ` (centrality of `ζ`) and is intertwined by all maps from
  `A_j σ` (`fullPiece_hom_comm_center`), so `A_k(σ(c)) ≫ d = d ≫ σ(ψ_j c)`; also
  `A_k(σ(c)) ≫ d = d ≫ σ(ψ_k c)`. Conclude with `eq_zero_of_comp_centerEndomorphism_eq`.
- `leviJacquetSupportFiltration_graded_separated`: hypothesis `hB` of the dévissage. If the
  piece `k` is not full, `d = 0`. If the piece `j` is not full, the pair `(𝟙, 0)` gives
  `d = 0`. Otherwise `fullPieces_separated` applies, with `not_mem_pointImage_of_ne`.

## Proof of the main theorem

The orbit setup copies `leviJacquetInduction_hom_apply_mk_eq_zero`
(`InducedKernelVanishing`): `representedGeometricLemmaGeometry` gives the intersection data and
a finite classification of the double cosets; `closedSubgroupOrbitOrdering_of_finiteOrbitOrdering`
with `finiteOrbitOrdering` gives an ordering `s`; `classifiedRepresentatives` replaces its
representatives by the inverses of the classified points, giving `t0` and data `E i` at
`(t0.representative i)⁻¹`; `representedGeometricLemmaSupportGraded_of_orbitComparison` gives
the graded pieces. No orbit needs to be moved to the end.

`RepFunctorFiltration.map_comp_eq_comp_of_graded` (`Filtration/CommutingHomDevissage`) with
`F = leviJacquetInductionFunctor`, `X = σ`, `Y = σ`, `z = ζ` and the two hypotheses above shows
that every `M(k)`-map `H : r_P(i_P σ) → σ` satisfies `H(r_P(i_P ζ) y) = ζ(H y)`.

Let `e` be the Frobenius isomorphism of `leviFrobeniusReciprocity`, with
`e(F)(mk f) = ev₁(F f)`. For `a ∈ End(i_P σ)`, both `i_P(ζ) ≫ a` and `a ≫ i_P(ζ)` have the same
image under `e`: on `mk f`, the first gives `e(a)(r_P(i_P ζ)(mk f))`, the second
`ζ(e(a)(mk f))`, and these agree by the previous paragraph. Since `e` is injective,
`a * i_P(ζ) = i_P(ζ) * a`.

## Technical notes

The file sets `backward.isDefEq.respectTransparency false`, like `InducedKernelVanishing`.
Calls of the lemmas carrying `σ : SmoothRep.{0, u, max u v}` give the universes explicitly
(`.{u, v}`); otherwise unification of `max u ?v` with `max u v` stalls. Several declarations
raise `maxHeartbeats` to 800000 or 1600000.
