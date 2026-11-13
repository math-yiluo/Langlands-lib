# Affine charts: the section lies in the smooth locus

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). It proves the local theorem used in that proof, except for one algebraic
input, which is taken as the hypothesis `homega`. Let `S` be reduced and locally Noetherian,
`q : Y → S` locally of finite type with a section `e`, and suppose the residue fibres of `q`
over an open `U` are smooth of relative dimension `n`. Then `q` is smooth at `e s` for every
`s ∈ U`.

The declaration is in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all schemes
and rings lie in one universe `u`.

## Declaration

`mem_smoothLocus_of_fibres_of_finrank`. Hypotheses:

- `homega`: for all commutative rings `R`, `B` with `B` an `R`-algebra, every prime `p` of
  `R`, every prime `Q` of `B` lying over `p` (`Q.LiesOver p`) and every `n : ℕ`, assume that
  `Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField (p.Fiber B)))` is
  `SmoothOfRelativeDimension n`. Here `p.Fiber B` is `κ(p) ⊗[R] B`. Then
  `Module.finrank Q.ResidueField (Q.ResidueField ⊗[B] Ω[B⁄R]) = n`;
- `S` is reduced and locally Noetherian, `q : Y ⟶ S` is locally of finite type, and
  `e : S ⟶ Y` satisfies `e ≫ q = 𝟙 S`;
- `n : ℕ` and `U : S.Opens`, with `q.fiberToSpecResidueField t` `SmoothOfRelativeDimension n`
  for every `t ∈ U`;
- `s : S` with `s ∈ U`.

Conclusion: `e s ∈ q.smoothLocus`.

The hypothesis `homega` is exactly the statement of
`Langlands.GroupScheme.ReducedBaseSmooth.finrank_residueField_tensor_kaehler_eq` (Worker 50,
`OmegaRank.lean`). The unconditional form `mem_smoothLocus_of_fibres` is obtained by
supplying that theorem; it is stated in the final proof module.

## Provenance

This is an internal lemma with a derived name. It is the step "the unit section lies in the
smooth locus" of the route used for SGA 3 VI_B 4.4. The route differs from SGA 3, which
proves flatness through EGA IV₃ 15.6.7 instead.

## Proof

Choose an affine open `V ∋ s` of `S` and an affine open `W ∋ e s` of `Y` with
`W ⊆ q⁻¹(V)`, using the bases of affine opens. Let `R = Γ(S, V)`, `A = Γ(Y, W)`, and let
`φ = q.appLE V W : R → A`. Then `A` is a finite type `R`-algebra
(`Scheme.Hom.finiteType_appLE`), and `Spec φ` is compatible with `q` through the open
immersions `Spec R → S` and `Spec A → Y` (`IsAffineOpen.SpecMap_appLE_fromSpec`). Let `x`
and `y` be the points of `Spec R` and `Spec A` over `s` and `e s`. Injectivity of
`Spec R → S` gives `Spec φ (y) = x`, so the prime `y` lies over the prime `x`.

1. The residue fibre of `Spec φ` at `x` is smooth of relative dimension `n`. First,
   `smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion` restricts the hypothesis at `s`
   to `Spec A → Y → S`. Then `smoothOfRelativeDimension_fiber_of_isPullback`, for the square
   of `Spec φ` along the open immersion `Spec R → S`, moves it to `Spec φ`. Mathlib's
   `Spec.fiberToSpecResidueFieldIso` identifies this fibre with
   `Spec (κ(x) ⊗[R] A) → Spec κ(x)`.
2. `homega` gives `finrank κ(y) (κ(y) ⊗[A] Ω[A⁄R]) = n`.
3. `exists_span_eq_top_of_finrank_eq` gives `a : Fin n → A` whose differentials span this
   cotangent fibre.
4. `exists_closedImmersion_smooth_of_span` gives `f ∉ y` and a closed immersion
   `i0 : Spec A[1/f] → Z0` into a scheme `p0 : Z0 → Spec R` that is smooth of relative
   dimension `n`, quasi-compact and quasi-separated, with `i0 ≫ p0 = Spec(R → A[1/f])`.
5. Let `ιY : Spec A[1/f] → Spec A → Y`, an open immersion. Then
   `Spec(R → A[1/f]) ≫ (Spec R → S) = ιY ≫ q`. The point `e s` lies in the range of `ιY`
   because `f ∉ y` (`PrimeSpectrum.localization_away_comap_range`).

`mem_smoothLocus_of_closedImmersion_chart` (in `Local.lean`) now applies with
`ιV = (Spec R → S)`, `ιY`, `g = Spec(R → A[1/f])`, `p0` and `i0`. It needs `q` locally of
finite presentation, which holds because `q` is locally of finite type over a locally
Noetherian base.
