# `(G, M)`-families

Module `Langlands.LinearAlgebra.GMFamilies`, namespace `Langlands.GMFamily`. The lemmas of Arthur 2005, §17, about these objects are stated in
`Langlands.LinearAlgebra.GMFamiliesStatement` (see its Markdown).

The module defines Arthur's `(G, M)`-families and every object that his Lemmas 17.1 and 17.4–17.6
use: `𝓟(M)`, `𝓕(M)`, `𝓛(M)`, `Δ_P`, `θ_P`, `θ̂_P^Q`, `c_M`, `c_M^Q`, the restrictions `c_Q`,
(17.7), the coefficients `d_{M₁}^G(M, L₁)` and `d_M^G(L₁, L₂)` and the sections of Lemmas 17.5
and 17.6. It proves two lemmas, `gramVolume_smul` and `thetaOf_smul`. Every definition is total.
Outside the intended range (a set `a` that is not a Levi space, a set of roots that is not a
chamber) the definitions are formulas without meaning.

## Source

J. Arthur, *An introduction to the trace formula*, in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12), §17,
printed pp.93–101:

- p.93: for a Levi subgroup `M` over `k` and `P ∈ 𝓟(M)`, smooth functions `c_P(λ)`, `λ ∈ i𝔞_M^*`,
  form a `(G, M)`-family if `c_P(λ) = c_{P'}(λ)` for adjacent `P, P'` and `λ` in the hyperplane
  spanned by the common wall of the chambers `i(𝔞_M^*)_P^+` and `i(𝔞_M^*)_{P'}^+`;
- p.94: a Haar measure on `𝔞_M^G` is fixed and
  `θ_P(λ) = vol(𝔞_M^G / Z(Δ_P^∨))⁻¹ ∏_{α ∈ Δ_P} λ(α^∨)`, `Z(Δ_P^∨)` the lattice spanned by the
  basis `Δ_P^∨` of `𝔞_M^G`; Lemma 17.1, (17.1) `c_M(λ) = ∑_{P ∈ 𝓟(M)} c_P(λ) θ_P(λ)⁻¹`;
- pp.96–97: `θ̂_P^Q(λ) = vol(𝔞_P^Q / Z((Δ̂_P^Q)^∨))⁻¹ ∏_{ϖ ∈ Δ̂_P^Q} λ(ϖ^∨)`, (17.7)
  `c'_P(λ) = ∑_{Q ⊃ P} (−1)^{dim(A_P/A_Q)} c_Q(λ_Q) θ̂_P^Q(λ)⁻¹ θ_Q(λ_Q)⁻¹`, the restrictions
  `c_R^Q(λ) = c_{Q(R)}(λ)` (an `(M_Q, M)`-family) and `c_Q(λ) = c_P(λ)` for `λ ∈ i𝔞_L^*`,
  `Q ∈ 𝓟(L)`, `P ⊆ Q` (a `(G, L)`-family), and the remark that (17.7) applies to any `Q`;
- p.97: the product family `(cd)_P = c_P d_P`;
- pp.99–100: the `(G, M)`-family `c_P(λ) = c_{P₁}(λ)` induced from a `(G, M₁)`-family for a Levi
  subgroup `M₁ ⊆ M` over an extension `k₁` of `k`; the coefficient `d_{M₁}^G(M, L₁)`, `0` unless
  `𝔞_{M₁}^M ⊕ 𝔞_{M₁}^{L₁} → 𝔞_{M₁}^G` is an isomorphism, and then the factor by which the product
  measure must be multiplied to give the measure on `𝔞_{M₁}^G`, the measure on `𝔞_{M₁}^M` being
  the quotient of those on `𝔞_{M₁}^G` and `𝔞_M^G`. (The printed `𝔞_{M₁}^L ⊕ 𝔞_{M₁}^{L₁}` in the
  measure clause is a misprint for `𝔞_{M₁}^M ⊕ 𝔞_{M₁}^{L₁}`.) Arthur suggests the measures of a
  Euclidean inner product on `𝔞_{M₁}`; the section `L₁ ↦ Q₁` defined by a small `ξ ∈ 𝔞_{M₁}^M` in
  general position;
- pp.100–101: the diagonal variant `M ⊆ M × M ⊆ G × G`, the coefficient `d_M^G(L₁, L₂)`
  (with the printed relation `d_{𝐌}^{𝐆}(M, 𝐋) = 2^{dim(𝔞_M^G)/2} d_M^G(L₁, L₂)`, discussed under
  `dCoeff` below) and the section
  `(L₁, L₂) ↦ (Q₁, Q₂)`: writing `ξ = ½ξ₁ − ½ξ₂`, `Qᵢ` is the group of `𝓟(Lᵢ)` with
  `ξᵢ ∈ 𝔞_{Qᵢ}^+`.

J. Arthur, *The invariant trace formula. I. Local theory*, J. Amer. Math. Soc. 1 (1988),
registered as `arthur-1988-invariant-trace-formula-I` (PDF page = printed page − 322), §7, printed
pp.355–358: special subspaces, the coefficients `d_M^G(b, L)` (volume of the parallelogram of
orthonormal bases of `𝔞_M^b` and `𝔞_M^L`), Proposition 7.1 and Corollary 7.4,
`(cd)_M = ∑_{L₁, L₂} d_M^G(L₁, L₂) c_M^{Q₁} d_M^{Q₂}`.

## The model

- `E` is a finite-dimensional real inner product space: Arthur's `𝔞_0` (more precisely the space
  `𝔞_{M_0}` of a minimal Levi subgroup over the field `k` of `M`) with a Weyl-invariant inner product,
  which fixes all the Haar measures (Euclidean measures of the subspaces), as Arthur suggests on
  p.99.
- `R : Finset E` is the set of roots of `(G, A_{M_0})`, each written as the vector `α^♯` with
  `α(H) = ⟪α^♯, H⟫`. It may be nonreduced. `IsRootSet R` records the root-system axioms: `0 ∉ R`,
  stability under the orthogonal reflections, integrality of `2⟪β, α⟫/⟪α, α⟫`.
- A Levi subgroup `M ⊇ M_0` is recorded by `a = 𝔞_M ⊆ E`, an intersection of root hyperplanes:
  `IsLeviSpace R a` says `a = leviSpaceOf R h₀` for a point `h₀` (the common kernel of the roots
  vanishing at `h₀`). Every Levi subgroup of `G` over `k` is conjugate to one containing `M_0`, and
  conjugate Levi subgroups have isomorphic data, so this records every `M` up to conjugacy.
- `λ ∈ i𝔞_M^*` is written `λ = iΛ` with `Λ : StrongDual ℝ a`, so that `λ(H) = i Λ(H)`. The
  functions of a family are functions `StrongDual ℝ a → ℂ`; smooth means `ContDiff ℝ ∞`.
- `centralSpace R` is `𝔞_G`, the common kernel of the roots.

## Definitions

- `restrictedRoot a α`: the orthogonal projection of `α` to `a`, the vector of the restriction of
  `α` to `𝔞_M`. For a root `β` with `β|_{𝔞_M} = α`, Arthur's coroot `α^∨` (the projection of `β^∨`
  for the simple root `β` of a minimal parabolic contained in `P`) is
  `(2/⟪β, β⟫) · restrictedRoot a β`: the decomposition `𝔞_0 = 𝔞_0^M ⊕ 𝔞_M` is orthogonal for a
  Weyl-invariant inner product and `β^∨ = 2β/⟪β, β⟫`. So `restrictedRoot` gives positive multiples
  of Arthur's coroots, in the same direction. (This computation is not formalized.)
- `IsRegular R a h`, `posSet R h`: regular points of `a` (no root nonzero on `a` vanishes at `h`)
  and the roots positive at `h`.
- `parabolics R a` is `𝓟(M)`: the sets `posSet R h` for regular `h ∈ a`, one for each chamber of
  `a`. A group `P ∈ 𝓟(M)` is recorded by its set of roots positive on its chamber, which determines
  it. `faces R a` is `𝓕(M)`: the sets `posSet R h` for all `h ∈ a`, one for each face of a chamber,
  that is, each parabolic subgroup containing `M`. `G` itself is the empty set.
- `restrictedRoots a S`, `simpleRoots a S`: the restricted positive roots of `S` and `Δ_P`, those
  that are not sums of two restricted positive roots. For a Levi space these are the restrictions
  of the simple roots of a minimal parabolic subgroup contained in `P` that do not vanish on `𝔞_M`
  (a standard root-system fact, not proved here).
- `gramVolume v = √det(⟪vᵢ, vⱼ⟫)`: the Euclidean volume of the parallelepiped spanned by `v`. For
  a linearly independent family, such as `Δ_P`, this is the covolume of the lattice `Z(v)` in its
  span; for `Δ_P` the span is `𝔞_M^G`. For a dependent family it is `0` (two copies of a unit
  vector have Gram volume `0`, although the lattice they generate has covolume `1` in its span).
- `thetaOf a v Λ = gramVolume(v)⁻¹ ∏ᵢ (i Λ(vᵢ))`, and `theta a S = thetaOf` of `simpleRoots a S`.
  This is `θ_P(iΛ)` with Arthur's coroots replaced by the positive multiples
  `simpleRoots a S`. `thetaOf_smul` proves that rescaling the vectors by positive numbers does not
  change the value (both the volume and the product scale by the product of the factors;
  `gramVolume_smul`). Hence `theta a S` is exactly Arthur's `θ_P`.
- `IsAdjacentAlong R a S S' v`: `v ∈ Δ_P`, `−v ∈ Δ_{P'}`, and every root whose restriction is not
  a multiple of `v` has the same sign on both chambers. These are the adjacent pairs, and the
  hyperplane spanned by the common wall of `i(𝔞_M^*)_P^+` and `i(𝔞_M^*)_{P'}^+` is `Λ(v) = 0`.
- `IsFamily R a c`: each `c S`, `S ∈ 𝓟(M)`, is smooth, and `c S Λ = c S' Λ` whenever `S, S'` are
  adjacent along `v` and `Λ v = 0`. This is Arthur's definition. Only the direction of `v` enters.
- `cM R a c Λ = ∑_{S ∈ 𝓟(M)} c S Λ · (theta a S Λ)⁻¹`, Arthur's (17.1). At singular `Λ` Lean's
  convention `0⁻¹ = 0` applies; Lemma 17.1 concerns the regular `Λ`.
- `familyMul`: the product family.
- `leviRoots R Q`: the roots of `M_Q` for `Q ∈ 𝓕(M)`, neither positive nor negative on `Q`.
  `faceSpace R a Q` is `𝔞_Q`. `leviSpaces R a` is `𝓛(M)`, the spaces `𝔞_L`, `L ⊇ M`.
- `paramProj a b Λ` is `λ ↦ λ_b`, the projection of `i𝔞_M^*` onto `i𝔞_b^*` for `b ⊆ a`, through
  the orthogonal projection `𝔞_M → 𝔞_b` (the decomposition `𝔞_M = 𝔞_M^L ⊕ 𝔞_L` is orthogonal).
  `restrictParam a b Λ` restricts `Λ` to `b`; `extendParam a a₁ Λ` extends `Λ ∈ 𝔞_M^*` to
  `𝔞_{M₁}^* ⊇ 𝔞_M^*` for `a ⊆ a₁`.
- `famRestrict R a c Q Λ = c_P(λ_Q)` for a chosen `P ∈ 𝓟(M)` with `P ⊆ Q` (positive roots of `Q`
  among those of `P`): Arthur's `c_Q(λ_Q)`. For a family the value does not depend on the choice;
  this is not proved here.
- `cQM R a c Q Λ = ∑_{S ∈ 𝓟^{M_Q}(M)} c(Q ∪ S)(Λ) · θ_S^Q(Λ)⁻¹`: Arthur's `c_M^Q`. The
  chambers `𝓟^{M_Q}(M)` are `parabolics (leviRoots R Q) a`, and `Q(S) ∈ 𝓟(M)` has positive roots
  `Q ∪ S`. For `Q ∈ 𝓟(M)` it reduces to `c_Q`.
- `gram`, `coweight s v = ∑_u (G⁻¹)_{vu} u`: the coweights, the basis dual to `s` (exact, not up to
  scale). `thetaHat S Λ` is `θ̂_P^Q` for the chamber `S` of `b = 𝔞_P` among the roots of `M_Q`:
  the volume of the coweight lattice and the product of the `λ(ϖ^∨)`.
- `dPrime R a d Q Λ` is (17.7) for `Q ∈ 𝓕(M)` and the `(G, M_Q)`-family restricted from `d`:
  `∑_{Q' ⊇ Q} (−1)^{dim 𝔞_Q − dim 𝔞_{Q'}} d_{Q'}(λ_{Q'}) θ̂_Q^{Q'}(λ)⁻¹ θ_{Q'}(λ_{Q'})⁻¹`. Here
  `Q' ⊇ Q` is `Q' ⊆ Q` as sets of positive roots, `θ̂_Q^{Q'}` is `thetaHat` for the chamber
  `Q ∩ leviRoots R Q'` of `𝔞_Q`, and `θ_{Q'}` is `theta` for the chamber `Q'` of `𝔞_{Q'}`.
- `measureFactor U W V`: the volume of the parallelepiped spanned by orthonormal bases of `U` and of
  `W`, and `0` unless `dim U + dim W = dim V`. For `U, W ⊆ V` this is the factor `d` with
  `dV = d (dU × dW)` under `U ⊕ W → V`, and it is nonzero exactly when that map is an isomorphism.
- `dCoeff R a L₁ L₂` is `d_M^G(L₁, L₂)`, the factor for `𝔞_M^{L₁} ⊕ 𝔞_M^{L₂} → 𝔞_M^G`, where
  `𝔞_M^L = 𝔞_M ∩ 𝔞_L^⊥`, with the Euclidean measures. This is the coefficient of Arthur 1988,
  Corollary 7.4 (printed p.358), whose product formula Lemma 17.6 restates.
  **Normalization note.** Arthur 2005 (p.101) introduces `d_M^G(L₁, L₂)` through the diagonal
  `M ⊆ 𝐌 = M × M ⊆ 𝐆 = G × G` and prints `d_{𝐌}^{𝐆}(M, 𝐋) = 2^{n/2} d_M^G(L₁, L₂)`, where
  `n = dim 𝔞_M^G`; Arthur 1988 (p.358) prints the same positive exponent in the corresponding
  comparison just before Corollary 7.4. The coefficient `d_{𝐌}^{𝐆}(M, 𝐋)` is the descent
  coefficient of p.100 for `M ⊆ 𝐌`: the factor `d` with `d · (μ_anti × μ_𝐋) = μ_𝐆`, where `μ_𝐆` is
  the measure on `𝔞_𝐌^𝐆 = 𝔞_M^G ⊕ 𝔞_M^G`, `μ_𝐋` the measure on
  `𝔞_𝐌^𝐋 = 𝔞_M^{L₁} ⊕ 𝔞_M^{L₂}` and `μ_anti` a measure on the antidiagonal
  `𝔞_𝐌^M = {(H, −H)}`. Take product Euclidean measures for `μ_𝐆` and `μ_𝐋`. Two choices of
  `μ_anti` give the following ratios to the direct coefficient `dCoeff`:
  - `μ_anti` the Euclidean measure of the antidiagonal for the product inner product (orthonormal
    bases, as in the definition on Arthur 1988, p.356): `d = 2^{−n/2} dCoeff`;
  - `μ_anti` the quotient of `μ_𝐆` by the Euclidean measure of `𝔞_M^G` carried to the diagonal by
    `H ↦ (H, H)`, which is Arthur's quotient convention on p.100: this quotient is `2^{n/2}` times
    the Euclidean measure of the antidiagonal, so `d = 2^{−n} dCoeff`.

  Rank-one check: for
  `𝔞_M^G = ℝ` and `(L₁, L₂) = (M, G)`, `dCoeff = 1`. In the first case `d` is the Gram volume of
  `(1, −1)/√2` and `(0, 1)`, which is `1/√2`. In the second, in coordinates `(x, y) = (t + s, t − s)`
  the product area is `dx dy = 2 dt ds`, so the quotient measure of the antidiagonal is `2 ds` in the
  coordinate `s` of `(s, −s)`; the map `(s, w) ↦ (s, −s + w)` from the antidiagonal times
  `𝔞_𝐌^𝐋 = {(0, w)}` pulls `dx dy` back to `ds dw`, so `d · 2 ds dw = ds dw` and `d = 1/2`. The
  printed value is `√2`. Neither normalization gives the printed exponent `+n/2`, and this module
  does not identify one that does. Lemma 17.6 is stated with the direct coefficient `dCoeff`,
  which is the coefficient of Arthur 1988, Corollary 7.4 (defined by the orthonormal-basis volume
  of p.356 for the pair `𝔞_M^{L₁}`, `𝔞_M^{L₂}`); the formula does not pass through the diagonal
  coefficient.
- `dDescent a z a₁ L₁` is `d_{M₁}^G(M, L₁)` with `z = 𝔞_G`: the factor for
  `𝔞_{M₁}^M ⊕ 𝔞_{M₁}^{L₁} → 𝔞_{M₁}^G`, with `𝔞_{M₁}^M = 𝔞_{M₁} ∩ 𝔞_M^⊥`. For Levi subgroups
  `M₁ ⊆ M` of `G` over the same field, `𝔞_{M₁}^M` is the kernel of the natural projection
  `𝔞_{M₁} → 𝔞_M` (it is `𝔞_{M₁}` intersected with the span of the coroots of `M`, orthogonal to
  `𝔞_M` for a Weyl-invariant inner product), and the quotient measure on it is the Euclidean one,
  as `𝔞_{M₁}^G = 𝔞_{M₁}^M ⊕ 𝔞_M^G` is orthogonal. This is also Arthur 1988's `d_{M₁}^G(b, L₁)` (§7,
  printed p.356; his `M` is our `M₁`) for `b = 𝔞_M`.
- `descentSection R a z ξ L₁`: the chamber of `𝔞_{L₁}` containing the point of
  `(ξ + 𝔞_M^G) ∩ 𝔞_{L₁}^G`; `splittingSection R ξ L₁ L₂`: the chambers of `ξ₁` and `ξ₂` when
  `2ξ = ξ₁ − ξ₂` with `ξᵢ ∈ 𝔞_{Lᵢ}^G`. Arthur's `ξ ∈ 𝔞_{𝐌}^M = {(H, −H)}` has an `𝔞_G`-part that
  does not affect the chambers; the formulation here takes `ξ ∈ 𝔞_M^G`, an equivalent choice. The
  points are chosen when they exist; when the relevant map is an isomorphism they are unique.
- `inducedFamily R a a₁ c₁`: the family `c_P(λ) = c_{P₁}(λ)` for a chosen `P₁ ∈ 𝓟(M₁)` with
  `P₁ ⊆ P` and `λ ∈ i𝔞_M^* ⊆ i𝔞_{M₁}^*`, the inclusion being `extendParam` (dual to the
  orthogonal projection `𝔞_{M₁} → 𝔞_M`). For Levi subgroups over the same field this is the
  inclusion of Arthur's character spaces. For a Levi subgroup `M₁` over a proper extension `k₁`
  the inclusion `𝔞_M^* ⊆ 𝔞_{M₁}^*` of rational characters need not be dual to an orthogonal
  projection for a Weyl-invariant inner product (see the Markdown of the statement module); the
  definitions are not used in that case.

## Choices and qualifications

- The coroots enter only through their directions, as explained above, and the measures are those
  of the inner product. Arthur allows any Haar measure on `𝔞_M^G` with the compatibilities his
  formulas need; Euclidean measures of a Weyl-invariant inner product satisfy them, and rescaling
  the inner product rescales them.
- The model is a space with a root set, not an actual group. The comparison with the actual
  relative root system of a connected reductive group (the space `V T` of
  `Langlands.GroupScheme.ArthurRelative` with a Weyl-invariant inner product, and its relative
  roots) is not part of this module.
- Choices of `P ⊆ Q` and `P₁ ⊆ P` (`famRestrict`, `inducedFamily`) use `Classical.choose`;
  independence of the choice is a property of families, not proved here.

## Provenance

The objects are Arthur's (source), in a derived Euclidean model: the encoding of parabolic
subgroups by sets of positive roots, the restricted root vectors in place of the coroots
(justified by `thetaOf_smul`), and the Gram-determinant volumes are internal choices. The two
lemmas are proved.
