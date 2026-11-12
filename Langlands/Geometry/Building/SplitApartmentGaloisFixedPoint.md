# Uniqueness and Galois-fixed points of split apartment classes

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint`.

This internal unit proves three facts used to descend a split apartment class from a
finite Galois extension (task 8ffe0456): a split apartment class is unique, it is
therefore stable under coefficient automorphisms, and over a finite extension it has
a point fixed by all of them.

## Fixed points of finite affine actions

`exists_fixed_of_finite_affineAction`: if a finite group `M` acts by affine
equivalences `ρ : M →* (P ≃ᵃ[ℝ] P)` on a nonempty real affine space `P`, some point
is fixed by every element. For a point `p`, the fixed point is
`c +ᵥ p` with `c = |M|⁻¹ • Σ_n (ρ n p -ᵥ p)`, the barycenter of the orbit of `p`.
The proof applies the linear part of `ρ m` to `c` and reindexes the sum by
`n ↦ m n`.

## Translation by rational torus points

Let `i : T.toGrp ⟶ G` be a monomorphism into an affine group.

- `exists_eval_eq_neg_order`: if `T` is split and `ω : kˣ → ℝ` is additive, then for
  every rational point `τ` of `T` there is `w : V(T)` with
  `a(w) = -ω(a(τ))` for every character `a`. It applies
  the published `Langlands.BruhatTits.Cartan.exists_eval_eq`.
- `IsSplitTorusCompatible.centralizer_smul_eq_vadd`: if `φ` is a valuation of the root
  datum, compatible with `ω` on `T`, and the centralizer point `z` is the image of
  `τ`, then `z • φ = w +ᵥ φ` for every such `w`. The vector does not depend on `φ`.
  The proof applies the published `RootFunctionFamily.centralizer_smul_eq_vadd`
  with the covariance given by split-torus compatibility.

## Uniqueness

`KPApartmentData.eq_of_isMaximalTorus_of_isSplitTorus`: let `G` be connected
reductive, `i` a split maximal torus, and `ω` additive. Any two
`KPApartmentData i ω` are equal.

The centralizer of a maximal torus is the torus (published
`maximalTorusCentralizer`), so every centralizer point is the image of a rational
torus point `τ`. By the previous lemma it moves points of both classes by the same
vector `w`. This is the published hypothesis `HasCommonCentralizerDisplacements`.
The published rigidity theorem
`eq_of_hasCommonCentralizerDisplacements_of_hasOppositeFactorPairs` then gives
equality. Its premises are supplied as follows: a split maximal torus is maximal
split (`IsMaximalTorus.isMaximalSplitTorus`), and opposite factor pairs come from the
published `rootRankOneFactorization` through
`hasRankOneFactorization_iff_hasOppositeFactorPairs`.

## Galois stability and fixed points

Let `K/k` be a field extension, `T` and `G` defined over `k`, and `i : T.toGrp ⟶ G`.
Write `T_K`, `G_K` and `i_K` for the base changes.

- `KPApartmentData.galoisStable_of_isSplitTorus`: if `G_K` is connected reductive,
  `i_K` is a split maximal torus, and `ω : Kˣ → ℝ` is additive and invariant under
  every `σ : K ≃ₐ[k] K`, then every `KPApartmentData i_K ω` is `GaloisStable`.
  The published coefficient image `galoisImage` is another class for the same torus
  and `ω`, so uniqueness identifies it with the original class.
- `KPApartmentData.exists_galoisFixed`: if moreover `K/k` is finite, a `GaloisStable`
  class has an apartment point whose family is fixed by the coefficient action of
  every `σ`. It applies the fixed-point lemma to the published affine action
  `galoisAffineAction` and uses `mem_galoisFixedApartment_iff`.
- `KPApartmentData.galoisFixedPoint` (definition): a chosen such point, obtained by
  `Classical.choose` from `exists_galoisFixed`. Its property is
  `KPApartmentData.galoisAction_galoisFixedPoint`.

## Provenance

The uniqueness statement is the split case of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Proposition 6.2.6, printed p. 216 (PDF p. 247), here derived
from the published rigidity step of that proposition. Galois stability of the
apartment of the split group is stated in the same source, Construction 6.1.21,
printed pp. 207–208 (PDF pp. 238–239): "The action of `Θ` on the set of valuations of the
root datum preserves `A(T)`". The barycenter argument for fixed points is standard.
All proofs here are internal compositions of published Library results.

## Scope

Nothing here constructs the apartment over the original field. In particular, the
fixed point is not yet descended, and no relative valuation axioms are proved.
