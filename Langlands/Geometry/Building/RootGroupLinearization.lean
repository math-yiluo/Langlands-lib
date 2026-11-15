import Langlands.Geometry.Building.KPApartment
import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Semilinear coordinates on rational root-group points

For a field extension `K/k`, a `k`-group `G` with a `k`-torus `S`, and a character `α` of `S`,
this module defines the proposition `RootGroupLinearization iS α v`. It asserts that the group
`U = U_{α_K}(K)` of rational points of the root group of `α_K` carries two coordinate maps

* `q : U → K^n`, a homomorphism to the additive group whose kernel is
  `U₂ = U_{2α_K}(K)` (or `{1}` when `2α_K` is not a root), and
* `e : U₂ → K^m`, an injective homomorphism to the additive group,

that are equivariant for the coefficient action of `Aut(K/k)`, and that for every `c ∈ K^×` with
`v(c) = 1` some point `t` of `S_K` with `v(χ(t)) = 1` for every rational character `χ` scales
`q` by `c^d` and `e` by `c^2` under conjugation, for a fixed `d ∈ {1, 2}`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The base change of an affine group scheme along `Spec K ⟶ Spec k` is affine. -/
local instance rootGroupLinearization_isAffineHom_baseChange :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The same instance for the form `baseChanged k K G` used by `rationalConjugate`. -/
local instance rootGroupLinearization_isAffineHom_baseChanged :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap k K))
  infer_instance

/-- **Semilinear coordinates on `U_{α_K}(K)`.** Write `b = algebraBaseMap k K`,
`U = U_{α_K}(K)` for the rational points of the root group of `α_K` for `(G_K, S_K)` and
`U₂ = doubleRootGroupPoints` of `α_K` (that is `U_{2α_K}(K)`, or `{1}` if `2α_K` is not a
root). The proposition asserts that there are `n m d : ℕ` and maps `q : G_K(K) → K^n`,
`e : G_K(K) → K^m` such that:

1. `d = 1` or `d = 2`;
2. `q` is additive on `U` and, for `x ∈ U`, `q x = 0` if and only if `x ∈ U₂`;
3. `e` is additive and injective on `U₂`;
4. `U` is stable under the coefficient action `rationalConjugate` of every `σ ∈ Aut(K/k)`,
   and `q`, `e` are equivariant on `U`, resp. `U₂`: `q(σ x) = σ(q x)` coordinatewise;
5. for every unit `c` of `K` with `v(c) = 1` there is a point `t` of `S_K` in
   `characterValuationKernel v` whose image `T` in `G_K(K)` is fixed by every `σ` that fixes
   `c`, normalizes `U`, and satisfies `q(T x T⁻¹) = c^d q x` on `U` and
   `e(T x T⁻¹) = c^2 e x` on `U₂`. -/
def RootGroupLinearization (iS : S.toGrp ⟶ G) (α : characterLattice S)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) : Prop :=
  ∃ (n m d : ℕ)
    (q : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) → Fin n → K)
    (e : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) → Fin m → K),
    (d = 1 ∨ d = 2) ∧
    (∀ x ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      ∀ y ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      q (x * y) = q x + q y) ∧
    (∀ x ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      q x = 0 ↔ x ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α)) ∧
    (∀ x ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      ∀ y ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      e (x * y) = e x + e y) ∧
    (∀ x ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      e x = 0 → x = 1) ∧
    (∀ σ : K ≃ₐ[k] K, ∀ x ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      rationalConjugate k K G σ x ∈
        rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
          (characterLattice.baseChange (algebraBaseMap k K) S α)) ∧
    (∀ σ : K ≃ₐ[k] K, ∀ x ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      q (rationalConjugate k K G σ x) = fun i => σ (q x i)) ∧
    (∀ σ : K ≃ₐ[k] K,
      ∀ x ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
        (characterLattice.baseChange (algebraBaseMap k K) S α),
      e (rationalConjugate k K G σ x) = fun i => σ (e x i)) ∧
    ∀ c : Kˣ, v (c : K) = 1 →
      ∃ t ∈ characterValuationKernel v
          ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S).toGrp,
        (∀ σ : K ≃ₐ[k] K, σ (c : K) = c →
          rationalConjugate k K G σ
              (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t) =
            rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t) ∧
        (∀ x ∈ rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
            (characterLattice.baseChange (algebraBaseMap k K) S α),
          rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t * x *
              (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t)⁻¹ ∈
            rootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
              (characterLattice.baseChange (algebraBaseMap k K) S α) ∧
          q (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t * x *
              (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t)⁻¹) =
            (c : K) ^ d • q x) ∧
        (∀ x ∈ doubleRootGroupPoints ((GroupScheme.baseChange (algebraBaseMap k K)).map iS)
            (characterLattice.baseChange (algebraBaseMap k K) S α),
          e (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t * x *
              (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map iS) t)⁻¹) =
            (c : K) ^ 2 • e x)

end Langlands.Geometry.Building
