import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStatement

/-! Renard VI.4.3: the structure of the convolution algebra `A = H(G, ρ)` of the common norm
kernel `⁰G`: the lines `F_x(ρ)` of functions supported on one coset `⁰G x`, the product rule
(VI.4.3.1), the commutation rule (VI.4.3.2), the lattice `⁰G \ N` and the units (VI.4.3.3). -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open GroupScheme

/-- Renard VI.4.3, the structure of `A = H(G, ρ)` (printed pp.154–155), for an irreducible
smooth representation `ρ` of the common norm kernel `H = ⁰G`, with the published space
`rationalNormKernelHecke G ρ` and convolution `rationalNormKernelConvolution G ρ`. Write
`F_x` for the functions of `A` supported in `H x`, and `N` for the set of `x` such that
`ρ^x ≅ ρ`, where `ρ^x(h) = ρ(x⁻¹ h x)`. There is a unit `ε` of `A` supported in `H` with
`ε(1) = 1`, and:
1. `φ ↦ φ(x)` is injective on `F_x`, with image `Hom_H(ρ^x, ρ)`;
2. `F_x` has dimension at most one, and is nonzero exactly when `x ∈ N`;
3. every element of `A` is supported in `N` (`A = H(N, ρ)`);
4. (VI.4.3.1) for `φ ∈ F_x` and `ψ ∈ F_y`, `φ * ψ ∈ F_{xy}` and `(φ * ψ)(xy) = φ(x) ψ(y)`;
5. a nonzero `φ ∈ F_x` is invertible, with inverse in `F_{x⁻¹}`;
6. (VI.4.3.2) for nonzero `φ ∈ F_x`, `ψ ∈ F_y`, `φ * ψ = c ψ * φ` with `c ∈ ℂˣ`;
7. `N` is a subgroup containing `H`, and `H \ N` and `Λ(G) = H \ G` are free abelian of the
   same finite rank;
8. `A` is spanned by the `F_x`, and (VI.4.3.3) the units of `A` are exactly its nonzero
   elements lying in some `F_x`. -/
def RationalNormKernelHeckeStructureStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
      ρ.IsIrreducible →
      let H := rationalCommonNormKernel G
      let A := rationalNormKernelHecke G ρ
      let conv := rationalNormKernelConvolution G ρ
      let InF : rationalPoints G → (rationalPoints G → Module.End ℂ ρ) → Prop := fun x φ =>
        φ ∈ A ∧ ∀ g, φ g ≠ 0 → g * x⁻¹ ∈ H
      let IsTwistHom : rationalPoints G → Module.End ℂ ρ → Prop := fun x T =>
        ∀ h h' : H, (h' : rationalPoints G) = x⁻¹ * h * x →
          T * ρ.representation h' = ρ.representation h * T
      let InN : rationalPoints G → Prop := fun x =>
        ∃ T : Module.End ℂ ρ, IsTwistHom x T ∧ Function.Bijective T
      let IsLatticeBasis : (n : ℕ) → (Fin n → rationalPoints G) → Set (rationalPoints G) →
          Prop := fun n b S =>
        ∀ g ∈ S, ∃! e : Fin n → ℤ, g * ((List.ofFn fun i => b i ^ e i).prod)⁻¹ ∈ H
      ∃ ε : rationalPoints G → Module.End ℂ ρ,
        InF 1 ε ∧ ε 1 = 1 ∧ (∀ φ ∈ A, conv ε φ = φ ∧ conv φ ε = φ) ∧
        (∀ x : rationalPoints G,
          (∀ φ, InF x φ → φ x = 0 → φ = 0) ∧
          ∀ T : Module.End ℂ ρ, IsTwistHom x T ↔ ∃ φ, InF x φ ∧ φ x = T) ∧
        (∀ x : rationalPoints G,
          (∀ φ ψ, InF x φ → InF x ψ → φ ≠ 0 → ∃ c : ℂ, ψ = c • φ) ∧
          ((∃ φ, InF x φ ∧ φ ≠ 0) ↔ InN x)) ∧
        (∀ φ ∈ A, ∀ g, φ g ≠ 0 → InN g) ∧
        (∀ x y φ ψ, InF x φ → InF y ψ →
          InF (x * y) (conv φ ψ) ∧ conv φ ψ (x * y) = φ x * ψ y) ∧
        (∀ x φ, InF x φ → φ ≠ 0 → ∃ ψ, InF x⁻¹ ψ ∧ conv φ ψ = ε ∧ conv ψ φ = ε) ∧
        (∀ x y φ ψ, InF x φ → InF y ψ → φ ≠ 0 → ψ ≠ 0 →
          ∃ c : ℂ, c ≠ 0 ∧ conv φ ψ = c • conv ψ φ) ∧
        (∃ N : Subgroup (rationalPoints G), (∀ g, g ∈ N ↔ InN g) ∧ H ≤ N ∧
          ∃ n : ℕ,
            (∃ y : Fin n → rationalPoints G, IsLatticeBasis n y Set.univ) ∧
            (∃ x : Fin n → rationalPoints G, (∀ i, x i ∈ N) ∧ IsLatticeBasis n x N)) ∧
        A = Submodule.span ℂ {φ | ∃ x, InF x φ} ∧
        ∀ φ ∈ A, (∃ ψ ∈ A, conv φ ψ = ε ∧ conv ψ φ = ε) ↔ (φ ≠ 0 ∧ ∃ x, InF x φ)

end Langlands.CuspidalSupport
