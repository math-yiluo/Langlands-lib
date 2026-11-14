import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RingHom.Flat

/-! # Enlarging a flat Artinian approximation so that it contains a power of a unit -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open IsLocalRing

/-- A refinement of the proof of Stacks Smoothing Ring Maps, Lemma 16.11.3 (07FI), for units, with
control of the residue field. Let `k` be a field of characteristic `p > 0` and let
`ψ : D → L` be a flat local homomorphism of Artinian local `k`-algebras, with `D` essentially of
finite type over `k`. Let `ℓ ∈ L` be a unit, and let `b₁, …, b_t ∈ D` be elements whose residue
classes have differentials forming a basis of `Ω_{κ_D/k}`. Then there are an Artinian local
`k`-algebra `D'`, essentially of finite type over `k`, a `k`-algebra map `ι : D → D'` and a flat
local `k`-algebra map `ψ' : D' → L` with `ψ' ∘ ι = ψ`, such that
(1) some power `ℓ^Q` (`Q > 0`) is `ψ'(u)` for an element `u ∈ D'` with `d(ū) = 0` in
`Ω_{κ_{D'}/k}`;
(2) there are elements `v₁, …, v_r ∈ D'` with `ψ'(v_j) = ℓ` such that the differentials of the
residue classes of `ι(b₁), …, ι(b_t), v₁, …, v_r` form a basis of `Ω_{κ_{D'}/k}`. -/
def ArtinianUnitEnlargementStatement : Prop :=
  ∀ (k D L : Type u) [Field k] [CommRing D] [CommRing L] [Algebra k D] [Algebra k L]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing L] [IsArtinianRing L]
    [Algebra.EssFiniteType k D] (ψ : D →ₐ[k] L), IsLocalHom ψ → (ψ : D →+* L).Flat →
    ∀ (ℓ : L), IsUnit ℓ → ∀ (t : ℕ) (b : Fin t → D),
      LinearIndependent (ResidueField D)
        (fun i => KaehlerDifferential.D k (ResidueField D) (residue D (b i))) →
      Submodule.span (ResidueField D)
        (Set.range fun i => KaehlerDifferential.D k (ResidueField D) (residue D (b i))) = ⊤ →
    ∃ (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (_ : Algebra k D') (_ : Algebra.EssFiniteType k D') (ι : D →ₐ[k] D') (ψ' : D' →ₐ[k] L),
      IsLocalHom ψ' ∧ (ψ' : D' →+* L).Flat ∧ ψ'.comp ι = ψ ∧
      (∃ (Q : ℕ) (u : D'), 0 < Q ∧ ψ' u = ℓ ^ Q ∧
        KaehlerDifferential.D k (ResidueField D') (residue D' u) = 0) ∧
      ∃ (r : ℕ) (v : Fin r → D'), (∀ j, ψ' (v j) = ℓ) ∧
        LinearIndependent (ResidueField D')
          (Sum.elim (fun i => KaehlerDifferential.D k (ResidueField D') (residue D' (ι (b i))))
            (fun j => KaehlerDifferential.D k (ResidueField D') (residue D' (v j)))) ∧
        Submodule.span (ResidueField D') (Set.range
          (Sum.elim (fun i => KaehlerDifferential.D k (ResidueField D') (residue D' (ι (b i))))
            (fun j => KaehlerDifferential.D k (ResidueField D') (residue D' (v j))))) = ⊤

end Langlands.CommutativeAlgebra.Popescu
