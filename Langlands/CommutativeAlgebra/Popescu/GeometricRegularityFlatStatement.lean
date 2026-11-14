import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Flatness from a differential basis of a residue subextension -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

/-- Stacks More on Algebra, Lemma 15.36.2 (07E6), stated at a prime `q` of a geometrically regular
algebra: let `k` be a field of characteristic `p > 0`, `Λ` a Noetherian geometrically regular
`k`-algebra, `q` a prime of `Λ`, `F ⊂ κ(q)` a finitely generated subextension over `k`, and
`φ : k[y_1, …, y_m] → Λ` a `k`-algebra map such that each `y_i` maps to an element of `F` in
`κ(q)` and `dy_1, …, dy_m` map to a basis of `Ω_{F/k}`. Put `𝔭 = φ⁻¹(q)`. Then
`k[y]_𝔭 → Λ_q` is flat and `Λ_q/𝔭Λ_q` is a regular local ring. -/
def GeometricRegularityFlatStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ → ∀ (q : Ideal Λ) [q.IsPrime]
      (F : IntermediateField k q.ResidueField), F.FG →
    ∀ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (hF : ∀ i, algebraMap Λ q.ResidueField (φ (X i)) ∈ F),
      LinearIndependent F (fun i => KaehlerDifferential.D k F ⟨_, hF i⟩) →
      Submodule.span F (Set.range fun i => KaehlerDifferential.D k F ⟨_, hF i⟩) = ⊤ →
    ∀ (𝔭 : Ideal (MvPolynomial (Fin m) k)) [𝔭.IsPrime]
      (h𝔭 : 𝔭 = q.comap (φ : MvPolynomial (Fin m) k →+* Λ)),
      (Localization.localRingHom 𝔭 q φ h𝔭).Flat ∧
      IsRegularLocalRing (Localization.AtPrime q ⧸
        𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ))

end Langlands.CommutativeAlgebra.Popescu
