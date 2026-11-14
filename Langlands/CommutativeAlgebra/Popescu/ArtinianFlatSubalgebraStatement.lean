import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic

/-! # Artinian local algebras as unions of flat essentially finite type subalgebras -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open IsLocalRing

/-- Stacks Smoothing Ring Maps, Lemma 16.11.1 (07FG), in the form used in Lemma 16.11.2: let `k` be a
field of characteristic `p > 0` and `(L, 𝔪, K)` an Artinian local `k`-algebra with
`dim_K H₁(L_{K/k}) < ∞`. Then every finite subset `E ⊂ L` lies in a `k`-subalgebra `A ⊂ L` which
is an Artinian local ring essentially of finite type over `k`, with `A → L` flat and `𝔪_A L = 𝔪`. -/
def ArtinianFlatSubalgebraStatement : Prop :=
  ∀ (k L : Type u) [Field k] [CommRing L] [Algebra k L] (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsLocalRing L] [IsArtinianRing L],
    Module.Finite (ResidueField L) (Algebra.H1Cotangent k (ResidueField L)) →
    ∀ E : Finset L, ∃ (A : Subalgebra k L) (_ : IsLocalRing A), (E : Set L) ⊆ A ∧
      IsArtinianRing A ∧ Algebra.EssFiniteType k A ∧ Module.Flat A L ∧
      (maximalIdeal A).map (algebraMap A L) = maximalIdeal L

end Langlands.CommutativeAlgebra.Popescu
