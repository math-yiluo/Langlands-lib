import Langlands.GroupScheme.Rational.SplitRankReduction
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.LinearAlgebra.RationalFiniteIndex

/-! # Rank comparisons for finite and epimorphic maps of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace splitTorus

variable {k : Type u} [Field k] (I J : Type u) [Finite I] [Finite J]

local notation "S" => Spec (CommRingCat.of k)

/-- A finite map of split tori cannot decrease the number of factors. -/
theorem card_le_card_of_isFinite (f : splitTorus S I ⟶ splitTorus S J)
    [IsFinite f.hom.hom.left] : Nat.card I ≤ Nat.card J := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let c := (characterMap I J f).toAddMonoidHom
  have : Finite ((I → ℤ) ⧸ c.range) := characterMap_finite_cokernel I J f
  have hc := rationalization_surjective_of_finiteIndex c
    (AddSubgroup.finiteIndex_of_finite_quotient (H := c.range))
  let eI := tensorEquivPi (AddEquiv.refl (I → ℤ))
  let eJ := tensorEquivPi (AddEquiv.refl (J → ℤ))
  let cQ : (J → ℚ) →ₗ[ℚ] (I → ℚ) :=
    eI.toLinearMap.comp ((c.toIntLinearMap.baseChange ℚ).comp eJ.symm.toLinearMap)
  have hcQ : Function.Surjective cQ :=
    eI.surjective.comp (hc.comp eJ.symm.surjective)
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    LinearMap.finrank_le_finrank_of_surjective hcQ

/-- An epimorphism of schemes between split tori cannot increase the number of factors. -/
theorem card_le_card_of_epi (f : splitTorus S I ⟶ splitTorus S J)
    [Epi f.hom.hom.left] : Nat.card J ≤ Nat.card I := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    LinearMap.finrank_le_finrank_of_injective (characterMap_injective_of_epi I J f)

end splitTorus

variable {k : Type u} [Field k]
  {T S : GroupScheme (Spec (CommRingCat.of k))}

/-- A finite homomorphism between split tori cannot decrease their split ranks. -/
theorem IsSplitTorus.splitRank_le_of_isFinite
    (hT : IsSplitTorus T) (hS : IsSplitTorus S) (f : T ⟶ S)
    [IsFinite f.hom.hom.left] : splitRank T ≤ splitRank S := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := hS
  let := hI
  let := hJ
  let g := eI.inv ≫ f ≫ eJ.hom
  have : IsIso eI.inv.hom.hom.left := (Over.forget _).map_isIso eI.inv.hom.hom
  have : IsIso eJ.hom.hom.hom.left := (Over.forget _).map_isIso eJ.hom.hom.hom
  have : IsFinite g.hom.hom.left := by
    change IsFinite (eI.inv.hom.hom.left ≫ f.hom.hom.left ≫ eJ.hom.hom.hom.left)
    infer_instance
  rw [splitRank_eq_of_splitIso I eI, splitRank_eq_of_splitIso J eJ]
  exact_mod_cast splitTorus.card_le_card_of_isFinite I J g

/-- An epimorphism of schemes between split tori cannot increase their split ranks. -/
theorem IsSplitTorus.splitRank_le_of_epi
    (hT : IsSplitTorus T) (hS : IsSplitTorus S) (f : T ⟶ S)
    [Epi f.hom.hom.left] : splitRank S ≤ splitRank T := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := hS
  let := hI
  let := hJ
  let g := eI.inv ≫ f ≫ eJ.hom
  have : IsIso eI.inv.hom.hom.left := (Over.forget _).map_isIso eI.inv.hom.hom
  have : IsIso eJ.hom.hom.hom.left := (Over.forget _).map_isIso eJ.hom.hom.hom
  have : Epi g.hom.hom.left := by
    change Epi (eI.inv.hom.hom.left ≫ f.hom.hom.left ≫ eJ.hom.hom.hom.left)
    infer_instance
  rw [splitRank_eq_of_splitIso I eI, splitRank_eq_of_splitIso J eJ]
  exact_mod_cast splitTorus.card_le_card_of_epi I J g

end Langlands.GroupScheme
