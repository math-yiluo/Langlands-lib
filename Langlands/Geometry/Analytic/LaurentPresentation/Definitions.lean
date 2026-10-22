import Langlands.Geometry.Analytic.RationalPresentation.Definitions

/-! # Actual unit-radius Laurent quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.LaurentPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (n m l : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (f : Fin m → StrictTateAlgebra (Fin n) K)
  (g : Fin l → StrictTateAlgebra (Fin n) K)

/-- A common denominator for all the lower-bound functions. -/
def denominator : StrictTateAlgebra (Fin n) K := ∏ j, g j

/-- The product of all lower-bound functions other than the indicated one. -/
def complementaryProduct (j : Fin l) : StrictTateAlgebra (Fin n) K :=
  ∏ k ∈ Finset.univ.erase j, g k

theorem mul_complementaryProduct (j : Fin l) :
    g j * complementaryProduct K n l g j = denominator K n l g :=
  Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)

/-- Fractions `f_i`, `1/g_j` and `1/(prod g_j)`, expressed using a common
denominator. The numerator one makes the unit-ideal condition automatic. -/
def numerators : Fin (m + l + 1) → StrictTateAlgebra (Fin n) K :=
  Fin.append
    (Fin.append (fun i => f i * denominator K n l g)
      (complementaryProduct K n l g)) (fun _ : Fin 1 => 1)

theorem numerators_upper (i : Fin m) :
    numerators K n m l f g (Fin.castAdd 1 (Fin.castAdd l i)) =
      f i * denominator K n l g := by
  simp only [numerators, Fin.append_left]

theorem numerators_lower (j : Fin l) :
    numerators K n m l f g (Fin.castAdd 1 (Fin.natAdd m j)) =
      complementaryProduct K n l g j := by
  simp only [numerators, Fin.append_left, Fin.append_right]

theorem numerators_one :
    numerators K n m l f g (Fin.natAdd (m + l) (0 : Fin 1)) = 1 := by
  simp only [numerators, Fin.append_right]

variable [CompleteSpace K]

/-- A genuine strict affinoid quotient presenting the unit-radius Laurent locus. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  RationalPresentation.algebra K n (m + l + 1) S
    (denominator K n l g) (numerators K n m l f g)

/-- The constructed bounded map from the base algebra. -/
def baseMap : BoundedAlgHom K (ofRelations K n S) (algebra K n m l S f g) :=
  RationalPresentation.baseMap K n (m + l + 1) S
    (denominator K n l g) (numerators K n m l f g)

/-- The actual finite Laurent inequality locus with all radii equal to one. -/
def locus : Set (BanachSpectrum (ofRelations K n S)) :=
  laurentLocus (fun i => presentationMap K (ofRelations K n S) (f i)) (fun _ => 1)
    (fun j => presentationMap K (ofRelations K n S) (g j)) (fun _ => 1)

end Langlands.Analytic.LaurentPresentation
