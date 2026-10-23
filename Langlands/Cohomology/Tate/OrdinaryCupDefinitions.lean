import Langlands.Cohomology.Tate.OrdinaryCochainCup

noncomputable section

universe u

open CategoryTheory groupCohomology

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G] {A B C : Rep R G}

/-- The explicit ordinary cochain cup restricted to actual cocycles. -/
def ordinaryCupCocycles (φ : Pairing A B C) (p q : ℕ) :
    cocycles A p →ₗ[R] cocycles B q →ₗ[R] cocycles C (p + q) :=
  OrdinaryCup.onCocycles A B C p q (ordinaryCochainCup φ p q)
    (OrdinaryCup.cycles_of_leibniz A B C (ordinaryCochainCup φ)
      (ordinaryCochainCup_d φ) p q)

/-- Inclusion of the cocycle cup is the explicit cochain cup. -/
@[simp]
lemma i_ordinaryCupCocycles (φ : Pairing A B C) (p q : ℕ)
    (a : cocycles A p) (b : cocycles B q) :
    iCocycles C (p + q) (ordinaryCupCocycles φ p q a b) =
      ordinaryCochainCup φ p q (iCocycles A p a) (iCocycles B q b) :=
  OrdinaryCup.i_onCocycles _ _ _ _ _ _ _ _ _

/-- The tuple formula for the cocycle representing the ordinary cup. -/
lemma ordinaryCupCocycles_apply (φ : Pairing A B C) (p q : ℕ)
    (a : cocycles A p) (b : cocycles B q) (x : Fin (p + q) → G) :
    iCocycles C (p + q) (ordinaryCupCocycles φ p q a b) x =
      φ.bilinear (iCocycles A p a (fun i => x (Fin.castAdd q i)))
        (B.ρ (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod
          (iCocycles B q b (fun j => x (Fin.natAdd p j)))) := by
  rw [i_ordinaryCupCocycles, ordinaryCochainCup_apply]

/-- The ordinary cup product on actual Mathlib group cohomology, obtained by
descending the explicit cochain cup using its proved Leibniz identity. -/
def ordinaryCup (φ : Pairing A B C) (p q : ℕ) :
    groupCohomology A p →ₗ[R] groupCohomology B q →ₗ[R]
      groupCohomology C (p + q) :=
  OrdinaryCup.fromLeibniz A B C (ordinaryCochainCup φ) (ordinaryCochainCup_d φ) p q

/-- The ordinary cup is represented by the explicit cup of cocycle representatives. -/
@[simp]
lemma ordinaryCup_π_π (φ : Pairing A B C) (p q : ℕ)
    (a : cocycles A p) (b : cocycles B q) :
    ordinaryCup φ p q (π A p a) (π B q b) =
      π C (p + q) (ordinaryCupCocycles φ p q a b) :=
  OrdinaryCup.fromLeibniz_π_π A B C (ordinaryCochainCup φ) (ordinaryCochainCup_d φ)
    p q a b

end Langlands.Tate
