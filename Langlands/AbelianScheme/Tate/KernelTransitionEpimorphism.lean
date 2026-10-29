import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.MultiplicationIsogenyStatement
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Epimorphisms between actual multiplication kernels -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- The actual divisibility transition is a pullback of multiplication by `m / n`. -/
lemma kernelTransition_isPullback {n m : ℕ} (h : n ∣ m) :
    IsPullback (kernelι (multiplication G m)).hom.hom
      (kernelTransition G h) (multiplication G (m / n : ℕ)).hom.hom
      (kernelι (multiplication G n)).hom.hom := by
  have hmul :
      (multiplication G (m / n : ℕ)).hom.hom ≫ (multiplication G n).hom.hom =
        (multiplication G m).hom.hom := by
    change (multiplication G (m / n : ℕ) ≫ multiplication G n).hom.hom = _
    have hm : ((m / n : ℕ) : ℤ) * (n : ℤ) = (m : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel h
    rw [← multiplication_mul, hm]
  have houter :
      IsPullback (kernelι (multiplication G m)).hom.hom
        (kernelTransition G h ≫ toUnit (kernel (multiplication G n)).X)
        ((multiplication G (m / n : ℕ)).hom.hom ≫ (multiplication G n).hom.hom)
        η[G.X] := by
    rw [comp_toUnit, hmul]
    exact kernel_isPullback (multiplication G m)
  exact houter.of_bot (kernelTransition_ι G h).symm
    (kernel_isPullback (multiplication G n))

/-- The actual multiplication kernel, identified with the base change of `[m / n]`. -/
def kernelTransitionPullbackIso {n m : ℕ} (h : n ∣ m) :
    (kernel (multiplication G m)).X ≅
      pullback (multiplication G (m / n : ℕ)).hom.hom
        (kernelι (multiplication G n)).hom.hom :=
  (kernelTransition_isPullback G h).isoPullback

/-- The first projection of the comparison is the actual kernel inclusion. -/
@[reassoc (attr := simp)]
lemma kernelTransitionPullbackIso_hom_fst {n m : ℕ} (h : n ∣ m) :
    (kernelTransitionPullbackIso G h).hom ≫ pullback.fst _ _ =
      (kernelι (multiplication G m)).hom.hom :=
  (kernelTransition_isPullback G h).isoPullback_hom_fst

/-- The second projection of the comparison is the actual torsion transition. -/
@[reassoc (attr := simp)]
lemma kernelTransitionPullbackIso_hom_snd {n m : ℕ} (h : n ∣ m) :
    (kernelTransitionPullbackIso G h).hom ≫ pullback.snd _ _ =
      kernelTransition G h :=
  (kernelTransition_isPullback G h).isoPullback_hom_snd

/-- The same square is a pullback of actual schemes. -/
lemma kernelTransition_isPullback_scheme {n m : ℕ} (h : n ∣ m) :
    IsPullback (kernelι (multiplication G m)).hom.hom.left
      (kernelTransition G h).left (multiplication G (m / n : ℕ)).hom.hom.left
      (kernelι (multiplication G n)).hom.hom.left :=
  (kernelTransition_isPullback G h).map (Over.forget S)

/-- Flatness of integer multiplication passes to the actual transition. -/
lemma kernelTransition_flat {n m : ℕ} (h : n ∣ m)
    [Flat (multiplication G (m / n : ℕ)).hom.hom.left] :
    Flat (kernelTransition G h).left :=
  MorphismProperty.of_isPullback (P := @Flat)
    (kernelTransition_isPullback_scheme G h) inferInstance

/-- Surjectivity of integer multiplication passes to the actual transition. -/
lemma kernelTransition_surjective {n m : ℕ} (h : n ∣ m)
    [Surjective (multiplication G (m / n : ℕ)).hom.hom.left] :
    Surjective (kernelTransition G h).left :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (kernelTransition_isPullback_scheme G h) inferInstance

/-- A flat surjective multiplication map gives an epimorphism of actual schemes. -/
lemma kernelTransition_epi_left {n m : ℕ} (h : n ∣ m)
    [Flat (multiplication G (m / n : ℕ)).hom.hom.left]
    [Surjective (multiplication G (m / n : ℕ)).hom.hom.left] :
    Epi (kernelTransition G h).left := by
  have := kernelTransition_flat G h
  have := kernelTransition_surjective G h
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

/-- The corresponding epimorphism in the slice category. -/
lemma kernelTransition_epi {n m : ℕ} (h : n ∣ m)
    [Flat (multiplication G (m / n : ℕ)).hom.hom.left]
    [Surjective (multiplication G (m / n : ℕ)).hom.hom.left] :
    Epi (kernelTransition G h) := by
  have := kernelTransition_epi_left G h
  exact Over.epi_of_epi_left _

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme

open Langlands.GroupScheme

/-- The actual doubling transition is an epimorphism of schemes, conditional
only on the published multiplication-isogeny statement. -/
lemma kernelDoubling_epi_left_of_multiplicationIsogeny
    (hIsogeny : MultiplicationIsogenyStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ) (hn : 0 < n) :
    Epi (Tate.kernelTransition A.toGrp (dvd_mul_left n 2)).left := by
  have hi := hIsogeny S A.toGrp A.smooth A.proper A.geometricallyConnected 2 (by norm_num)
  have hratio : 2 * n / n = 2 := by
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left 2 hn
  have hflat : Flat (multiplication A.toGrp (2 * n / n : ℕ)).hom.hom.left := by
    rw [hratio]
    exact hi.2.1
  have hsurj : Surjective (multiplication A.toGrp (2 * n / n : ℕ)).hom.hom.left := by
    rw [hratio]
    exact hi.2.2
  have := hflat
  have := hsurj
  exact Tate.kernelTransition_epi_left A.toGrp (dvd_mul_left n 2)

/-- The exact slice-category epimorphism consumed by the alternation assembly. -/
lemma kernelDoubling_epi_of_multiplicationIsogeny
    (hIsogeny : MultiplicationIsogenyStatement.{u})
    (S : Scheme.{u}) (A : AbelianScheme S) (n : ℕ) (hn : 0 < n) :
    Epi (Tate.kernelTransition A.toGrp (dvd_mul_left n 2)) := by
  have := kernelDoubling_epi_left_of_multiplicationIsogeny hIsogeny A n hn
  exact Over.epi_of_epi_left _

end Langlands.AbelianScheme
