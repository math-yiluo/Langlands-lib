import Langlands.GroupScheme.Rational.GeneralLinearCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # The lattice step in the diagonal-torus centralizer calculation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable (k : Type u) [CommRing k] [IsDomain k] (I : Type u) [Finite I]

/-- The difference of coordinate characters pairs with the difference of weights. -/
theorem latticePairing_proj_sub
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (i j : I) :
    latticePairing (commGroupScheme (Spec (CommRingCat.of k)) I)
        (proj _ I i - proj _ I j) ν =
      cocharacterLatticeEquiv k I ν i - cocharacterLatticeEquiv k I ν j := by
  rw [map_sub, LinearMap.sub_apply]
  rfl

/-- Avoiding the coordinate-root hyperplanes is equivalent to distinct weights. -/
theorem coordinatePairings_ne_zero_iff_injective
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    (∀ i j : I, i ≠ j →
      latticePairing (commGroupScheme (Spec (CommRingCat.of k)) I)
        (proj _ I i - proj _ I j) ν ≠ 0) ↔
      Function.Injective (cocharacterLatticeEquiv k I ν) := by
  simp_rw [latticePairing_proj_sub, sub_ne_zero]
  exact ⟨fun h i j hij => by
    by_contra hne
    exact h i j hne hij,
    fun h i j hij heq => hij (h heq)⟩

end splitTorus

namespace GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]
variable (k : Type u) [CommRing k] [IsDomain k]

/-- A homomorphism with the diagonal-torus point formula carries every cocharacter
to the published diagonal cocharacter with its lattice weights. -/
theorem cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points
    (i : splitTorus (Spec (CommRingCat.of k)) (ULift.{u} n) ⟶
      groupScheme n (CommRingCat.of k))
    (hi : ∀ (U : Over (Spec (CommRingCat.of k)))
      (t : U ⟶ (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} n)).X),
      (pointsEquiv n (CommRingCat.of k) U (t ≫ i.hom.hom) :
        Matrix n n Γ(U.left, ⊤)) =
      Matrix.diagonal fun j =>
        ((splitTorus.pointsEquiv (ULift.{u} n) U t (ULift.up j) : (Γ(U.left, ⊤))ˣ) : Γ(U.left, ⊤)))
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n))) :
    CommGroupScheme.groupHom ν ≫ i =
      diagonalCocharacter n (CommRingCat.of k)
        (fun j : n => splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ν (ULift.up j)) := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv n (CommRingCat.of k) U).injective
  apply Units.ext
  change
    (pointsEquiv n (CommRingCat.of k) U
      (x ≫ (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom) :
      Matrix n n Γ(U.left, ⊤)) = _
  rw [← Category.assoc, hi, pointsEquiv_diagonalCocharacter, coe_diagonalUnits]
  have hν := splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm k (ULift.{u} n)
    (splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ν) x
  rw [AddEquiv.symm_apply_apply] at hν
  rw [hν]

/-- The diagonal point formula and nonzero coordinate-root pairings reduce the
generic centralizer equality to the published dynamic block-Levi computation. -/
theorem dynamicCentralizer_eq_torusCentralizer_of_coordinate_pairings
    (i : splitTorus (Spec (CommRingCat.of k)) (ULift.{u} n) ⟶
      groupScheme n (CommRingCat.of k))
    (hi : ∀ (U : Over (Spec (CommRingCat.of k)))
      (t : U ⟶ (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} n)).X),
      (pointsEquiv n (CommRingCat.of k) U (t ≫ i.hom.hom) :
        Matrix n n Γ(U.left, ⊤)) =
      Matrix.diagonal fun j =>
        ((splitTorus.pointsEquiv (ULift.{u} n) U t (ULift.up j) : (Γ(U.left, ⊤))ˣ) : Γ(U.left, ⊤)))
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)))
    (hν : ∀ a b : ULift.{u} n, a ≠ b →
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n))
        (splitTorus.proj _ (ULift.{u} n) a - splitTorus.proj _ (ULift.{u} n) b) ν ≠ 0)
    (hcentralizer : ∀ e : n → ℤ,
      Dynamic.centralizer (diagonalCocharacter n (CommRingCat.of k) e) =
        blockLevi n (CommRingCat.of k) e) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) =
      torusCentralizer
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)) i := by
  apply dynamicCentralizer_eq_torusCentralizer_of_injective_weights i
    (CommGroupScheme.groupHom ν)
    (((splitTorus.coordinatePairings_ne_zero_iff_injective k (ULift.{u} n) ν).1 hν).comp
      (fun a b h => congrArg ULift.down h))
  · intro U t
    rw [hi]
    exact Matrix.isDiag_diagonal _
  · exact cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points k i hi ν
  · exact hcentralizer _

end GeneralLinear

end Langlands.GroupScheme
