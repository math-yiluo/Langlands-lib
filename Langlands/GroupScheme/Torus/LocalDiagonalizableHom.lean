import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.Algebra.HopfPointConnected
import Mathlib.CategoryTheory.HomCongr

/-! # Homomorphisms between diagonalizable groups over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CompleteLocalDeformation

open DiagonalizableCharacter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section LocalCoefficients

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type u} [AddCommGroup M]

/-- Over a local ring, a group-like element of a group algebra is a monomial. -/
theorem eq_single_of_isGrouplike {v : AddMonoidAlgebra R M}
    (hv : CharacterAction.IsGrouplike
      (M := M) (B := baseAlg (CommRingCat.of R)) v) :
    ∃ m, v = AddMonoidAlgebra.single m 1 := by
  classical
  have h01 : ∀ p, v.coeff p = 0 ∨ v.coeff p = 1 := fun p =>
    Langlands.Algebra.HopfPointConnected.isIdempotentElem_eq_zero_or_one_of_isLocalRing
      (v.coeff p) (hv.isIdempotentElem_coeff p)
  have hsum : ∑ n ∈ v.coeff.support, v.coeff n = (1 : R) := hv.sum_coeff
  obtain ⟨m, hm⟩ : ∃ m, v.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun n _ => h n)] at hsum
    exact zero_ne_one hsum
  have hm1 : v.coeff m = 1 := (h01 m).resolve_left hm
  refine ⟨m, ?_⟩
  ext n
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact hm1
  · have h0 : v.coeff n * v.coeff m = 0 := hv.coeff_mul_coeff_of_ne h
    rwa [hm1, mul_one] at h0

/-- A natural character of a diagonalizable group over a local ring is evaluation
at a unique character-group element. -/
theorem naturalUnits_existsUnique (c : NaturalUnits (CommRingCat.of R) M) :
    ∃! m : M, ∀ (U : Over (Spec (CommRingCat.of R)))
      (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of R) M).X),
      c.app U x = Diagonalizable.characterPointsEquiv (CommRingCat.of R) M U x (.ofAdd m) := by
  obtain ⟨m, hm⟩ := eq_single_of_isGrouplike c.isGrouplike_value
  refine ⟨m, (c.app_eq_iff m).2 hm, fun m' hm' => ?_⟩
  have h := ((c.app_eq_iff m').1 hm').symm.trans hm
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero (α := R)) h

/-- Additive maps of character groups classify homomorphisms of diagonalizable
groups over every local ring. -/
theorem restrictMap_bijective (M N : Type u) [AddCommGroup M] [AddCommGroup N] :
    Function.Bijective
      (fun g : N →+ M => Diagonalizable.restrictMap (CommRingCat.of R) g) := by
  constructor
  · intro g₁ g₂ h
    change Diagonalizable.restrictMap (CommRingCat.of R) g₁ =
      Diagonalizable.restrictMap (CommRingCat.of R) g₂ at h
    ext n
    have h₁ : ∀ (U : Over (Spec (CommRingCat.of R)))
        (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of R) M).X),
        (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of R) g₁) n).app U x =
          Diagonalizable.characterPointsEquiv (CommRingCat.of R) M U x (.ofAdd (g₁ n)) :=
      fun U x => Diagonalizable.pointsEquiv_restrictMap _ g₁ x n
    have h₂ : ∀ (U : Over (Spec (CommRingCat.of R)))
        (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of R) M).X),
        (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of R) g₁) n).app U x =
          Diagonalizable.characterPointsEquiv (CommRingCat.of R) M U x (.ofAdd (g₂ n)) := by
      rw [h]
      exact fun U x => Diagonalizable.pointsEquiv_restrictMap _ g₂ x n
    exact (naturalUnits_existsUnique
      (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of R) g₁) n)).unique h₁ h₂
  · intro f
    choose g hg using fun n : N => naturalUnits_existsUnique (NaturalUnits.ofHom f n)
    have hadd : ∀ a b : N, g (a + b) = g a + g b := fun a b =>
      ((hg (a + b)).2 (g a + g b) (fun U x => by
        change Diagonalizable.characterPointsEquiv (CommRingCat.of R) N U (x ≫ f.hom.hom)
            (.ofAdd (a + b)) = _
        rw [ofAdd_add, map_mul, ofAdd_add, map_mul]
        exact congrArg₂ (· * ·) ((hg a).1 U x) ((hg b).1 U x))).symm
    refine ⟨AddMonoidHom.mk' g hadd, ?_⟩
    apply hom_ext_points
    intro T x
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of R) N T).injective
    apply MonoidHom.ext
    intro n
    exact (Diagonalizable.pointsEquiv_restrictMap _ (AddMonoidHom.mk' g hadd) x n.toAdd).trans
      ((hg n.toAdd).1 T x).symm

end LocalCoefficients

section BaseChange

variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
  {M N : Type u} [AddCommGroup M] [AddCommGroup N]

/-- Restriction of characters commutes with the canonical base-change comparison. -/
theorem baseChange_restrictMap (g : N →+ M) :
    (GroupScheme.baseChange b).map (Diagonalizable.restrictMap R g) ≫
        (Diagonalizable.baseChangeIso b N).hom =
      (Diagonalizable.baseChangeIso b M).hom ≫ Diagonalizable.restrictMap R' g := by
  apply hom_ext_points
  intro T x
  apply (Diagonalizable.characterPointsEquiv R' N T).injective
  apply MonoidHom.ext
  intro n
  change Diagonalizable.characterPointsEquiv R' N T
      ((x ≫ ((GroupScheme.baseChange b).map
        (Diagonalizable.restrictMap R g)).hom.hom) ≫
          (Diagonalizable.baseChangeIso b N).hom.hom.hom) n =
    Diagonalizable.characterPointsEquiv R' N T
      ((x ≫ (Diagonalizable.baseChangeIso b M).hom.hom.hom) ≫
        (Diagonalizable.restrictMap R' g).hom.hom) n
  rw [Diagonalizable.characterPointsEquiv_baseChangeIso_hom]
  change Diagonalizable.characterPointsEquiv R N ((Over.map b).obj T)
      (baseChangePointsEquiv b (Diagonalizable.groupScheme R N).toGrp T
        (x ≫ ((GroupScheme.baseChange b).map
          (Diagonalizable.restrictMap R g)).hom.hom)) (.ofAdd n.toAdd) = _
  rw [baseChangePointsEquiv_comp]
  exact (Diagonalizable.pointsEquiv_restrictMap R g
    (baseChangePointsEquiv b (Diagonalizable.groupScheme R M).toGrp T x) n.toAdd).trans
    ((congrArg (fun χ => χ (.ofAdd (g n.toAdd)))
        (Diagonalizable.characterPointsEquiv_baseChangeIso_hom b M T x)).symm.trans
      (Diagonalizable.pointsEquiv_restrictMap R' g
        (x ≫ (Diagonalizable.baseChangeIso b M).hom.hom.hom) n.toAdd).symm)

end BaseChange

section Equivalence

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]

/-- The character-group classification of split homomorphisms over a local ring. -/
def characterHomEquiv :
    (N →+ M) ≃
      ((Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶
        (Diagonalizable.groupScheme (CommRingCat.of R) N).toGrp) :=
  Equiv.ofBijective _ (restrictMap_bijective M N)

end Equivalence

section LocalBaseChange

variable {R R' : Type u} [CommRing R] [IsLocalRing R]
  [CommRing R'] [IsLocalRing R']
  (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]

/-- Base change between local rings induces a bijection on homomorphisms
between split diagonalizable groups. -/
theorem baseChange_hom_bijective :
    Function.Bijective
      (fun f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶
          (Diagonalizable.groupScheme (CommRingCat.of R) N).toGrp =>
        (GroupScheme.baseChange b).map f) := by
  let e := Iso.homCongr (Diagonalizable.baseChangeIso b M)
    (Diagonalizable.baseChangeIso b N)
  have hcomp :
      (fun f => e ((GroupScheme.baseChange b).map f)) ∘
        (fun g : N →+ M => Diagonalizable.restrictMap (CommRingCat.of R) g) =
      (fun g : N →+ M => Diagonalizable.restrictMap (CommRingCat.of R') g) := by
    funext g
    change (Diagonalizable.baseChangeIso b M).inv ≫
      (GroupScheme.baseChange b).map (Diagonalizable.restrictMap (CommRingCat.of R) g) ≫
        (Diagonalizable.baseChangeIso b N).hom = _
    rw [baseChange_restrictMap, Iso.inv_hom_id_assoc]
  have heF : Function.Bijective (fun f => e ((GroupScheme.baseChange b).map f)) := by
    apply (Function.Bijective.of_comp_iff _ (restrictMap_bijective (R := R) M N)).mp
    rw [hcomp]
    exact restrictMap_bijective (R := R') M N
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp heF

end LocalBaseChange

end Langlands.GroupScheme.CompleteLocalDeformation
