import Langlands.GroupScheme.Torus.GeometricRootProfiles

/-! # Comparison of actual root supports over a local base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.splitTorus

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- The complete adjoint weight-rank profile is constant over a local base. -/
theorem exponentWeightRankProfile_eq_of_isLocalRing
    (s t : Spec (CommRingCat.of R)) :
    exponentWeightRankProfile I G i s = exponentWeightRankProfile I G i t := by
  have h (x : Spec (CommRingCat.of R)) :
      exponentWeightRankProfile I G i x =
        exponentWeightRankProfile I G i (IsLocalRing.closedPoint R) :=
    (IsLocalRing.specializes_closedPoint x).mem_open
      ((isLocallyConstant_exponentWeightRankProfile I G i).isOpen_fiber _) rfl
  exact (h s).trans (h t).symm

/-- All chosen geometric identity-component fibres have the same actual root support. -/
theorem geometricExponentRoots_eq_of_isLocalRing
    (s t : Spec (CommRingCat.of R)) :
    geometricExponentRoots I G i s = geometricExponentRoots I G i t := by
  ext m
  rw [mem_geometricExponentRoots_iff, mem_geometricExponentRoots_iff]
  have he := congrArg (fun p => p m)
    (exponentWeightRankProfile_eq_of_isLocalRing I G i s t)
  change exponentWeightRank I G i m s = exponentWeightRank I G i m t at he
  rw [he]

variable {k l : Type u} [Field k] [Field l] [Algebra R k] [Algebra R l]

local instance localRootSupportAffine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

local instance localRootSupportSmooth {A : Type u} [CommRing A] [Algebra R A] :
    Smooth ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom (algebraBaseMap R A)))

/-- Every fixed-exponent actual character has the same weight dimension on any
 two field-valued fibres of a smooth affine group over a local ring. -/
theorem finrank_weightSpace_eq_of_isLocalRing (m : I → ℤ) :
    Module.finrank k
        (weightSpace (baseChangeHom (K := k) G I i)
          (exponentCharacter (Spec (CommRingCat.of k)) I m)) =
      Module.finrank l
        (weightSpace (baseChangeHom (K := l) G I i)
          (exponentCharacter (Spec (CommRingCat.of l)) I m)) := by
  rw [← exponentWeightSpace_eq_weightSpace_exponentCharacter,
    ← exponentWeightSpace_eq_weightSpace_exponentCharacter,
    finrank_exponentWeightSpace_fieldBaseChange,
    finrank_exponentWeightSpace_fieldBaseChange]
  exact congrArg (fun p => p m)
    (exponentWeightRankProfile_eq_of_isLocalRing I G i _ _)

/-- Root membership of every fixed-exponent actual character agrees on any
 two field-valued fibres over the local base. -/
theorem mem_roots_fieldBaseChange_iff_of_isLocalRing (m : I → ℤ) :
    exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (baseChangeHom (K := k) G I i) ↔
      exponentCharacter (Spec (CommRingCat.of l)) I m ∈
        roots (baseChangeHom (K := l) G I i) := by
  rw [mem_roots_iff_finrank_ne_zero, mem_roots_iff_finrank_ne_zero,
    finrank_weightSpace_eq_of_isLocalRing (k := k) (l := l) I G i m,
    exponentCharacter_eq_characterLatticeEquiv_symm,
    exponentCharacter_eq_characterLatticeEquiv_symm]
  simp only [ne_eq, AddEquiv.map_eq_zero_iff]

/-- The actual character lattices of two field fibres, compared through their
 common integral coordinates. -/
def fieldCharacterEquiv :
    characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) ≃+
      characterLattice (commGroupScheme (Spec (CommRingCat.of l)) I) :=
  (characterLatticeEquiv k I).trans (characterLatticeEquiv l I).symm

/-- Integral-coordinate comparison restricts to an equivalence of the actual
 root sets on any two field-valued fibres of the supplied group. -/
def fieldRootsEquiv :
    roots (T := commGroupScheme _ I) (baseChangeHom (K := k) G I i) ≃
      roots (T := commGroupScheme _ I) (baseChangeHom (K := l) G I i) :=
  (fieldCharacterEquiv (k := k) (l := l) I).toEquiv.subtypeEquiv (by
    intro χ
    obtain ⟨m, rfl⟩ := (characterLatticeEquiv k I).symm.surjective χ
    change (characterLatticeEquiv k I).symm m ∈ roots _ ↔
      (characterLatticeEquiv l I).symm
        (characterLatticeEquiv k I ((characterLatticeEquiv k I).symm m)) ∈ roots _
    rw [AddEquiv.apply_symm_apply, ← exponentCharacter_eq_characterLatticeEquiv_symm,
      ← exponentCharacter_eq_characterLatticeEquiv_symm]
    exact mem_roots_fieldBaseChange_iff_of_isLocalRing (k := k) (l := l) I G i m)

set_option linter.unusedSectionVars false in
@[simp]
theorem fieldRootsEquiv_character (α : roots (T := commGroupScheme _ I)
    (baseChangeHom (K := k) G I i)) :
    (fieldRootsEquiv (k := k) (l := l) I G i α).val =
      (characterLatticeEquiv l I).symm (characterLatticeEquiv k I α.val) := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem fieldRootsEquiv_coordinates (α : roots (T := commGroupScheme _ I)
    (baseChangeHom (K := k) G I i)) :
    characterLatticeEquiv l I (fieldRootsEquiv (k := k) (l := l) I G i α).val =
      characterLatticeEquiv k I α.val :=
  (characterLatticeEquiv l I).apply_symm_apply _

end Langlands.GroupScheme.splitTorus
