import Langlands.GroupScheme.RelativeLevi.ParabolicRootLatticeComparison

/-! # Comparing the lattices on two field fibres of a split group -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : IsFibrewiseRootDatumOf I G i P)

local instance fibreComparisonAffine {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap R k)))

/-- The same exponent coordinates compare the full lattices of any two
field fibres. Constancy of roots is supplied by the fibrewise root datum. -/
def fibreParabolicRootLatticeComparison
    (k l : Type u) [Field k] [Algebra R k] [Field l] [Algebra R l] :
    ParabolicRootLatticeComparison
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (U := splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)
      (splitTorus.baseChangeHom (K := k) G I i)
      (splitTorus.baseChangeHom (K := l) G I i) where
  characterEquiv := (splitTorus.characterLatticeEquiv k I).trans
    (splitTorus.characterLatticeEquiv l I).symm
  cocharacterEquiv := (splitTorus.cocharacterLatticeEquiv k I).trans
    (splitTorus.cocharacterLatticeEquiv l I).symm
  root_mem_iff α := by
    obtain ⟨m, rfl⟩ := (splitTorus.characterLatticeEquiv k I).symm.surjective α
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      ← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact (hP.mem_roots_iff l m).trans (hP.mem_roots_iff k m).symm
  pairing α ν := by
    obtain ⟨m, rfl⟩ := (splitTorus.characterLatticeEquiv k I).symm.surjective α
    obtain ⟨n, rfl⟩ := (splitTorus.cocharacterLatticeEquiv k I).symm.surjective ν
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      ← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      ← splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm,
      ← splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter]

@[simp] theorem fibreParabolicRootLatticeComparison_cocharacter
    (k l : Type u) [Field k] [Algebra R k] [Field l] [Algebra R l]
    (n : I → ℤ) :
    (fibreParabolicRootLatticeComparison I G i P hP k l).cocharacterEquiv
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) =
      splitTorus.exponentCocharacter (Spec (CommRingCat.of l)) I n := by
  simp only [fibreParabolicRootLatticeComparison, AddEquiv.trans_apply,
    splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm,
    AddEquiv.apply_symm_apply]

end Langlands.GroupScheme
