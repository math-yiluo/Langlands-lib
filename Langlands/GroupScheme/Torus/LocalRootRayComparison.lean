import Langlands.GroupScheme.Torus.LocalRootSupportComparison
import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Rational.RootRayDecomposition

/-! # Root-ray geometry between field fibres over a local ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.splitTorus

open RelativeRoot

variable {k l : Type u} [Field k] [Field l]
  (I : Type u) [Fintype I] [DecidableEq I]

/-- Cocharacter comparison through the same integral exponent coordinates. -/
def fieldCocharacterEquiv :
    cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) ≃+
      cocharacterLattice (commGroupScheme (Spec (CommRingCat.of l)) I) :=
  (cocharacterLatticeEquiv k I).trans (cocharacterLatticeEquiv l I).symm

omit [DecidableEq I] in
/-- The coordinate comparisons preserve the actual integer lattice pairing. -/
theorem latticePairing_fieldEquiv
    (a : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    latticePairing (commGroupScheme (Spec (CommRingCat.of l)) I)
      (fieldCharacterEquiv (k := k) (l := l) I a)
      (fieldCocharacterEquiv (k := k) (l := l) I ν) =
      latticePairing (commGroupScheme (Spec (CommRingCat.of k)) I) a ν := by
  simp only [latticePairing_eq_sum, fieldCharacterEquiv, fieldCocharacterEquiv,
    AddEquiv.trans_apply, AddEquiv.apply_symm_apply]

omit [DecidableEq I] in
private theorem fieldCharacterEquiv_nsmul
    (a : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) (m : ℕ) :
    fieldCharacterEquiv (k := k) (l := l) I (m • a) =
      m • fieldCharacterEquiv (k := k) (l := l) I a :=
  map_nsmul (fieldCharacterEquiv (k := k) (l := l) I).toAddMonoidHom m a

/-- Character comparison keeps every specified exponent vector. -/
@[simp] theorem fieldCharacterEquiv_exponentCharacter (m : I → ℤ) :
    fieldCharacterEquiv (k := k) (l := l) I
      (exponentCharacter (Spec (CommRingCat.of k)) I m) =
        exponentCharacter (Spec (CommRingCat.of l)) I m := by
  simp only [exponentCharacter_eq_characterLatticeEquiv_symm,
    fieldCharacterEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]

/-- Cocharacter comparison keeps every specified exponent vector. -/
@[simp] theorem fieldCocharacterEquiv_exponentCocharacter (m : I → ℤ) :
    fieldCocharacterEquiv (k := k) (l := l) I
      (exponentCocharacter (Spec (CommRingCat.of k)) I m) =
        exponentCocharacter (Spec (CommRingCat.of l)) I m := by
  simp only [exponentCocharacter_eq_cocharacterLatticeEquiv_symm,
    fieldCocharacterEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]

/-- Positive integral rays are preserved and reflected by coordinate comparison. -/
theorem mem_cyclicTail_fieldCharacterEquiv_iff
    (a x : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (r : ℕ) :
    fieldCharacterEquiv (k := k) (l := l) I x ∈
      cyclicTail (fieldCharacterEquiv (k := k) (l := l) I a) r ↔
      x ∈ cyclicTail a r := by
  constructor
  · rintro ⟨m, hmr, hm, he⟩
    refine ⟨m, hmr, hm, ?_⟩
    apply (fieldCharacterEquiv (k := k) (l := l) I).injective
    simpa only [fieldCharacterEquiv_nsmul] using he
  · rintro ⟨m, hmr, hm, rfl⟩
    exact ⟨m, hmr, hm, (fieldCharacterEquiv_nsmul (k := k) (l := l) I a m).symm⟩

/-- The same coordinate comparison preserves disjointness of complete rays. -/
theorem disjoint_cyclicTail_fieldCharacterEquiv_iff
    (a b : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (r s : ℕ) :
    Disjoint
      (cyclicTail (fieldCharacterEquiv (k := k) (l := l) I a) r :
        Set (characterLattice (commGroupScheme (Spec (CommRingCat.of l)) I)))
      (cyclicTail (fieldCharacterEquiv (k := k) (l := l) I b) s :
        Set (characterLattice (commGroupScheme (Spec (CommRingCat.of l)) I))) ↔
      Disjoint (cyclicTail a r : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)))
        (cyclicTail b s : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))) := by
  simp only [Set.disjoint_left]
  constructor
  · intro h x hxa hxb
    exact h ((mem_cyclicTail_fieldCharacterEquiv_iff I a x r).mpr hxa)
      ((mem_cyclicTail_fieldCharacterEquiv_iff I b x s).mpr hxb)
  · intro h y hya hyb
    obtain ⟨x, rfl⟩ := (fieldCharacterEquiv (k := k) (l := l) I).surjective y
    exact h ((mem_cyclicTail_fieldCharacterEquiv_iff I a x r).mp hya)
      ((mem_cyclicTail_fieldCharacterEquiv_iff I b x s).mp hyb)

variable {R : Type u} [CommRing R] [IsLocalRing R]
  [Algebra R k] [Algebra R l]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance localRootRayAffine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

/-- The coordinate comparison preserves and reflects all actual roots. -/
theorem mem_roots_fieldCharacterEquiv_iff
    (a : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    fieldCharacterEquiv (k := k) (l := l) I a ∈
        roots (baseChangeHom (K := l) G I i) ↔
      a ∈ roots (baseChangeHom (K := k) G I i) := by
  obtain ⟨m, rfl⟩ := (characterLatticeEquiv k I).symm.surjective a
  change (characterLatticeEquiv l I).symm
    (characterLatticeEquiv k I ((characterLatticeEquiv k I).symm m)) ∈ roots _ ↔ _
  rw [AddEquiv.apply_symm_apply, ← exponentCharacter_eq_characterLatticeEquiv_symm,
    ← exponentCharacter_eq_characterLatticeEquiv_symm]
  exact (mem_roots_fieldBaseChange_iff_of_isLocalRing (k := k) (l := l) I G i m).symm

/-- Divisibility within the actual root set is unchanged between field fibres. -/
theorem mem_indivisibleRoots_fieldCharacterEquiv_iff
    (a : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    fieldCharacterEquiv (k := k) (l := l) I a ∈
        indivisibleRoots (baseChangeHom (K := l) G I i) ↔
      a ∈ indivisibleRoots (baseChangeHom (K := k) G I i) := by
  change (_ ∈ roots _ ∧ _) ↔ (a ∈ roots _ ∧ _)
  rw [mem_roots_fieldCharacterEquiv_iff I G i]
  apply and_congr_right
  intro _
  constructor
  · intro h b hb m hm he
    apply h (fieldCharacterEquiv (k := k) (l := l) I b)
      ((mem_roots_fieldCharacterEquiv_iff I G i b).mpr hb) m hm
    simpa only [fieldCharacterEquiv_nsmul] using congrArg (fieldCharacterEquiv (k := k) (l := l) I) he
  · intro h b hb m hm he
    obtain ⟨c, rfl⟩ := (fieldCharacterEquiv (k := k) (l := l) I).surjective b
    apply h c ((mem_roots_fieldCharacterEquiv_iff I G i c).mp hb) m hm
    apply (fieldCharacterEquiv (k := k) (l := l) I).injective
    simpa only [fieldCharacterEquiv_nsmul] using he

/-- Actual indivisible positive roots correspond for corresponding cocharacters. -/
theorem mem_indivisiblePositiveRoots_fieldCharacterEquiv_iff
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (a : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    fieldCharacterEquiv (k := k) (l := l) I a ∈
        indivisiblePositiveRoots (baseChangeHom (K := l) G I i)
          (fieldCocharacterEquiv (k := k) (l := l) I ν) ↔
      a ∈ indivisiblePositiveRoots (baseChangeHom (K := k) G I i) ν := by
  change (_ ∈ indivisibleRoots _ ∧ 0 < _) ↔ (a ∈ indivisibleRoots _ ∧ 0 < _)
  rw [mem_indivisibleRoots_fieldCharacterEquiv_iff I G i, latticePairing_fieldEquiv]

/-- An exact enumeration on one fibre transports with its original order and size. -/
theorem range_fieldCharacterEquiv_indivisiblePositiveRoots
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    {n : ℕ}
    (a : Fin n → characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (ha : Set.range a = indivisiblePositiveRoots (baseChangeHom (K := k) G I i) ν) :
    Set.range (fun r => fieldCharacterEquiv (k := k) (l := l) I (a r)) =
      indivisiblePositiveRoots (baseChangeHom (K := l) G I i)
        (fieldCocharacterEquiv (k := k) (l := l) I ν) := by
  ext b
  obtain ⟨c, rfl⟩ := (fieldCharacterEquiv (k := k) (l := l) I).surjective b
  rw [mem_indivisiblePositiveRoots_fieldCharacterEquiv_iff I G i, ← ha]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (fieldCharacterEquiv (k := k) (l := l) I).injective hr⟩
  · rintro ⟨r, rfl⟩
    exact Set.mem_range_self r

/-- Disjoint positive-root rays on one field fibre suffice on every field fibre. -/
theorem disjoint_positive_rays_fieldBaseChange
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hdisj : ∀ a ∈ indivisiblePositiveRoots (baseChangeHom (K := k) G I i) ν,
      ∀ b ∈ indivisiblePositiveRoots (baseChangeHom (K := k) G I i) ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)))
          (cyclicTail b 1 : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)))) :
    ∀ a ∈ indivisiblePositiveRoots (baseChangeHom (K := l) G I i)
        (fieldCocharacterEquiv (k := k) (l := l) I ν),
      ∀ b ∈ indivisiblePositiveRoots (baseChangeHom (K := l) G I i)
        (fieldCocharacterEquiv (k := k) (l := l) I ν), a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of l)) I)))
          (cyclicTail b 1 : Set (characterLattice (commGroupScheme (Spec (CommRingCat.of l)) I))) := by
  intro a ha b hb hne
  obtain ⟨c, rfl⟩ := (fieldCharacterEquiv (k := k) (l := l) I).surjective a
  obtain ⟨d, rfl⟩ := (fieldCharacterEquiv (k := k) (l := l) I).surjective b
  apply (disjoint_cyclicTail_fieldCharacterEquiv_iff I c d 1 1).mpr
  exact hdisj c ((mem_indivisiblePositiveRoots_fieldCharacterEquiv_iff I G i ν c).mp ha)
    d ((mem_indivisiblePositiveRoots_fieldCharacterEquiv_iff I G i ν d).mp hb)
    (fun h => hne (congrArg _ h))

end Langlands.GroupScheme.splitTorus
