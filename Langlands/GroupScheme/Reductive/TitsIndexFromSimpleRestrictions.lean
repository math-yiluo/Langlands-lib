import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Rational.FaceSimpleRootRestriction

/-! # Actual Tits indices from positivity on simple restrictions -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace RootPairing.Base

variable {J M N A : Type*} [Finite J]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup A]
  (P : RootDatum J M N) (b : P.Base)
  (ρ : M →+ A) (ℓ : A →+ ℤ)
  (h : ∀ a ∈ b.support, ρ (P.root a) = 0 ∨ 0 < ℓ (ρ (P.root a)))

include h in
/-- A positive root has either zero image or strictly positive image value. -/
theorem restriction_zero_or_pos {a : J} (ha : b.IsPos a) :
    ρ (P.root a) = 0 ∨ 0 < ℓ (ρ (P.root a)) := by
  apply ha.induction_on_add h
  intro a c z hz ha hc
  rw [hz, map_add, map_add]
  rcases ha with ha | ha <;> rcases h c hc with hc | hc
  · exact Or.inl (by rw [ha, hc, zero_add])
  · exact Or.inr (by rw [ha, map_zero, zero_add]; exact hc)
  · exact Or.inr (by rw [hc, map_zero, add_zero]; exact ha)
  · exact Or.inr (add_pos ha hc)

include h in
/-- Nonzero root images have the same sign as the base's positive roots. -/
theorem isPos_iff_restriction_pos (a : J) (ha : ρ (P.root a) ≠ 0) :
    b.IsPos a ↔ 0 < ℓ (ρ (P.root a)) := by
  constructor
  · intro hp
    exact (restriction_zero_or_pos P b ρ ℓ h hp).resolve_left ha
  · intro hp
    let := P.indexNeg
    rcases IsPos.or_neg b a with hpos | hneg
    · exact hpos
    · have hn : ρ (P.root (-a)) ≠ 0 := by simpa using ha
      have hlt : 0 < -ℓ (ρ (P.root a)) := by
        simpa using (restriction_zero_or_pos P b ρ ℓ h hneg).resolve_left hn
      omega

include b h in
/-- The functional detects zero on every root image. -/
theorem restriction_value_ne_zero (a : J) (ha : ρ (P.root a) ≠ 0) :
    ℓ (ρ (P.root a)) ≠ 0 := by
  let := P.indexNeg
  rcases IsPos.or_neg b a with hpos | hneg
  · exact ((isPos_iff_restriction_pos P b ρ ℓ h a ha).mp hpos).ne'
  · have hn : ρ (P.root (-a)) ≠ 0 := by simpa using ha
    have hlt : 0 < -ℓ (ρ (P.root a)) := by
      simpa using (restriction_zero_or_pos P b ρ ℓ h hneg).resolve_left hn
    omega

end RootPairing.Base

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom]

namespace GaloisPinningData

variable (p : GaloisPinningData K (SeparableClosure K) G)
  (S : CommGroupScheme (Spec (CommRingCat.of K))) (hS : IsSplitTorus S.toGrp)
  (f : S ⟶ p.torus) (ν : cocharacterLattice S)

/-- Each actual simple restriction is zero or pairs positively with the
supplied cocharacter of the split torus. -/
def SimpleRestrictionsPositive : Prop :=
  ∀ a ∈ p.base.support,
    absoluteRootRestriction p S hS f a = 0 ∨
      0 < latticePairing S (absoluteRootRestriction p S hS f a) ν

/-- The actual restriction on the entire character lattice. -/
def restrictionHom :
    characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap K (SeparableClosure K))).obj p.torus) →+ characterLattice S where
  toFun χ := (characterLattice.baseChangeEquiv (algebraBaseMap K (SeparableClosure K)) S hS).symm
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map f ≫ χ)
  map_zero' := by rw [Limits.comp_zero, map_zero]
  map_add' χ ψ := by rw [Preadditive.comp_add, map_add]

variable {p S hS f ν}

/-- Positivity on the simple restrictions implies compatibility on every
absolute root whose restriction is nonzero. -/
theorem SimpleRestrictionsPositive.compatible (h : p.SimpleRestrictionsPositive S hS f ν)
    (a : p.rootIndex) (ha : absoluteRootRestriction p S hS f a ≠ 0) :
    p.base.IsPos a ↔ 0 < latticePairing S (absoluteRootRestriction p S hS f a) ν :=
  RootPairing.Base.isPos_iff_restriction_pos p.rootDatum p.base
    (p.restrictionHom S hS f) ((latticePairing S).flip ν).toAddMonoidHom h a ha

/-- The same simple-root hypothesis gives nonzero pairing on all nonzero
absolute restrictions. -/
theorem SimpleRestrictionsPositive.pairing_ne_zero
    (h : p.SimpleRestrictionsPositive S hS f ν)
    (a : p.rootIndex) (ha : absoluteRootRestriction p S hS f a ≠ 0) :
    latticePairing S (absoluteRootRestriction p S hS f a) ν ≠ 0 :=
  RootPairing.Base.restriction_value_ne_zero p.rootDatum p.base
    (p.restrictionHom S hS f) ((latticePairing S).flip ν).toAddMonoidHom h a ha

variable [LocallyOfFiniteType G.X.hom]

/-- A prescribed pinning and maximal split torus define actual index data
once zero-or-positive pairing is known for the simple restrictions. -/
def titsIndexOfSimpleRestrictions (hG : IsSemisimple G)
    (hT : IsMaximalTorus p.inclusion)
    (s : S.toGrp ⟶ G) (hs : IsMaximalSplitTorus s)
    (hsq : CommGroupScheme.groupHom f ≫ p.inclusion = s)
    (h : p.SimpleRestrictionsPositive S hS f ν) : TitsIndexData G where
  isSemisimple := hG
  pinning := p
  maximalTorus := hT
  splitTorus := S
  splitInclusion := s
  maximalSplit := hs
  torusMap := f
  square := hsq
  positiveCocharacter := ν
  generic := by
    intro α hα
    rw [← hsq] at hα
    obtain ⟨hne, β, hβ, hβα⟩ :=
      (mem_roots_iff_exists_splittingField_restriction hS p.isSplitTorus f p.inclusion α).mp hα
    rw [← p.isRootDatum.2.1] at hβ
    obtain ⟨a, rfl⟩ := hβ
    have ha : absoluteRootRestriction p S hS f a = α := by
      apply (characterLattice.baseChangeEquiv (algebraBaseMap K (SeparableClosure K)) S hS).injective
      unfold absoluteRootRestriction
      rw [AddEquiv.apply_symm_apply]
      exact hβα
    rw [← ha]
    exact h.pairing_ne_zero a (by rwa [ha])
  compatible := h.compatible

end GaloisPinningData

end Langlands.GroupScheme
