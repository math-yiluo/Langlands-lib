import Langlands.GroupScheme.Rational.CocharacterCone
import Langlands.GroupScheme.Rational.CocharacterStandardFace

/-! # Strict standard faces of the nonnegative integral quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterCone

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The image of the existing standard cocharacters for `J` in the integral
quotient by the common simple-root annihilator. -/
def strictFace (J : Set (characterLattice T)) :
    Set (cocharacterLattice T ⧸
      RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν)) :=
  (RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν)).mkQ ''
    {ξ | IsStandardCocharacter i ν J ξ}

/-- Standardness depends only on the quotient class. -/
theorem isStandardCocharacter_iff_of_mkQ_eq (J : Set (characterLattice T))
    (ξ η : cocharacterLattice T)
    (h : (RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν)).mkQ ξ =
      (RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν)).mkQ η) :
    IsStandardCocharacter i ν J ξ ↔ IsStandardCocharacter i ν J η := by
  have hdiff := (Submodule.Quotient.eq _).mp h
  have hp := (RealTorusSpace.mem_rootAnnihilatorInt
    (simpleRelativeRoots i ν) (ξ - η)).mp hdiff
  have he : ∀ α ∈ simpleRelativeRoots i ν,
      latticePairing T α ξ = latticePairing T α η := by
    intro α hα
    exact sub_eq_zero.mp (by simpa only [map_sub] using hp α hα)
  constructor
  · rintro ⟨hJ, hzero, hpos⟩
    exact ⟨hJ, fun α hα => (he α (hJ hα)).symm.trans (hzero α hα),
      fun α hα hαJ => (he α hα) ▸ hpos α hα hαJ⟩
  · rintro ⟨hJ, hzero, hpos⟩
    exact ⟨hJ, fun α hα => (he α (hJ hα)).trans (hzero α hα),
      fun α hα hαJ => (he α hα).symm ▸ hpos α hα hαJ⟩

/-- Every representative of a class in a strict face is standard for its index. -/
@[simp] theorem mkQ_mem_strictFace_iff (J : Set (characterLattice T))
    (ξ : cocharacterLattice T) :
    (RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν)).mkQ ξ ∈
      strictFace i ν J ↔ IsStandardCocharacter i ν J ξ := by
  constructor
  · rintro ⟨η, hη, hηξ⟩
    exact (isStandardCocharacter_iff_of_mkQ_eq i ν J η ξ hηξ).mp hη
  · intro hξ
    exact ⟨ξ, hξ, rfl⟩

/-- Strict faces lie in the existing nonnegative quotient monoid. -/
theorem strictFace_subset_quotient (J : Set (characterLattice T)) :
    strictFace i ν J ⊆ quotient T (simpleRelativeRoots i ν) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨ξ, fun α hα => hξ.nonneg i ν hα, rfl⟩

/-- Every nonnegative quotient class lies in exactly one strict standard face. -/
theorem existsUnique_strictFace
    (x : quotient T (simpleRelativeRoots i ν)) :
    ∃! J : Set (characterLattice T), x.val ∈ strictFace i ν J := by
  obtain ⟨ξ, hξ, hx⟩ := x.property
  refine ⟨simpleRootFace i ν ξ,
    ⟨ξ, isStandardCocharacter_simpleRootFace i ν hξ, hx⟩, ?_⟩
  intro J hJ
  obtain ⟨η, hη, hηx⟩ := hJ
  have hηξ := hηx.trans hx.symm
  exact ((isStandardCocharacter_iff_of_mkQ_eq i ν J η ξ hηξ).mp hη).eq_simpleRootFace i ν

/-- The strict standard faces cover precisely the nonnegative quotient. -/
theorem iUnion_strictFace :
    (⋃ J : Set (characterLattice T), strictFace i ν J) =
      (quotient T (simpleRelativeRoots i ν) : Set _) := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hJ⟩ := Set.mem_iUnion.mp hx
    exact strictFace_subset_quotient i ν J hJ
  · intro hx
    obtain ⟨J, hJ, _⟩ := existsUnique_strictFace i ν ⟨x, hx⟩
    exact Set.mem_iUnion.mpr ⟨J, hJ⟩

/-- Distinct indices give disjoint strict faces, including empty faces. -/
theorem strictFace_disjoint {J K : Set (characterLattice T)} (hJK : J ≠ K) :
    Disjoint (strictFace i ν J) (strictFace i ν K) := by
  rw [Set.disjoint_left]
  intro x hxJ hxK
  have hx := strictFace_subset_quotient i ν J hxJ
  obtain ⟨L, _, hL⟩ := existsUnique_strictFace i ν ⟨x, hx⟩
  exact hJK ((hL J hxJ).trans (hL K hxK).symm)

/-- A face with an index outside the simple roots is empty. -/
theorem strictFace_eq_empty_of_not_subset (J : Set (characterLattice T))
    (hJ : ¬ J ⊆ simpleRelativeRoots i ν) : strictFace i ν J = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨ξ, hξ, _⟩
  exact hJ hξ.1

end Langlands.GroupScheme.CocharacterCone
