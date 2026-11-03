import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # The reversed chamber and actual opposite rational subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A generic chamber remains generic after reversal. -/
theorem IsGenericCocharacter.neg (hν : IsGenericCocharacter i ν) :
    IsGenericCocharacter i (-ν) := by
  intro α hα
  simpa only [map_neg, neg_ne_zero] using hν α hα

/-- Simultaneous negation preserves positive-root membership. -/
theorem neg_mem_positiveRelativeRoots_iff
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (α : characterLattice T) :
    -α ∈ positiveRelativeRoots i (-ν) ↔ α ∈ positiveRelativeRoots i ν := by
  constructor
  · rintro ⟨hα, hpos⟩
    exact ⟨by simpa only [neg_neg] using hneg (-α) hα, by simpa using hpos⟩
  · rintro ⟨hα, hpos⟩
    exact ⟨hneg α hα, by simpa using hpos⟩

/-- A decomposition in the reversed positive system negates to a decomposition
in the original one, so simple roots negate to simple roots. -/
theorem neg_mem_simpleRelativeRoots
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) :
    -α ∈ simpleRelativeRoots i (-ν) := by
  refine ⟨(neg_mem_positiveRelativeRoots_iff i ν hneg α).2 hα.1, ?_⟩
  rintro ⟨β, hβ, γ, hγ, heq⟩
  apply hα.2
  refine ⟨-β, ?_, -γ, ?_, ?_⟩
  · simpa only [neg_neg] using
      (neg_mem_positiveRelativeRoots_iff i (-ν) hneg β).2 hβ
  · simpa only [neg_neg] using
      (neg_mem_positiveRelativeRoots_iff i (-ν) hneg γ).2 hγ
  · simpa only [neg_neg, neg_add] using congrArg Neg.neg heq

/-- Reversal identifies exactly the two actual simple-root sets. -/
theorem neg_mem_simpleRelativeRoots_iff
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (α : characterLattice T) :
    -α ∈ simpleRelativeRoots i (-ν) ↔ α ∈ simpleRelativeRoots i ν := by
  constructor
  · intro hα
    simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg hα
  · exact neg_mem_simpleRelativeRoots i ν hneg

/-- Negating both the face and the cocharacter gives a standard cocharacter
for the reversed chamber. -/
theorem IsStandardCocharacter.neg
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν J ζ) :
    IsStandardCocharacter i (-ν) (Neg.neg '' J) (-ζ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν hneg (hζ.1 hα)
  · rintro _ ⟨α, hα, rfl⟩
    simpa using hζ.2.1 α hα
  · intro α hα hαJ
    have hs : -α ∈ simpleRelativeRoots i ν := by
      simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg hα
    have hn : -α ∉ J := by
      intro h
      exact hαJ ⟨-α, h, neg_neg α⟩
    simpa only [map_neg, LinearMap.neg_apply] using hζ.2.2 (-α) hs hn

/-- The reversed root-indexed subgroups are the opposite dynamic subgroups,
and their Levi is the original standard Levi, on every test scheme. -/
theorem standardSubgroups_reversedChamber
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardParabolic i (-ν) (Neg.neg '' J) =
        Dynamic.parabolic (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)) ∧
      standardLevi i (-ν) (Neg.neg '' J) = standardLevi i ν J ∧
      standardUnipotent i (-ν) (Neg.neg '' J) =
        Dynamic.unipotent (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)) := by
  have := hi.isSplitSubtorus.mono
  have hζneg := hζ.neg i ν hneg
  obtain ⟨hP, hM, hU⟩ :=
    (hStandard k G hG T i hi (-ν) (hν.neg i ν) _ hζneg.subset).2 (-ζ) hζneg
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at hP hM hU
  have hMorig :=
    ((hStandard k G hG T i hi ν hν J hζ.subset).2 ζ hζ).2.1
  exact ⟨hP, hM.trans ((Dynamic.centralizer_inverseCocharacter _).trans hMorig.symm), hU⟩

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)

/-- Negation as an equivalence of the literal actual simple-root labels. -/
def oppositeSimpleRootEquiv : SimpleRoot i ν ≃ SimpleRoot i (-ν) where
  toFun α := ⟨-α.val, neg_mem_simpleRelativeRoots i ν hneg α.property⟩
  invFun α := ⟨-α.val, by
    simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg α.property⟩
  left_inv α := Subtype.ext (neg_neg α.val)
  right_inv α := Subtype.ext (neg_neg α.val)

/-- The finite face with all actual simple-root labels negated. -/
def oppositeIndex (I : Finset (SimpleRoot i ν)) : Finset (SimpleRoot i (-ν)) :=
  I.map (oppositeSimpleRootEquiv i ν hneg).toEmbedding

/-- The transported finite face has exactly the negated character subset. -/
theorem rootSet_oppositeIndex (I : Finset (SimpleRoot i ν)) :
    rootSet i (-ν) (oppositeIndex i ν hneg I) = Neg.neg '' rootSet i ν I := by
  ext α
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact ⟨a.val, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨oppositeSimpleRootEquiv i ν hneg a,
      Finset.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩

/-- The dynamic opposite parabolic agrees with the actual reversed standard
parabolic at the transported literal face. -/
theorem oppositeParabolic_eq_reversed
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    oppositeParabolic i ζ = parabolic i (-ν) (oppositeIndex i ν hneg I) := by
  change _ = (standardParabolic i (-ν)
    (rootSet i (-ν) (oppositeIndex i ν hneg I))).carrier (Over.mk (𝟙 _))
  rw [rootSet_oppositeIndex, (standardSubgroups_reversedChamber i ν
    hStandard hG hi hν hneg hζ).1]
  rfl

/-- Reversing the chamber and face preserves the exact actual Levi subgroup. -/
theorem levi_oppositeIndex
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    levi i (-ν) (oppositeIndex i ν hneg I) = levi i ν I := by
  change (standardLevi i (-ν)
    (rootSet i (-ν) (oppositeIndex i ν hneg I))).carrier (Over.mk (𝟙 _)) = _
  rw [rootSet_oppositeIndex, (standardSubgroups_reversedChamber i ν
    hStandard hG hi hν hneg hζ).2.1]

/-- The dynamic opposite radical is the actual reversed standard radical. -/
theorem oppositeUnipotent_eq_reversed
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    oppositeUnipotent i ζ = unipotent i (-ν) (oppositeIndex i ν hneg I) := by
  change _ = (standardUnipotent i (-ν)
    (rootSet i (-ν) (oppositeIndex i ν hneg I))).carrier (Over.mk (𝟙 _))
  rw [rootSet_oppositeIndex, (standardSubgroups_reversedChamber i ν
    hStandard hG hi hν hneg hζ).2.2]
  rfl

/-- At the self-association target's root-system scope, no separate
negation-closure hypothesis is needed for the actual opposite comparisons. -/
theorem oppositeSubgroups_eq_reversedStandardPoints
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    {J : Set (characterLattice T)} (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν J ζ) :
    oppositeParabolic i ζ = standardParabolicPoints i (-ν) (Neg.neg '' J) ∧
      standardLeviPoints i (-ν) (Neg.neg '' J) = standardLeviPoints i ν J ∧
      oppositeUnipotent i ζ = standardUnipotentPoints i (-ν) (Neg.neg '' J) := by
  have := hi.isSplitSubtorus.mono
  have hneg' : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i :=
    fun _ hα => hRoots.neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα
  obtain ⟨hP, hM, hU⟩ :=
    standardSubgroups_reversedChamber i ν hStandard hG hi hν hneg' hζ
  exact ⟨congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hP.symm,
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hM,
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hU.symm⟩

end Langlands.Aubert.General.RationalPointFamily
