import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget

/-!
# Standard Levi Weyl images on actual rational points

The comparison uses the same normalizer representatives and exact standard Levi
point subgroups on both sides. The two ambient subgroup comparisons remain
explicit hypotheses.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The subgroup of the actual ambient Weyl quotient represented in the exact
standard Levi point subgroup. -/
def pointStandardWeyl (I : Finset (SimpleRoot i ν)) : Subgroup (Weyl i) :=
  (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν I)).range

theorem mem_pointStandardWeyl_iff (I : Finset (SimpleRoot i ν)) (w : Weyl i) :
    w ∈ pointStandardWeyl i ν I ↔
      ∃ n : Group.RelativeWeyl.normalizer (torusPoints i),
        (n : RationalPoint k G.X) ∈ levi i ν I ∧ QuotientGroup.mk n = w := by
  constructor
  · rintro ⟨v, rfl⟩
    induction v using Quotient.inductionOn' with
    | h n =>
      exact ⟨⟨n, n.property.1⟩, n.property.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨QuotientGroup.mk ⟨n, n.property, hn⟩, rfl⟩

/-- Under the centralizer comparison, the standard Levi contains the full
point-image centralizer used as the Weyl denominator. -/
theorem pointCentralizer_le_levi (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) :
    Group.RelativeWeyl.centralizer (torusPoints i) ≤ levi i ν I := by
  rw [← hZ]
  exact centralizerPoints_le_levi i ν I

/-- The ambient Weyl comparison carries the exact scheme-standard Weyl image
onto the image of the actual Levi Weyl quotient. -/
theorem weylEquiv_map_schemeStandardWeyl
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) :
    (schemeStandardWeyl i ν I).map (weylEquiv i hN hZ).toMonoidHom =
      pointStandardWeyl i ν I := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases (mem_standardRelativeWeylGroup_iff i ν).mp hv with ⟨n, hn, rfl⟩
    apply (mem_pointStandardWeyl_iff i ν I _).mpr
    exact ⟨normalizerEquiv i hN n, hn, weylEquiv_mk i hN hZ n⟩
  · intro hw
    rcases (mem_pointStandardWeyl_iff i ν I w).mp hw with ⟨n, hn, rfl⟩
    refine ⟨QuotientGroup.mk ((normalizerEquiv i hN).symm n), ?_, ?_⟩
    · exact (mem_standardRelativeWeylGroup_iff i ν).mpr
        ⟨(normalizerEquiv i hN).symm n, hn, rfl⟩
    · change weylEquiv i hN hZ
        (QuotientGroup.mk ((normalizerEquiv i hN).symm n)) = QuotientGroup.mk n
      rw [weylEquiv_mk, MulEquiv.apply_symm_apply]

/-- The restriction of the ambient comparison to the standard Weyl images. -/
def standardWeylImageEquiv
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) :
    schemeStandardWeyl i ν I ≃* pointStandardWeyl i ν I :=
  ((weylEquiv i hN hZ).subgroupMap (schemeStandardWeyl i ν I)).trans
    (MulEquiv.subgroupCongr (weylEquiv_map_schemeStandardWeyl i ν hN hZ I))

@[simp] theorem standardWeylImageEquiv_apply
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) (w : schemeStandardWeyl i ν I) :
    (standardWeylImageEquiv i ν hN hZ I w : Weyl i) =
      weylEquiv i hN hZ w :=
  rfl

/-- The actual Levi quotient identifies with the exact scheme-standard Weyl
subgroup through the injective actual quotient inclusion. -/
def leviWeylEquiv
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) :
    LeviWeyl i ν I ≃* schemeStandardWeyl i ν I :=
  (MonoidHom.ofInjective
    (Group.RelativeWeyl.inclusion_injective (torusPoints i) (levi i ν I))).trans
      (standardWeylImageEquiv i ν hN hZ I).symm

/-- The comparison commutes with the actual inclusion in the ambient quotient. -/
@[simp] theorem weylEquiv_leviWeylEquiv
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν)) (w : LeviWeyl i ν I) :
    weylEquiv i hN hZ (leviWeylEquiv i ν hN hZ I w : relativeWeylGroup i) =
      Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν I) w := by
  have h := congrArg (fun v : pointStandardWeyl i ν I => (v : Weyl i))
    ((standardWeylImageEquiv i ν hN hZ I).apply_symm_apply
      (MonoidHom.ofInjective
        (Group.RelativeWeyl.inclusion_injective (torusPoints i) (levi i ν I)) w))
  exact h

/-- On each normalizer class the Levi comparison preserves the ambient point. -/
theorem leviWeylEquiv_mk
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizerIn (torusPoints i) (levi i ν I)) :
    (leviWeylEquiv i ν hN hZ I (QuotientGroup.mk n) : relativeWeylGroup i) =
      QuotientGroup.mk
        ((normalizerEquiv i hN).symm ⟨n, n.property.1⟩) := by
  apply (weylEquiv i hN hZ).injective
  rw [weylEquiv_leviWeylEquiv, Group.RelativeWeyl.inclusion_mk,
    weylEquiv_mk, MulEquiv.apply_symm_apply]
  rfl

end Langlands.Aubert.General.RationalPointFamily
