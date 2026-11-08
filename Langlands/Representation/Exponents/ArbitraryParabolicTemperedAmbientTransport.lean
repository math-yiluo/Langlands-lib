import Langlands.Representation.Exponents.ArbitraryParabolicTemperedConjugation
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Normalized-exponent temperedness under an ambient scheme isomorphism -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section GroupTransport

variable {Γ Δ : Type u} [Group Γ] [Group Δ]
  [TopologicalSpace Γ] [TopologicalSpace Δ]
  [LocallyCompactSpace Γ] [LocallyCompactSpace Δ]
  [NonarchimedeanGroup Γ] [NonarchimedeanGroup Δ]
  {B : Type w} [Group B] {N L : Subgroup Γ} {N' L' : Subgroup Δ}

/-- Transport of the actual normalized quotients, restricted to corresponding
maps from one unchanged group. The quotient representatives are unchanged. -/
def normalizedJacquetRestrictedAmbientEquiv
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hN' : IsClosed (N' : Set Δ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Δ))
    (e : Δ ≃ₜ* Γ) (hNN' : ∀ x : Δ, x ∈ N' ↔ e x ∈ N)
    (hLL' : ∀ x : Δ, x ∈ L' ↔ e x ∈ L)
    (rho : B →* L) (rho' : B →* L')
    (hrho : ∀ t : B, GroupTransport.subgroupEquiv e hLL' (rho' t) = rho t)
    (π : SmoothRep.{0, u, v} ℂ Γ) :
    Representation.Equiv
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp rho)
      (((normalizedJacquetFunctor N' L' hN' hLN').obj
        (SmoothRep.pullback e π)).representation.comp rho') := by
  let t := Jacquet.Localization.transportEquiv
    (π.representation.comp e.toMonoidHom) π.representation N' N 1 1
    (GroupTransport.subgroupEquiv e hNN').toMulEquiv (LinearEquiv.refl ℂ π)
    (fun _ _ => rfl) (fun _ => rfl)
  refine Representation.Equiv.mk t.symm ?_
  intro b
  apply Jacquet.Localization.hom_ext
  ext x
  have ht (y : π) : t.symm (Jacquet.Localization.mk π.representation N 1 y) =
      Jacquet.Localization.mk (π.representation.comp e.toMonoidHom) N' 1 y := by
    apply t.injective
    rw [t.apply_symm_apply]
    rfl
  have he : e (rho' b : Δ) = (rho b : Γ) := congrArg Subtype.val (hrho b)
  change t.symm
      (((HaarModulus.closedInverseHalfCharacter N hN L hLN (rho b) : ℂˣ) : ℂ) •
        Jacquet.Localization.mk π.representation N 1 (π.representation (rho b) x)) =
    ((HaarModulus.closedInverseHalfCharacter N' hN' L' hLN' (rho' b) : ℂˣ) : ℂ) •
      Jacquet.Localization.mk (π.representation.comp e.toMonoidHom) N' 1
        (π.representation (e (rho' b : Δ)) x)
  rw [GroupTransport.closedInverseHalfCharacter_transport e hNN' hLL' hN hN'
    hLN hLN' (rho' b), hrho b, he, map_smul, ht]

end GroupTransport

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]

local instance arbitraryParabolicTemperedAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology
local instance arbitraryParabolicTemperedAmbientPointTopology' : TopologicalSpace (rationalPoints G') :=
  RationalPointFamily.pointTopology

/-- The canonical topological group equivalence is the actual rational-point
map of the specified group-scheme isomorphism. -/
def ambientIsoPointsEquiv (e : G' ≅ G) : rationalPoints G' ≃ₜ* rationalPoints G := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  exact {
    toFun := rationalPoints.map e.hom
    invFun := rationalPoints.map e.inv
    left_inv := fun x => by
      rw [← pointMap_comp_apply, Iso.hom_inv_id]
      rfl
    right_inv := fun x => by
      rw [← pointMap_comp_apply, Iso.inv_hom_id]
      rfl
    map_mul' := (rationalPoints.map e.hom).map_mul
    continuous_toFun := continuous_rationalPointMap k e.hom.hom.hom
    continuous_invFun := continuous_rationalPointMap k e.inv.hom.hom }

@[simp] theorem ambientIsoPointsEquiv_apply (e : G' ≅ G) (x : rationalPoints G') :
    ambientIsoPointsEquiv e x = rationalPoints.map e.hom x := rfl

/-- Membership in the point image of a subgroup is preserved by the actual
point map of the ambient isomorphism. -/
theorem mem_pointImage_comp_ambientIso {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G') (e : G' ≅ G) (x : rationalPoints G') :
    x ∈ pointImage j ↔ ambientIsoPointsEquiv e x ∈ pointImage (j ≫ e.hom) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, pointMap_comp_apply j e.hom y⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (ambientIsoPointsEquiv e).injective ?_⟩
    exact (pointMap_comp_apply j e.hom y).symm.trans hy

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints G')] [NonarchimedeanGroup (rationalPoints G')]

section Exponents

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G') (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Ambient transport and pullback preserve each actual normalized Jacquet
exponent, with the character and the Levi and radical source maps fixed. -/
theorem isNormalizedJacquetExponent_comp_ambientIso_iff (ha : IsSplitComponent a)
    (e : G' ≅ G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent (p ≫ e.hom) l r (hp.comp_iso e) hl hr hmul ha π χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha
        (SmoothRep.pullback (ambientIsoPointsEquiv e) π) χ := by
  rw [isNormalizedJacquetExponent_iff, isNormalizedJacquetExponent_iff]
  have hN : ∀ x : rationalPoints G', x ∈ pointImage (r ≫ p) ↔
      ambientIsoPointsEquiv e x ∈ pointImage (r ≫ (p ≫ e.hom)) := by
    intro x
    simpa only [Category.assoc] using mem_pointImage_comp_ambientIso (r ≫ p) e x
  have hL : ∀ x : rationalPoints G', x ∈ pointImage (l ≫ p) ↔
      ambientIsoPointsEquiv e x ∈ pointImage (l ≫ (p ≫ e.hom)) := by
    intro x
    simpa only [Category.assoc] using mem_pointImage_comp_ambientIso (l ≫ p) e x
  apply isGeneralizedEigencharacter_iff_of_equiv
    (normalizedJacquetRestrictedAmbientEquiv
      (isClosed_pointImage_comp (p ≫ e.hom) r (hp.comp_iso e).isClosedSubgroup
        hr.1.isClosedSubgroup)
      (pointImage_le_normalizer (p ≫ e.hom) l r hr)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (pointImage_le_normalizer p l r hr)
      (ambientIsoPointsEquiv e) hN hL _ _ ?_ π) χ
  intro t
  apply Subtype.ext
  change rationalPoints.map e.hom (rationalPoints.map (l ≫ p) (rationalPoints.map a t)) =
    rationalPoints.map (l ≫ (p ≫ e.hom)) (rationalPoints.map a t)
  simp only [pointMap_comp_apply]

end Exponents

section ConeCondition

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G') (l : M ⟶ P) (a : A.toGrp ⟶ M)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a)

/-- Ambient pullback preserves coverage by root presentations and every
normalized exponent test in every compatible presentation. -/
theorem satisfiesNormalizedExponentConeCondition_comp_ambientIso_iff
    (e : G' ≅ G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    SatisfiesNormalizedExponentConeCondition (p ≫ e.hom) l a (hp.comp_iso e) hl ha π ↔
      SatisfiesNormalizedExponentConeCondition p l a hp hl ha
        (SmoothRep.pullback (ambientIsoPointsEquiv e) π) := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨pres⟩ := hne
      exact ⟨pres.invCompAmbientIso e⟩
    · intro pres U r hr hmul χ hχ
      have hc := h (pres.compAmbientIso e) U r hr hmul χ
        ((isNormalizedJacquetExponent_comp_ambientIso_iff
          p l r hp hl hr hmul ha e π χ).mpr hχ)
      simpa only [ParabolicRootPresentation.nonnegCone_compAmbientIso] using hc
  · rintro ⟨hne, h⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨pres⟩ := hne
      exact ⟨pres.compAmbientIso e⟩
    · intro pres U r hr hmul χ hχ
      have hc := h (pres.invCompAmbientIso e) U r hr hmul χ
        ((isNormalizedJacquetExponent_comp_ambientIso_iff
          p l r hp hl hr hmul ha e π χ).mp hχ)
      simpa only [ParabolicRootPresentation.nonnegCone_invCompAmbientIso] using hc

end ConeCondition

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Normalized-exponent temperedness transports through any actual ambient
scheme isomorphism with the canonical topology on both point groups. -/
theorem IsNormalizedExponentTempered.pullback_ambientIso
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (e : G' ≅ G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : IsNormalizedExponentTempered hG π) :
    IsNormalizedExponentTempered hG'
      (SmoothRep.pullback (ambientIsoPointsEquiv e) π) := by
  have := hG.smooth
  have := hG'.smooth
  refine ⟨isAdmissible_comp_continuousMulEquiv π.representation
    (ambientIsoPointsEquiv e) hπ.isAdmissible, ?_⟩
  intro P M A p l a hp hl ha
  exact (satisfiesNormalizedExponentConeCondition_comp_ambientIso_iff
    p l a hp hl ha e π).mp (hπ.parabolic (p ≫ e.hom) l a (hp.comp_iso e) hl ha)

end Langlands.Aubert.General.RepresentedParabolic
