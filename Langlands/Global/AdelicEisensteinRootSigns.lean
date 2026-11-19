import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Representation.Plancherel.ParabolicRootCone
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.OppositeIntersectionRootInclusions
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # The Eisenstein positive roots and parabolics containing the inducing parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Plancherel

variable {F : Type u} [Field F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [LocallyOfFiniteType G.X.hom]

/-- The nonzero restricted positive roots in the convergence statement are exactly the
positive roots of the actual split-component cocharacter. -/
theorem unipotentRoots_eq_intrinsicPositiveRoots (hG : IsConnectedReductive G) :
    r.unipotentRoots = r.intrinsicPositiveRoots := by
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hroot := relativeRootSystem F G hG r.data.T r.data.i r.isCompatible.maximalSplit
  ext α
  constructor
  · rintro ⟨h0, β, hβ, rfl⟩
    exact (r.restrict_positive_eq_zero_or_mem hβ).resolve_left h0
  · intro hα
    obtain ⟨β, hβ, hres⟩ := r.exists_positiveRoot_restrict
      (fun β hβ => hroot.neg_mem_relativeRoots r.data.i hT hβ) hα
    exact ⟨hα.1.1, β, hβ, hres⟩

/-- The defining cocharacter is nonzero on every actual relative root of the
split component. -/
theorem isGeneric_splitComponentCocharacter (hG : IsConnectedReductive G) :
    IsGenericCocharacter (a ≫ l ≫ p) r.splitComponentCocharacter := by
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hA := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hroot := relativeRootSystem F G hG r.data.T r.data.i r.isCompatible.maximalSplit
  intro α hα
  obtain ⟨h0, β, hβ, hres⟩ := (parabolic_mem_relativeRoots_iff r hA hT α).mp hα
  rcases lt_or_gt_of_ne (r.isCompatible.generic β hβ) with hneg | hpos
  · have hnβ : -β ∈ positiveRelativeRoots r.data.i r.data.ν :=
      ⟨hroot.neg_mem_relativeRoots r.data.i hT hβ, by simpa using neg_pos.mpr hneg⟩
    have hn := r.restrict_positive_eq_zero_or_mem hnβ
    rw [Preadditive.comp_neg, hres] at hn
    have hpos' := (hn.resolve_left (neg_ne_zero.mpr h0)).2
    rw [map_neg, LinearMap.neg_apply] at hpos'
    omega
  · have hp := r.restrict_positive_eq_zero_or_mem (alpha := β) ⟨hβ, hpos⟩
    rw [hres] at hp
    exact (hp.resolve_left h0).2.ne'

/-- Admissibility on the entire opposite radical gives a containing dynamic
parabolic for the negative of the admissible cocharacter. -/
theorem parabolic_le_of_oppositeAdmissible (hG : IsConnectedReductive G)
    (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) :
    SubgroupFunctor.range p ≤ Dynamic.parabolic (CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p) := by
  let := hG.smooth
  let := hG.connectedSpace
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hA := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hroot := relativeRootSystem F G hG r.data.T r.data.i r.isCompatible.maximalSplit
  rw [r.parabolic_eq_splitComponentCocharacter]
  apply (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hA
    (a ≫ l ≫ p) r.splitComponentCocharacter (-mu)).mpr
  intro α hα hα0
  have hpos := lt_of_le_of_ne hα0 ((r.isGeneric_splitComponentCocharacter hG α hα).symm)
  have hnegα := parabolic_neg_mem_relativeRoots r hroot hA hT hα
  have hn : latticePairing A (-α) r.splitComponentCocharacter < 0 := by
    simpa only [map_neg, LinearMap.neg_apply] using neg_lt_zero.mpr hpos
  have hp : 0 < latticePairing A (-α) (-r.splitComponentCocharacter) := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hpos
  simpa only [map_neg, LinearMap.neg_apply] using hmu (-α) hnegα hn hp

variable [IsAffine G.X.left]

/-- The inducing parabolic factors through the dynamic representative for the
negative of an admissible cocharacter. -/
def oppositeAdmissibleParabolicFactor (hG : IsConnectedReductive G)
    (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) :
    P ⟶ Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p) :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom _).factorHom p
    (r.parabolic_le_of_oppositeAdmissible hG mu hmu)

@[simp]
theorem oppositeAdmissibleParabolicFactor_comp (hG : IsConnectedReductive G)
    (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) :
    r.oppositeAdmissibleParabolicFactor hG mu hmu ≫
      Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p) = p :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom _).factorHom_comp _ _

end Langlands.GroupScheme.ParabolicRootPresentation
