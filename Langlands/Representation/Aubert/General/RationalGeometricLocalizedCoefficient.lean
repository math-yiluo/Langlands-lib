import Langlands.Representation.Aubert.General.GeometricCoefficientAction
import Langlands.Representation.Jacquet.Localization

/-! # Actual localized geometric coefficient actions and smooth realization -/

noncomputable section

universe u uA uB uR uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section NormalLocalization

variable {R : Type uR} [CommRing R]
  {A : Type uA} [Group A] {B : Type uB} [Group B]
  {V : Type uV} [AddCommGroup V] [Module R V]

private theorem normal_top_le_normalizer (N : Subgroup A) [N.Normal] :
    (⊤ : Subgroup A) ≤ Subgroup.normalizer N := by
  rw [Subgroup.normalizer_eq_top]

/-- Trivial-character localization with the actual action pulled back along s. -/
private def normalLocalizedSectionAction (ρ : Representation R A V)
    (N : Subgroup A) [N.Normal] (s : B →* A) :
    Representation R B (Jacquet.Localization.Coinvariants ρ N 1) :=
  (Jacquet.Localization.action ρ N 1 ⊤ (normal_top_le_normalizer N)
    (Jacquet.Localization.isInvariant_one N ⊤ (normal_top_le_normalizer N))).comp
      ((Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm.toMonoidHom.comp s)

/-- Use the published trivial-character equivalence, retaining the section action. -/
private def normalLocalizedSectionEquiv (ρ : Representation R A V)
    (N : Subgroup A) [N.Normal] (s : B →* A) :
    (normalLocalizedSectionAction ρ N s).Equiv ((ρ.toCoinvariants N).comp s) where
  toLinearEquiv :=
    (Jacquet.Localization.trivialEquiv ρ N ⊤ (normal_top_le_normalizer N)).toLinearEquiv
  isIntertwining' b := by
    apply Jacquet.Localization.hom_ext
    ext v
    rfl

private theorem normalLocalizedSectionEquiv_mk (ρ : Representation R A V)
    (N : Subgroup A) [N.Normal] (s : B →* A) (v : V) :
    normalLocalizedSectionEquiv ρ N s (Jacquet.Localization.mk ρ N 1 v) =
      Jacquet.mk ρ N v := rfl

private theorem isSmooth_normalLocalizedSectionAction
    [TopologicalSpace A] [TopologicalSpace B]
    (ρ : Representation R A V) (N : Subgroup A) [N.Normal] (s : B →* A)
    (hs : Continuous s) (hρ : IsSmooth ρ) :
    IsSmooth (normalLocalizedSectionAction ρ N s) :=
  isSmooth_of_surjective
    (show Representation.IntertwiningMap (ρ.comp s) (normalLocalizedSectionAction ρ N s) from
      { toLinearMap := Jacquet.Localization.mk ρ N 1
        isIntertwining' _ := rfl })
    (Jacquet.Localization.mk_surjective ρ N 1) (isSmooth_comp s hs hρ)

end NormalLocalization

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (parabolic i ν I)
local notation "N" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker dI.projection)
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (levi i ν I)
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection (levi i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  (parabolic i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  dJ (n : RationalPoint k G.X)
local notation "s" => geometricCoefficientSection
  (parabolic i ν I) (levi i ν I) (unipotent i ν I) (parabolic i ν J)
  dI (n : RationalPoint k G.X)

variable {R : Type uR} [CommRing R]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- The actual trivial-character localized coefficient quotient, with target section action. -/
abbrev geometricLocalizedCoefficientAction (σ : Representation R (levi i ν J) V) :
    Representation R K (Jacquet.Localization.Coinvariants (σ.comp f) N 1) :=
  normalLocalizedSectionAction (σ.comp f) N s

@[simp] theorem geometricLocalizedCoefficientAction_mk
    (σ : Representation R (levi i ν J) V) (l : K) (v : V) :
    geometricLocalizedCoefficientAction i ν I J dI dJ n σ l
        (Jacquet.Localization.mk (σ.comp f) N 1 v) =
      Jacquet.Localization.mk (σ.comp f) N 1 (σ (f (s l)) v) := rfl

variable
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "p" => geometricCoefficientLeviMap
  (levi i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget

/-- Trivial localization identifies the actual source Jacquet coefficient action,
with inverse conjugation and inflation through the actual target projection. -/
def geometricLocalizedCoefficientEquiv (σ : Representation R (levi i ν J) V) :
    (geometricLocalizedCoefficientAction i ν I J dI dJ n σ).Equiv
      ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p) :=
  (normalLocalizedSectionEquiv (σ.comp f) N s).trans
    (geometricCoefficientActionEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ)

@[simp] theorem geometricLocalizedCoefficientEquiv_mk
    (σ : Representation R (levi i ν J) V) (v : V) :
    geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ (Jacquet.Localization.mk (σ.comp f) N 1 v) =
      Jacquet.mk σ S v :=
  geometricCoefficientActionEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ v

@[simp] theorem geometricLocalizedCoefficientEquiv_symm_mk
    (σ : Representation R (levi i ν J) V) (v : V) :
    (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ).symm (Jacquet.mk σ S v) =
      Jacquet.Localization.mk (σ.comp f) N 1 v := by
  exact (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ).toLinearEquiv.symm_apply_eq.mpr
      (geometricLocalizedCoefficientEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ v).symm

set_option maxHeartbeats 800000 in
/-- Every original coefficient intertwiner commutes with the class-preserving comparison. -/
theorem geometricLocalizedCoefficientEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module R W]
    {σ : Representation R (levi i ν J) V} {τ : Representation R (levi i ν J) W}
    (T : σ.IntertwiningMap τ) (z : Jacquet.Localization.Coinvariants (σ.comp f) N 1) :
    geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget τ
        (Jacquet.Localization.mapLinear N 1 (geometricCoefficientIntertwiner i ν I J dJ n T) z) =
      Jacquet.map S Ls hSource.levi_le_normalizer T
        (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
          hSource hTarget σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective (σ.comp f) N 1 z
  change geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget τ (Jacquet.Localization.mk (τ.comp f) N 1 (T v)) = _
  rw [geometricLocalizedCoefficientEquiv_mk, geometricLocalizedCoefficientEquiv_mk]
  rfl

section Smooth

variable [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
  (hproj : Continuous dJ.projection)

include hproj in
/-- Smoothness follows from the original inducing projection and the actual target section. -/
theorem isSmooth_geometricLocalizedCoefficientAction
    (σ : Representation R (levi i ν J) V) (hσ : IsSmooth σ) :
    IsSmooth (geometricLocalizedCoefficientAction i ν I J dI dJ n σ) :=
  isSmooth_normalLocalizedSectionAction (σ.comp f) N s
    (continuous_geometricCoefficientSection _ _ _ _ dI _)
    (isSmooth_comp f (continuous_geometricCoefficientProjection _ _ _ _ dJ _ hproj) hσ)

include hStandard hG hi hν hN dI dJ hproj in
/-- The ordinary inflated source action is smooth through the actual quotient equivalence. -/
theorem isSmooth_geometricSourceCoefficientAction
    (σ : Representation R (levi i ν J) V) (hσ : IsSmooth σ) :
    IsSmooth ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p) :=
  isSmooth_of_surjective
    (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ).toIntertwiningMap
    (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ).surjective
    (isSmooth_geometricLocalizedCoefficientAction i ν I J dI dJ n hproj σ hσ)

/-- The comparison is an isomorphism on the two original smooth quotient carriers. -/
def geometricLocalizedCoefficientSmoothIso (σ : SmoothRep R (levi i ν J)) :
    SmoothRep.of (geometricLocalizedCoefficientAction i ν I J dI dJ n σ.representation)
        (isSmooth_geometricLocalizedCoefficientAction i ν I J dI dJ n hproj
          σ.representation σ.isSmooth) ≅
      SmoothRep.of ((Jacquet.action σ.representation S Ls hSource.levi_le_normalizer).comp p)
        (isSmooth_geometricSourceCoefficientAction i ν hStandard hG hi hν hN I J dI dJ n
          hSource hTarget hproj σ.representation σ.isSmooth) :=
  SmoothRep.mkIso (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ.representation)

end Smooth
end RationalPointFamily
end Langlands.Aubert.General
