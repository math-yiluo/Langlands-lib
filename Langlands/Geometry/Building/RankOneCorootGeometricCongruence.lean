import Langlands.Geometry.Building.RankOneCorootTransport
import Langlands.Geometry.Building.KPLocalWeilRestrictionCongruence
import Langlands.Geometry.Building.KPLocalCorootComponentStatement

/-! # Geometric character congruence for transported rank-one coroot points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.LocalField Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The pointwise factorization and all-character clause of the local coroot target,
for a specified source and morphism. -/
def CorootComponentCongruenceProperty (a : characterLattice B.S)
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (f : T ⟶ B.centralizerTorus hZ) : Prop :=
  ∀ (x : B.Apartment) (u u' : rationalPoints H),
    u ∈ B.rootGroup a → u ≠ 1 → u' ∈ B.rootGroup (-a) → u' ≠ 1 →
    ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a u + x.val (-a) u') →
    ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
      v' ∈ B.rootGroup (-a) → v ∈ B.rootGroup a →
      u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
      ∃ c : rationalPoints T.toGrp,
        rationalPoints.map (CommGroupScheme.groupHom f) c = z ∧
        ∀ χ : rationalCharacters (baseChanged (UnramifiedClosure F) (SeparableClosure F) T.toGrp),
          ((r : ℝ) : WithTop ℝ) ≤
            algebraicExtensionAddValuation F (SeparableClosure F)
              ((rationalCharacterEval χ
                (rationalExtend (UnramifiedClosure F) (SeparableClosure F) T.toGrp c) :
                  SeparableClosure F) - 1)

variable {B hZ} {b : characterLattice B.S}

namespace ValuedSL2RootCoordinates

variable (C : ValuedSL2RootCoordinates B hZ b)

/-- The supplied scheme coroot viewed in the commutative category. -/
def corootMorphism :
    WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension ⟶
      B.centralizerTorus hZ :=
  Additive.ofMul C.coroot

theorem corootComponentCongruenceProperty (hb : b ≠ 0) :
    CorootComponentCongruenceProperty B hZ b
      (WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension)
      C.corootMorphism := by
  intro x u u' hu _hu1 hu' _hu1' r hr hdepth v' v z hv' hv hfactor
  obtain ⟨t, htz, ht⟩ := C.exists_corootPoint_of_factorization hb x u u' hu hu'
    (r : ℝ) (by exact_mod_cast hr) hdepth.symm v' v z hv' hv hfactor
  refine ⟨(WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm t, ?_, ?_⟩
  · exact htz
  · intro χ
    exact MaximalUnramified.weilGm_geometricCharacter_bound F C.extension
      (MaximalUnramified.valuationSubring_isHenselian F) hr t ht.ge χ

end ValuedSL2RootCoordinates

namespace ValuedSU3RootCoordinates

variable (C : ValuedSU3RootCoordinates B hZ b)

/-- The supplied scheme coroot viewed in the commutative category. -/
def corootMorphism :
    WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension ⟶
      B.centralizerTorus hZ :=
  Additive.ofMul C.coroot

theorem corootComponentCongruenceProperty (hb : b ≠ 0) :
    CorootComponentCongruenceProperty B hZ b
      (WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension)
      C.corootMorphism := by
  intro x u u' hu _hu1 hu' _hu1' r hr hdepth v' v z hv' hv hfactor
  obtain ⟨t, htz, ht⟩ := C.exists_corootPoint_of_factorization hb x u u' hu hu'
    (r : ℝ) (by exact_mod_cast hr) hdepth.symm v' v z hv' hv hfactor
  refine ⟨(WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm t, ?_, ?_⟩
  · exact htz
  · intro χ
    exact MaximalUnramified.weilGm_geometricCharacter_bound F C.extension
      (MaximalUnramified.valuationSubring_isHenselian F) hr t ht χ

theorem double_corootComponentCongruenceProperty (hb : b ≠ 0) :
    CorootComponentCongruenceProperty B hZ (2 • b)
      (WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension)
      C.corootMorphism := by
  intro x u u' hu _hu1 hu' _hu1' r hr hdepth v' v z hv' hv hfactor
  obtain ⟨t, htz, ht⟩ := C.exists_corootPoint_of_double_factorization hb x u u' hu hu'
    (r : ℝ) (by exact_mod_cast hr) hdepth.symm v' v z hv' hv hfactor
  refine ⟨(WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm t, ?_, ?_⟩
  · exact htz
  · intro χ
    exact MaximalUnramified.weilGm_geometricCharacter_bound F C.extension
      (MaximalUnramified.valuationSubring_isHenselian F) hr t ht.ge χ

end ValuedSU3RootCoordinates

end Langlands.Geometry.Building
