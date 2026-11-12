import Langlands.Representation.LanglandsClassification.PQRegularIntertwiningDimension
import Langlands.Representation.Intertwining.OppositeIdentitySupportStatement

/-! # Reduction of opposite regularity to its kernel and identity-support inputs -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The ideal-comaximality part of the opposite-regularity target, with its unchanged
Langlands-triplet telescope and independent universes. -/
def LanglandsTripletOppositeKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Pbar Ubar : GroupScheme (Spec (CommRingCat.of k)))
      (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Ubar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
      (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
      (hmulbar : IsIso (subgroupMultiplication lbar rbar)),
      lbar ≫ pbar = l ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) →
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
        IsPQRegular p l r hp hr hl hmul pbar lbar rbar hpbar hrbar hlbar hmulbar a τ

/-- The exact VII.4.1 target follows from opposite identity support and its kernel part. -/
def LanglandsTripletOppositeRegularityReductionStatement : Prop :=
  OppositeIdentitySupportStatement.{u, v} →
    LanglandsTripletOppositeKernelStatement.{u, v} →
      LanglandsTripletOppositeRegularityStatement.{u, v}

/-- Twisting preserves the needed admissibility and irreducibility; the proved actual
parabolic dimension calculation supplies the second clause of the exact target. -/
theorem langlandsTripletOppositeRegularity_of_kernel_and_identitySupport :
    LanglandsTripletOppositeRegularityReductionStatement.{u, v} := by
  intro hS hK k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  have hreg := hK k G hG T i ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp hTrip
  obtain ⟨e⟩ := hS k G hG P M U Pbar Ubar p l r hp hl hr hmul pbar lbar rbar
    hpbar hlbar hrbar hmulbar hLevi hOpp τ
  exact ⟨hreg, pqRegular_intertwining_finrank_eq_one hG p l r hp hl hr hmul
    pbar lbar rbar hpbar hlbar hrbar hmulbar a ha τ hreg e hadm hirr⟩

end Langlands.Aubert.General.RepresentedParabolic
