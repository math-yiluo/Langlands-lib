import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralFamily

/-! # Actual comparison with the standard spectral family -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

section StandardComparison

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ (standardLeviModel hG hi hnu I).scheme)
  (hb : ∀ I, IsSplitComponent (b I))
  [hNormal : ∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [hMeas : ∀ I, MeasurableSpace (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I)))
  [hHaar : ∀ I, (eta I).IsHaarMeasure]

/-- The substantive split-component/quotient-measure comparison, stated on
identical actual smooth-dual classes. No coefficient equivalence is an input. -/
def RationalSemistandardStandardDiscreteSeriesComparison : Prop :=
  ∀ (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi (standardIndex hG hi hnu I))),
    IsDiscreteSeriesClass
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      (mu (standardIndex hG hi hnu I)) omega ↔
    @IsDiscreteSeriesClass.{u, uV} (levi (standardIndex hG hi hnu I))
      (inferInstanceAs (Group (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (TopologicalSpace (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (IsTopologicalGroup (levi (standardIndex hG hi hnu I))))
      (rationalLeviSplitCenter I (b I)) (hNormal I)
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) (hMeas I) (eta I) (hHaar I) omega

variable (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
  a ha mu hG hi hnu b hb eta)

/-- Changing split-component presentations retains the very same actual
representation isomorphism class. -/
def rationalStandardFullDiscreteSeriesEquiv (I : Finset (RationalPointFamily.SimpleRoot i nu)) :
    @DiscreteSeriesClass.{u, uV} (levi (standardIndex hG hi hnu I))
      (inferInstanceAs (Group (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (TopologicalSpace (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (IsTopologicalGroup (levi (standardIndex hG hi hnu I))))
      (rationalLeviSplitCenter I (b I)) (hNormal I)
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) (hMeas I) (eta I) (hHaar I) ≃
    DiscreteSeriesClass.{u, uV}
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      (mu (standardIndex hG hi hnu I)) where
  toFun x := ⟨x.val, (hds I x.val).mpr x.property⟩
  invFun x := ⟨x.val, (hds I x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex actual discrete-series orbits by the model comparison fixing every
literal Levi element and every actual unitary character value. -/
def rationalStandardFullOrbitEquiv (I : Finset (RationalPointFamily.SimpleRoot i nu)) :
    RationalLeviOrbitClass.{u, uV} b hb eta I ≃
      OrbitClass.{u, uV} (chosenLeviModel (standardIndex hG hi hnu I))
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I))
        (mu (standardIndex hG hi hnu I)) :=
  Quotient.congr (rationalStandardFullDiscreteSeriesEquiv a ha mu hG hi hnu b hb eta hds I) (by
    intro x y
    constructor
    · rintro ⟨chi, hchi⟩
      refine ⟨(standardLeviModel hG hi hnu I).unitaryCharactersEquiv
        (chosenLeviModel (standardIndex hG hi hnu I)) chi, Subtype.ext ?_⟩
      have h := congrArg Subtype.val hchi
      exact h
    · rintro ⟨chi, hchi⟩
      refine ⟨((standardLeviModel hG hi hnu I).unitaryCharactersEquiv
        (chosenLeviModel (standardIndex hG hi hnu I))).symm chi, Subtype.ext ?_⟩
      have h := congrArg Subtype.val hchi
      exact h)

@[simp] theorem rationalStandardFullOrbitEquiv_mk
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (x : @DiscreteSeriesClass.{u, uV} (levi (standardIndex hG hi hnu I))
      (inferInstanceAs (Group (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (TopologicalSpace (levi (standardIndex hG hi hnu I))))
      (inferInstanceAs (IsTopologicalGroup (levi (standardIndex hG hi hnu I))))
      (rationalLeviSplitCenter I (b I)) (hNormal I)
      (rationalLeviSplitCenter_le_center I (b I) (hb I)) (hMeas I) (eta I) (hHaar I)) :
    rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I (Quotient.mk _ x) =
      Quotient.mk _ (rationalStandardFullDiscreteSeriesEquiv.{u, uV}
        a ha mu hG hi hnu b hb eta hds I x) := rfl

/-- The old standard pair maps to its actual full semistandard pair. -/
def rationalStandardFullIndex (t : RationalStandardTheta.{u, uV} b hb eta) :
    RationalSemistandardTheta.{u, uV} a ha mu :=
  ⟨standardIndex hG hi hnu t.1,
    rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds t.1 t.2⟩

include hds in
/-- The old representative is a discrete series for the full-family split
component and Haar data, by the explicit comparison on its actual class. -/
theorem rationalStandardRepresentative_full_isSquareIntegrable
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    IsSquareIntegrableModCentralSubgroup
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      (rationalOrbitRepresentative.{u, uV} b hb eta I O).obj.representation
      (mu (standardIndex hG hi hnu I)) :=
  (hds I (Quotient.mk _ (rationalOrbitRepresentative.{u, uV} b hb eta I O))).mpr
    (rationalOrbitRepresentative_isSquareIntegrable b hb eta I O)

/-- This literal old representation belongs to the mapped actual full orbit. -/
theorem mk_discreteSeriesClass_rationalStandardRepresentative_full
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    (Quotient.mk _ (discreteSeriesClass
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter (a (standardIndex hG hi hnu I)))
      ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
      (mu (standardIndex hG hi hnu I)) (rationalOrbitRepresentative.{u, uV} b hb eta I O)
      (rationalStandardRepresentative_full_isSquareIntegrable.{u, uV}
        a ha mu hG hi hnu b hb eta hds I O)) :
      OrbitClass.{u, uV} (chosenLeviModel (standardIndex hG hi hnu I))
        (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I))
        (mu (standardIndex hG hi hnu I))) =
      rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O := by
  have h := congrArg (rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I)
    (mk_discreteSeriesClass_rationalOrbitRepresentative b hb eta I O)
  exact h

/-- Compare actual component sections by the published representative change
and the canonical model map through the identical all-test Levi subgroup. -/
def rationalStandardFullComponentEquiv
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    RationalSemistandardThetaSection.{u, uV} a ha mu
      (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds ⟨I, O⟩) ≃ₗ[ℂ]
      OrbitSections (standardLeviModel hG hi hnu I)
        (rationalOrbitRepresentative.{u, uV} b hb eta I O) :=
  (orbitSectionsBaseEquiv.{u, uV} (chosenLeviModel (standardIndex hG hi hnu I))
    (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I))
    (mu (standardIndex hG hi hnu I))
    (rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O)
    (rationalOrbitRepresentative.{u, uV} b hb eta I O)
    (rationalStandardRepresentative_full_isSquareIntegrable.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O)
    (mk_discreteSeriesClass_rationalStandardRepresentative_full.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O)).trans
    ((chosenLeviModel (standardIndex hG hi hnu I)).orbitSectionsModelEquiv
      (standardLeviModel hG hi hnu I) (rationalOrbitRepresentative.{u, uV} b hb eta I O))

/-- The standard-to-full index has finite fibers, without needing geometric
finiteness of the full semistandard index. -/
theorem rationalStandardFullIndex_finite_fibers
    (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    ((rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds) ⁻¹' {t}).Finite := by
  have := finite_simpleRoot hG hi hnu
  let X := ↥((rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds) ⁻¹' {t})
  have hinj : Function.Injective (fun s : X => s.val.1) := by
    rintro ⟨⟨I, O⟩, hx⟩ ⟨⟨J, Q⟩, hy⟩ h
    change rationalStandardFullIndex a ha mu hG hi hnu b hb eta hds ⟨I, O⟩ = t at hx
    change rationalStandardFullIndex a ha mu hG hi hnu b hb eta hds ⟨J, Q⟩ = t at hy
    change I = J at h
    subst J
    have hO := eq_of_heq (Sigma.mk.inj_iff.mp (hx.trans hy.symm)).2
    have heq : O = Q := (rationalStandardFullOrbitEquiv.{u, uV}
      a ha mu hG hi hnu b hb eta hds I).injective hO
    apply Subtype.ext
    cases heq
    rfl
  have : Finite X := Finite.of_injective _ hinj
  exact Set.toFinite _

/-- Restrict to the existing standard product using the actual orbit,
representative and model comparisons. -/
def rationalStandardFullRestrict :
    RationalSemistandardThetaSections.{u, uV} a ha mu →ₗ[ℂ]
      RationalStandardThetaSections.{u, uV} hG hi hnu b hb eta where
  toFun f I O := rationalStandardFullComponentEquiv.{u, uV}
    a ha mu hG hi hnu b hb eta hds I O
      (f (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds ⟨I, O⟩))
  map_add' f g := by
    funext I O
    exact (rationalStandardFullComponentEquiv.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O).map_add _ _
  map_smul' c f := by
    funext I O
    exact (rationalStandardFullComponentEquiv.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O).map_smul c _

/-- Canonical standard restriction followed by the specified orbit and actual
component changes is the comparison with the old standard family. -/
theorem rationalStandardFullRestrict_canonical
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds f I O =
      rationalStandardFullComponentEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O
        (rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu f
          ⟨I, rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O⟩) := rfl

/-- Component changes are linear equivalences, so the nonzero support is
exactly the preimage of the full support. -/
theorem rationalStandardFullRestrict_support
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    {t : RationalStandardTheta.{u, uV} b hb eta |
      rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds f t.1 t.2 ≠ 0} =
      (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds) ⁻¹'
        rationalSemistandardThetaSupport.{u, uV} a ha mu f := by
  ext t
  exact not_congr (map_eq_zero_iff (rationalStandardFullComponentEquiv.{u, uV}
    a ha mu hG hi hnu b hb eta hds t.1 t.2)
    (rationalStandardFullComponentEquiv.{u, uV}
      a ha mu hG hi hnu b hb eta hds t.1 t.2).injective)

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (hsm : ModelSmoothComparisonStatement.{u, uV} (F := F) (G := G) (i := i))
  {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))

include hsm in
/-- Smoothness is preserved by the constructed actual comparison, conditional
only on the substantive comparison of the prescribed model/compact pictures. -/
theorem rationalStandardFullComponentEquiv_smooth
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I)
    (q : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
      (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds ⟨I, O⟩)) :
    rationalStandardFullComponentEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O q.val ∈
      rationalInducedSmoothOrbitSections hG hi hnu I hK hPK
        (rationalOrbitRepresentative.{u, uV} b hb eta I O) := by
  let q' := orbitSmoothSectionsBaseEquiv.{u, uV}
    (chosenLeviModel (standardIndex hG hi hnu I))
    (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I))
    (mu (standardIndex hG hi hnu I)) (d (standardIndex hG hi hnu I))
    (rationalStandardFullOrbitEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O)
    (rationalOrbitRepresentative.{u, uV} b hb eta I O)
    (rationalStandardRepresentative_full_isSquareIntegrable.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O)
    (mk_discreteSeriesClass_rationalStandardRepresentative_full.{u, uV}
      a ha mu hG hi hnu b hb eta hds I O) q
  exact (hsm (standardIndex hG hi hnu I)
    (chosenLeviModel (standardIndex hG hi hnu I)) (standardLeviModel hG hi hnu I)
    (d (standardIndex hG hi hnu I)) (standardCompactData hG hi hnu I hK hPK)
    (rationalOrbitRepresentative.{u, uV} b hb eta I O) q'.val).mpr q'.property

/-- Restriction into the existing standard smooth finite-support family.
The two substantive comparisons are explicit hypotheses; support preservation
uses the proved finite fibers of the actual index map. -/
def rationalStandardFullSmoothRestrict :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      rationalStandardThetaSmoothSections.{u, uV} hG hi hnu hK hPK b hb eta where
  toFun f := ⟨rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds f.val,
    (fun I O => rationalStandardFullComponentEquiv_smooth.{u, uV}
      a ha mu hG hi hnu b hb eta hds d hsm hK hPK I O
        (rationalSemistandardThetaComponent.{u, uV} a ha mu d
          (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds ⟨I, O⟩) f)),
    (by
      rw [rationalStandardFullRestrict_support]
      exact f.property.2.preimage' (fun t _ =>
        rationalStandardFullIndex_finite_fibers.{u, uV} a ha mu hG hi hnu b hb eta hds t))⟩
  map_add' f g := by
    apply Subtype.ext
    exact (rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds).map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    exact (rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds).map_smul c _

@[simp] theorem rationalStandardFullSmoothRestrict_val
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    (rationalStandardFullSmoothRestrict.{u, uV}
      a ha mu hG hi hnu b hb eta hds d hsm hK hPK f).val I O =
        rationalStandardFullComponentEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O
          (f.val (rationalStandardFullIndex.{u, uV}
            a ha mu hG hi hnu b hb eta hds ⟨I, O⟩)) := rfl

/-- Compatibility with the canonical finite-support standard restriction,
followed by the actual orbit and component comparison. -/
theorem rationalStandardFullSmoothRestrict_canonical
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (I : Finset (RationalPointFamily.SimpleRoot i nu))
    (O : RationalLeviOrbitClass.{u, uV} b hb eta I) :
    (rationalStandardFullSmoothRestrict.{u, uV}
      a ha mu hG hi hnu b hb eta hds d hsm hK hPK f).val I O =
        rationalStandardFullComponentEquiv.{u, uV} a ha mu hG hi hnu b hb eta hds I O
          ((rationalSemistandardStandardSmoothRestrict.{u, uV}
            a ha mu d hG hi hnu f).val
              ⟨I, rationalStandardFullOrbitEquiv.{u, uV}
                a ha mu hG hi hnu b hb eta hds I O⟩) := rfl

theorem rationalStandardFullSmoothRestrict_support
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    {t : RationalStandardTheta.{u, uV} b hb eta |
      (rationalStandardFullSmoothRestrict.{u, uV}
        a ha mu hG hi hnu b hb eta hds d hsm hK hPK f).val t.1 t.2 ≠ 0} =
      (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds) ⁻¹'
        rationalSemistandardThetaSupport.{u, uV} a ha mu f.val :=
  rationalStandardFullRestrict_support.{u, uV} a ha mu hG hi hnu b hb eta hds f.val

end StandardComparison

end Langlands.HarishChandraSchwartz
