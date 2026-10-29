import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalChartChanges

/-! # Bounded transport in compatible induced rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport.Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

private theorem ambientInv_comp (r s : G) :
    (ρ.toMonoidHom r).inv.comp (ρ.toMonoidHom s).inv =
      (ρ.toMonoidHom (s * r)).inv := by
  rw [map_mul]
  rfl

/-- The actual bounded pullback in any target chart with the correct coset label. -/
def chartPullback (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G)) :
    BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra :=
  f.restriction.comp (Y.chartAlgebraChange b (a * f.label⁻¹) hab).hom

theorem chartPullback_comp_baseMap (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G)) :
    (f.chartPullback a b hab).comp Y.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (b⁻¹ * a)).inv := by
  unfold chartPullback
  rw [BoundedAlgHom.comp_assoc, Y.chartAlgebraChange_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, f.restriction_comp_baseMap,
    BoundedAlgHom.comp_assoc, ambientInv_comp]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The base triangle determines the bounded pullback by rational extension uniqueness. -/
theorem chartPullback_unique (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (φ : BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra)
    (hφ : φ.comp Y.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (b⁻¹ * a)).inv) :
    φ = f.chartPullback a b hab := by
  apply Y.domain.obj.hom_ext
  exact hφ.trans (f.chartPullback_comp_baseMap a b hab).symm

/-- The actual continuous spectrum map of the constructed bounded chart pullback. -/
def chartSpectrumMap (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G)) :
    C(X.LocalSpectrum, Y.LocalSpectrum) :=
  BanachSpectrum.comapContinuous (f.chartPullback a b hab).toBoundedRingHom

theorem chartSpectrumMap_apply (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (x : X.LocalSpectrum) :
    f.chartSpectrumMap a b hab x =
      Y.chartCoordinateChange b (a * f.label⁻¹) hab (f.localSpectrumMap x) := rfl

/-- The algebraic spectrum map realizes transport between the actual quotient charts. -/
theorem inducedChart_chartSpectrumMap (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (x : X.LocalSpectrum) :
    Y.inducedChart b (f.chartSpectrumMap a b hab x) =
      f.inducedMap (X.inducedChart a x) := by
  rw [chartSpectrumMap_apply, Y.inducedChart_chartCoordinateChange, f.inducedMap_chart]

theorem chartSpectrumMap_unique (f : X ⟶ Y) (a b : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (x : X.LocalSpectrum) (y : Y.LocalSpectrum)
    (hy : Y.inducedChart b y = f.inducedMap (X.inducedChart a x)) :
    y = f.chartSpectrumMap a b hab x :=
  (Y.isOpenEmbedding_inducedChart b).injective
    (hy.trans (f.inducedChart_chartSpectrumMap a b hab x).symm)

/-- In the unadjusted target chart, the pullback is the published rational restriction. -/
@[simp]
theorem chartPullback_canonical (f : X ⟶ Y) (a : G) :
    f.chartPullback a (a * f.label⁻¹) rfl = f.restriction := by
  simp [chartPullback]
  rfl

@[simp]
theorem chartSpectrumMap_canonical (f : X ⟶ Y) (a : G) (x : X.LocalSpectrum) :
    f.chartSpectrumMap a (a * f.label⁻¹) rfl x = f.localSpectrumMap x := by
  rw [chartSpectrumMap_apply, Y.chartCoordinateChange_refl]

@[simp]
theorem chartPullback_id (X : ρ.OpenSubgroupTransport) (a : G) :
    (𝟙 X : X ⟶ X).chartPullback a a (by simp) =
      BoundedAlgHom.id K X.domain.obj.algebra := by
  apply ((𝟙 X : X ⟶ X).chartPullback_unique a a (by simp) _ ?_).symm
  rw [inv_mul_cancel, map_one]
  rfl

@[simp]
theorem chartSpectrumMap_id (X : ρ.OpenSubgroupTransport) (a : G)
    (x : X.LocalSpectrum) :
    (𝟙 X : X ⟶ X).chartSpectrumMap a a (by simp) x = x := by
  apply ((𝟙 X : X ⟶ X).chartSpectrumMap_unique a a (by simp) x x ?_).symm
  simp

/-- Compatible source and intermediate labels give a compatible composite label. -/
theorem chartCoset_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a b c : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (hbc : (c : G ⧸ Z.subgroup.toSubgroup) = (b * g.label⁻¹ : G)) :
    (c : G ⧸ Z.subgroup.toSubgroup) = (a * (f ≫ g).label⁻¹ : G) := by
  calc
    _ = g.cosetMap (b : G ⧸ Y.subgroup.toSubgroup) := hbc
    _ = g.cosetMap (a * f.label⁻¹ : G ⧸ Y.subgroup.toSubgroup) :=
      congrArg g.cosetMap hab
    _ = _ := by simp only [cosetMap_mk, comp_label, mul_inv_rev, mul_assoc]

/-- The actual bounded maps compose contravariantly in any compatible charts. -/
theorem chartPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a b c : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (hbc : (c : G ⧸ Z.subgroup.toSubgroup) = (b * g.label⁻¹ : G))
    (hac : (c : G ⧸ Z.subgroup.toSubgroup) = (a * (f ≫ g).label⁻¹ : G)) :
    (f ≫ g).chartPullback a c hac =
      (f.chartPullback a b hab).comp (g.chartPullback b c hbc) := by
  apply ((f ≫ g).chartPullback_unique a c hac _ ?_).symm
  rw [BoundedAlgHom.comp_assoc, g.chartPullback_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, f.chartPullback_comp_baseMap,
    BoundedAlgHom.comp_assoc, ambientInv_comp]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem chartSpectrumMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a b c : G)
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (hbc : (c : G ⧸ Z.subgroup.toSubgroup) = (b * g.label⁻¹ : G))
    (hac : (c : G ⧸ Z.subgroup.toSubgroup) = (a * (f ≫ g).label⁻¹ : G))
    (x : X.LocalSpectrum) :
    (f ≫ g).chartSpectrumMap a c hac x =
      g.chartSpectrumMap b c hbc (f.chartSpectrumMap a b hab x) := by
  apply (Z.isOpenEmbedding_inducedChart c).injective
  simp only [inducedChart_chartSpectrumMap, inducedMap_comp]

/-- Changing both representatives preserves compatibility of the chart labels. -/
theorem chartCoset_change (f : X ⟶ Y) (a a' b b' : G)
    (ha : (a : G ⧸ X.subgroup.toSubgroup) = a')
    (hb : (b : G ⧸ Y.subgroup.toSubgroup) = b')
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G)) :
    (b' : G ⧸ Y.subgroup.toSubgroup) = (a' * f.label⁻¹ : G) := by
  calc
    _ = (b : G ⧸ Y.subgroup.toSubgroup) := hb.symm
    _ = (a * f.label⁻¹ : G ⧸ Y.subgroup.toSubgroup) := hab
    _ = _ := congrArg f.cosetMap ha

/-- The bounded pullbacks commute with actual source and target chart changes. -/
theorem chartPullback_naturality (f : X ⟶ Y) (a a' b b' : G)
    (ha : (a : G ⧸ X.subgroup.toSubgroup) = a')
    (hb : (b : G ⧸ Y.subgroup.toSubgroup) = b')
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (hab' : (b' : G ⧸ Y.subgroup.toSubgroup) = (a' * f.label⁻¹ : G)) :
    (X.chartAlgebraChange a a' ha).hom.comp (f.chartPullback a b hab) =
      (f.chartPullback a' b' hab').comp (Y.chartAlgebraChange b b' hb).hom := by
  apply Y.domain.obj.hom_ext
  conv_lhs =>
    rw [BoundedAlgHom.comp_assoc, f.chartPullback_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, X.chartAlgebraChange_comp_baseMap,
      BoundedAlgHom.comp_assoc, ambientInv_comp]
  conv_rhs =>
    rw [BoundedAlgHom.comp_assoc, Y.chartAlgebraChange_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, f.chartPullback_comp_baseMap,
      BoundedAlgHom.comp_assoc, ambientInv_comp]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem chartSpectrumMap_naturality (f : X ⟶ Y) (a a' b b' : G)
    (ha : (a : G ⧸ X.subgroup.toSubgroup) = a')
    (hb : (b : G ⧸ Y.subgroup.toSubgroup) = b')
    (hab : (b : G ⧸ Y.subgroup.toSubgroup) = (a * f.label⁻¹ : G))
    (hab' : (b' : G ⧸ Y.subgroup.toSubgroup) = (a' * f.label⁻¹ : G))
    (x : X.LocalSpectrum) :
    f.chartSpectrumMap a b hab (X.chartCoordinateChange a a' ha x) =
      Y.chartCoordinateChange b b' hb (f.chartSpectrumMap a' b' hab' x) := by
  apply (Y.isOpenEmbedding_inducedChart b).injective
  rw [inducedChart_chartSpectrumMap, X.inducedChart_chartCoordinateChange,
    Y.inducedChart_chartCoordinateChange, inducedChart_chartSpectrumMap]

/-- Quotient representatives give compatible charts without a supplied subgroup element. -/
theorem cosetChart_compatible (f : X ⟶ Y) (c : G ⧸ X.subgroup.toSubgroup) :
    ((f.cosetMap c).out : G ⧸ Y.subgroup.toSubgroup) = (c.out * f.label⁻¹ : G) := by
  calc
    _ = f.cosetMap c := Quotient.out_eq _
    _ = f.cosetMap (c.out : G ⧸ X.subgroup.toSubgroup) :=
      congrArg f.cosetMap (Quotient.out_eq c).symm
    _ = _ := rfl

/-- The actual bounded pullback for the quotient's chosen source and target representatives. -/
def cosetChartPullback (f : X ⟶ Y) (c : G ⧸ X.subgroup.toSubgroup) :
    BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra :=
  f.chartPullback c.out (f.cosetMap c).out (f.cosetChart_compatible c)

theorem cosetChartPullback_comp_baseMap (f : X ⟶ Y)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (f.cosetChartPullback c).comp Y.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom ((f.cosetMap c).out⁻¹ * c.out)).inv :=
  f.chartPullback_comp_baseMap c.out (f.cosetMap c).out (f.cosetChart_compatible c)

/-- The continuous spectrum map of the bounded pullback in chosen coset coordinates. -/
def cosetChartSpectrumMap (f : X ⟶ Y) (c : G ⧸ X.subgroup.toSubgroup) :
    C(X.LocalSpectrum, Y.LocalSpectrum) :=
  f.chartSpectrumMap c.out (f.cosetMap c).out (f.cosetChart_compatible c)

/-- Exact coset-copy coordinates, with their actual bounded algebra pullback constructed. -/
theorem inducedCoordinates_apply (f : X ⟶ Y) (c : G ⧸ X.subgroup.toSubgroup)
    (x : X.LocalSpectrum) :
    f.inducedCoordinates ⟨c, x⟩ = ⟨f.cosetMap c, f.cosetChartSpectrumMap c x⟩ := by
  apply Y.inducedCosetHomeomorph.injective
  rw [inducedCosetHomeomorph_inducedCoordinates, inducedCosetHomeomorph_apply,
    inducedCosetHomeomorph_apply]
  exact (f.inducedChart_chartSpectrumMap c.out (f.cosetMap c).out
    (f.cosetChart_compatible c) x).symm

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
