import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactCharts

/-! # Bounded coordinate changes between induced rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable (X : ρ.OpenSubgroupTransport)

/-- Equal left-coset labels give the same actual chart domain. -/
theorem inducedChartDomain_eq_of_coset_eq (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    X.inducedChartDomain a = X.inducedChartDomain b := by
  apply TopologicalSpace.Opens.ext
  change Set.range (X.inducedChart a) = Set.range (X.inducedChart b)
  rw [X.range_inducedChart_eq_fiber, X.range_inducedChart_eq_fiber, hab]

/-- Different labels have disjoint actual chart domains, including empty spectra. -/
theorem disjoint_inducedChartDomain_of_coset_ne (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) ≠ b) :
    Disjoint (X.inducedChartDomain a : Set X.InducedSpectrum)
      (X.inducedChartDomain b : Set X.InducedSpectrum) := by
  apply Set.disjoint_left.mpr
  intro z ha hb
  apply hab
  exact ((X.mem_inducedChartDomain_iff a z).mp ha).symm.trans
    ((X.mem_inducedChartDomain_iff b z).mp hb)

/-- A point in two charts determines equality of their coset labels. -/
theorem coset_eq_of_mem_inducedChartDomains (a b : G) (z : X.InducedSpectrum)
    (ha : z ∈ X.inducedChartDomain a) (hb : z ∈ X.inducedChartDomain b) :
    (a : G ⧸ X.subgroup.toSubgroup) = b :=
  ((X.mem_inducedChartDomain_iff a z).mp ha).symm.trans
    ((X.mem_inducedChartDomain_iff b z).mp hb)

/-- Nonempty overlap also records the necessary nonemptiness of the local spectrum. -/
theorem nonempty_inter_inducedChartDomains_iff (a b : G) :
    ((X.inducedChartDomain a : Set X.InducedSpectrum) ∩
      (X.inducedChartDomain b : Set X.InducedSpectrum)).Nonempty ↔
      (a : G ⧸ X.subgroup.toSubgroup) = b ∧ Nonempty X.LocalSpectrum := by
  constructor
  · rintro ⟨z, ha, hb⟩
    refine ⟨X.coset_eq_of_mem_inducedChartDomains a b z ha hb, ?_⟩
    obtain ⟨x, _⟩ := ha
    exact ⟨x⟩
  · rintro ⟨hab, ⟨x⟩⟩
    refine ⟨X.inducedChart a x, ⟨x, rfl⟩, ?_⟩
    rw [← X.inducedChartDomain_eq_of_coset_eq a b hab]
    exact ⟨x, rfl⟩

/-- The uniquely determined subgroup element relating two coset representatives. -/
def chartChangeElement (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) : X.subgroup :=
  ⟨a⁻¹ * b, QuotientGroup.eq.mp hab⟩

@[simp]
theorem chartChangeElement_coe (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    (X.chartChangeElement a b hab : G) = a⁻¹ * b := rfl

@[simp]
theorem chartChangeElement_refl (a : G) :
    X.chartChangeElement a a rfl = 1 := by
  apply Subtype.ext
  simp

theorem chartChangeElement_symm (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    X.chartChangeElement b a hab.symm = (X.chartChangeElement a b hab)⁻¹ := by
  apply Subtype.ext
  simp

theorem chartChangeElement_trans (a b c : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b)
    (hbc : (b : G ⧸ X.subgroup.toSubgroup) = c) :
    X.chartChangeElement a c (hab.trans hbc) =
      X.chartChangeElement a b hab * X.chartChangeElement b c hbc := by
  apply Subtype.ext
  simp [mul_assoc]

/-- The already constructed bounded section action restricted to the stored subgroup. -/
def chartSectionAction : X.subgroup →* Aut X.domain.obj.algebra :=
  (ρ.sectionAction X.domain.obj).comp
    (ρ.invariantStabilizerInclusion X.subgroup X.domain).toMonoidHom

theorem chartSectionAction_comp_baseMap (h : X.subgroup) :
    (X.chartSectionAction h).hom.comp X.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (h : G)).hom :=
  ρ.sectionAction_comp_baseMap X.domain.obj
    (ρ.invariantStabilizerInclusion X.subgroup X.domain h)

/-- Pullback from chart a to chart b is inverse to the forward section operator. -/
def chartAlgebraChange (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) : Aut X.domain.obj.algebra :=
  (X.chartSectionAction (X.chartChangeElement a b hab))⁻¹

/-- Both directions retain their actual bounded algebra maps. -/
def chartBoundedChange (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    BoundedAlgEquiv K X.domain.obj.algebra X.domain.obj.algebra :=
  boundedEquiv (X.chartAlgebraChange a b hab)

theorem chartAlgebraChange_comp_baseMap (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    (X.chartAlgebraChange a b hab).hom.comp X.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (a⁻¹ * b)).inv := by
  have h := X.chartSectionAction_comp_baseMap (X.chartChangeElement a b hab)⁻¹
  simpa only [chartAlgebraChange, map_inv, InvMemClass.coe_inv, chartChangeElement_coe,
    Aut.Aut_inv_def, Iso.symm] using h

/-- Rational extension uniqueness determines the bounded coordinate pullback from its base map. -/
theorem chartAlgebraChange_unique (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b)
    (f : BoundedAlgHom K X.domain.obj.algebra X.domain.obj.algebra)
    (hf : f.comp X.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (a⁻¹ * b)).inv) :
    f = (X.chartAlgebraChange a b hab).hom := by
  apply X.domain.obj.hom_ext
  exact hf.trans (X.chartAlgebraChange_comp_baseMap a b hab).symm

@[simp]
theorem chartAlgebraChange_refl (a : G) : X.chartAlgebraChange a a rfl = 1 := by
  simp [chartAlgebraChange]

theorem chartAlgebraChange_symm (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    X.chartAlgebraChange b a hab.symm = (X.chartAlgebraChange a b hab)⁻¹ := by
  simp [chartAlgebraChange, X.chartChangeElement_symm a b hab]

/-- Algebra pullbacks compose in the reverse order to point-coordinate changes. -/
theorem chartAlgebraChange_trans (a b c : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b)
    (hbc : (b : G ⧸ X.subgroup.toSubgroup) = c) :
    X.chartAlgebraChange a c (hab.trans hbc) =
      X.chartAlgebraChange b c hbc * X.chartAlgebraChange a b hab := by
  simp [chartAlgebraChange, X.chartChangeElement_trans a b c hab hbc, mul_inv_rev]

theorem chartAlgebraChange_hom_trans (a b c : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b)
    (hbc : (b : G ⧸ X.subgroup.toSubgroup) = c) :
    (X.chartAlgebraChange a c (hab.trans hbc)).hom =
      (X.chartAlgebraChange b c hbc).hom.comp (X.chartAlgebraChange a b hab).hom := by
  rw [X.chartAlgebraChange_trans a b c hab hbc]
  rfl

/-- The spectrum homeomorphism of the constructed bounded coordinate pullback. -/
def chartCoordinateChange (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) :
    X.LocalSpectrum ≃ₜ X.LocalSpectrum :=
  (X.chartBoundedChange a b hab).spectrumHomeomorph

@[simp]
theorem chartCoordinateChange_apply (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) (x : X.LocalSpectrum) :
    X.chartCoordinateChange a b hab x = X.chartChangeElement a b hab • x := rfl

/-- The algebraic spectrum map is exactly the change from b-coordinates to a-coordinates. -/
theorem inducedChart_chartCoordinateChange (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) (x : X.LocalSpectrum) :
    X.inducedChart a (X.chartCoordinateChange a b hab x) = X.inducedChart b x := by
  rw [chartCoordinateChange_apply]
  simpa using (X.inducedChart_mul_subgroup a (X.chartChangeElement a b hab) x).symm

/-- Chart injectivity uniquely determines the corresponding point-coordinate change. -/
theorem chartCoordinateChange_unique (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) (x y : X.LocalSpectrum)
    (hy : X.inducedChart a y = X.inducedChart b x) :
    y = X.chartCoordinateChange a b hab x :=
  (X.isOpenEmbedding_inducedChart a).injective
    (hy.trans (X.inducedChart_chartCoordinateChange a b hab x).symm)

@[simp]
theorem chartCoordinateChange_refl (a : G) (x : X.LocalSpectrum) :
    X.chartCoordinateChange a a rfl x = x := by
  simp

theorem chartCoordinateChange_symm (a b : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b) (x : X.LocalSpectrum) :
    X.chartCoordinateChange b a hab.symm (X.chartCoordinateChange a b hab x) = x := by
  simp [X.chartChangeElement_symm a b hab]

theorem chartCoordinateChange_trans (a b c : G)
    (hab : (a : G ⧸ X.subgroup.toSubgroup) = b)
    (hbc : (b : G ⧸ X.subgroup.toSubgroup) = c) (x : X.LocalSpectrum) :
    X.chartCoordinateChange a c (hab.trans hbc) x =
      X.chartCoordinateChange a b hab (X.chartCoordinateChange b c hbc x) := by
  simp [X.chartChangeElement_trans a b c hab hbc, mul_smul]

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
