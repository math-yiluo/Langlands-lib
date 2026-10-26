import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Transport of rational spectral tests by bounded automorphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory BanachSpectrum
open scoped Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Conjugation identifies the stabilizers of the original and moved loci. -/
def stabilizerConj (g : Aut P) (d : RationalData K P) :
    locusStabilizer d ≃* locusStabilizer (g • d) :=
  MulAction.stabilizerEquivStabilizer (locus_smul g d)

@[simp] theorem stabilizerConj_coe (g : Aut P) (d : RationalData K P)
    (h : locusStabilizer d) :
    (stabilizerConj g d h : Aut P) = g * (h : Aut P) * g⁻¹ :=
  MulAction.stabilizerEquivStabilizer_apply (locus_smul g d) h

/-- The moved locus stabilizer is the conjugate subgroup. -/
theorem locusStabilizer_smul (g : Aut P) (d : RationalData K P) :
    locusStabilizer (g • d) = (locusStabilizer d).map (MulAut.conj g).toMonoidHom := by
  change MulAction.stabilizer (Aut P) (g • d).locus = _
  rw [locus_smul]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g d.locus

theorem conj_mem_locusStabilizer_iff (g h : Aut P) (d : RationalData K P) :
    g * h * g⁻¹ ∈ locusStabilizer (g • d) ↔ h ∈ locusStabilizer d := by
  rw [locusStabilizer_smul]
  exact Subgroup.mem_map_iff_mem (MulAut.conj g).injective

variable [CompleteSpace K]

/-- The transported fixed-quotient action is intertwined by the actual bounded
comparison map. -/
theorem stabilizerSectionMap_comparison (g : Aut P) (d : RationalData K P)
    (h : locusStabilizer d) :
    (stabilizerSectionMap (g • d) (stabilizerConj g d h)).comp (d.comparison g.hom) =
      (d.comparison g.hom).comp (stabilizerSectionMap d h) := by
  apply d.hom_ext
  calc
    _ = (stabilizerSectionMap (g • d) (stabilizerConj g d h)).comp
        ((g • d).baseMap.comp g.hom) := by
      rw [BoundedAlgHom.comp_assoc, d.comparison_comp_baseMap]
      rfl
    _ = ((g • d).baseMap.comp
        (stabilizerConj g d h : Aut P).hom).comp g.hom := by
      rw [← BoundedAlgHom.comp_assoc, stabilizerSectionMap_comp_baseMap]
    _ = (g • d).baseMap.comp (g.hom.comp (h : Aut P).hom) := by
      rw [BoundedAlgHom.comp_assoc]
      apply congrArg ((g • d).baseMap.comp)
      rw [stabilizerConj_coe]
      ext a
      change g.hom.toAlgHom ((h : Aut P).hom.toAlgHom (g.inv.toAlgHom
        (g.hom.toAlgHom a))) = g.hom.toAlgHom ((h : Aut P).hom.toAlgHom a)
      have hinv : g.inv.toAlgHom (g.hom.toAlgHom a) = a :=
        congrArg (fun f : BoundedAlgHom K P P => f a) g.hom_inv_id
      rw [hinv]
    _ = ((d.comparison g.hom).comp (stabilizerSectionMap d h)).comp d.baseMap := by
      symm
      rw [BoundedAlgHom.comp_assoc, stabilizerSectionMap_comp_baseMap,
        ← BoundedAlgHom.comp_assoc, d.comparison_comp_baseMap,
        BoundedAlgHom.comp_assoc]
      rfl
omit [CompleteSpace K] in
private theorem spectralBound_iso_iff
    {A B : PresentedStrictAffinoidAlgebra K} (e : A ≅ B) (a : A) (r : ℝ) :
    SpectralBound (e.hom.toAlgHom a) r ↔ SpectralBound a r := by
  constructor
  · intro ha
    have hi := ha.map e.inv.toBoundedRingHom
    have heq : e.inv.toAlgHom (e.hom.toAlgHom a) = a :=
      congrArg (fun f : BoundedAlgHom K A A => f a) e.hom_inv_id
    exact heq ▸ hi
  · intro ha
    exact ha.map e.hom.toBoundedRingHom

/-- Spectral bounds are preserved and reflected by the actual quotient
comparison for a bounded base automorphism. -/
theorem spectralBound_comparison_iff (g : Aut P) (d : RationalData K P)
    (b : d.algebra) (r : ℝ) :
    SpectralBound (d.comparison g.hom b) r ↔ SpectralBound b r := by
  have h := spectralBound_iso_iff (d.comparisonIso (boundedEquiv g)) b r
  change SpectralBound (d.comparison (boundedEquiv g).toBoundedAlgHom b) r ↔
    SpectralBound b r at h
  rw [boundedEquiv_hom g] at h
  exact h

/-- Conjugation of the locus stabilizer transports the spectral displacement
condition on its fixed section algebra. -/
theorem stabilizerConj_mem_spectral_iff (g : Aut P) (d : RationalData K P)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) (h : locusStabilizer d) :
    stabilizerConj g d h ∈ stabilizerSpectralSubgroup (g • d)
      (d.comparison g.hom b) r hr ↔ h ∈ stabilizerSpectralSubgroup d b r hr := by
  change SpectralBound ((stabilizerSectionMap (g • d) (stabilizerConj g d h))
    (d.comparison g.hom b) - d.comparison g.hom b) r ↔
      SpectralBound (stabilizerSectionMap d h b - b) r
  have heq := congrArg (fun f : BoundedAlgHom K d.algebra (g • d).algebra => f b)
    (stabilizerSectionMap_comparison g d h)
  change stabilizerSectionMap (g • d) (stabilizerConj g d h) (d.comparison g.hom b) =
    d.comparison g.hom (stabilizerSectionMap d h b) at heq
  rw [heq, ← map_sub (d.comparison g.hom).toAlgHom]
  exact spectralBound_comparison_iff g d _ r

/-- An ambient automorphism passes the original test exactly when its
conjugate passes the transported test. -/
theorem conj_mem_rationalSpectralSubgroup_iff (g h : Aut P) (d : RationalData K P)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) :
    g * h * g⁻¹ ∈ rationalSpectralSubgroup (g • d) (d.comparison g.hom b) r hr ↔
      h ∈ rationalSpectralSubgroup d b r hr := by
  rw [mem_rationalSpectralSubgroup, mem_rationalSpectralSubgroup]
  constructor
  · rintro ⟨hh, hb⟩
    have hh' := (conj_mem_locusStabilizer_iff g h d).mp hh
    refine ⟨hh', ?_⟩
    apply (stabilizerConj_mem_spectral_iff g d b r hr ⟨h, hh'⟩).mp
    have heq : stabilizerConj g d ⟨h, hh'⟩ = ⟨g * h * g⁻¹, hh⟩ := by
      apply Subtype.ext
      exact stabilizerConj_coe g d ⟨h, hh'⟩
    rw [heq]
    exact hb
  · rintro ⟨hh, hb⟩
    have hh' := (conj_mem_locusStabilizer_iff g h d).mpr hh
    refine ⟨hh', ?_⟩
    have hbound := (stabilizerConj_mem_spectral_iff g d b r hr ⟨h, hh⟩).mpr hb
    have heq : stabilizerConj g d ⟨h, hh⟩ = ⟨g * h * g⁻¹, hh'⟩ := by
      apply Subtype.ext
      exact stabilizerConj_coe g d ⟨h, hh⟩
    rw [heq] at hbound
    exact hbound

/-- Move a rational test's actual quotient section and retain its tolerance. -/
def RationalSpectralTest.transport (g : Aut P) (t : RationalSpectralTest K P) :
    RationalSpectralTest K P where
  domain := g • t.domain
  element := t.domain.comparison g.hom t.element
  radius := t.radius
  radius_pos := t.radius_pos

/-- A single transported test gives precisely the conjugate subgroup. -/
theorem RationalSpectralTest.subgroup_transport (g : Aut P)
    (t : RationalSpectralTest K P) :
    rationalSpectralSubgroup (t.transport g).domain (t.transport g).element
      (t.transport g).radius (t.transport g).radius_pos.le =
      (rationalSpectralSubgroup t.domain t.element t.radius t.radius_pos.le).map
        (MulAut.conj g).toMonoidHom := by
  ext h
  obtain ⟨h, rfl⟩ := (MulAut.conj g).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  exact conj_mem_rationalSpectralSubgroup_iff g h t.domain t.element t.radius
    t.radius_pos.le

/-- The same conjugation law holds for every finite family, including the empty
family. The finite index has an independent universe. -/
theorem finiteRationalSpectralSubgroup_transport {ι : Type v} [Finite ι]
    (g : Aut P) (tests : ι → RationalSpectralTest K P) :
    finiteRationalSpectralSubgroup (fun i => (tests i).transport g) =
      (finiteRationalSpectralSubgroup tests).map (MulAut.conj g).toMonoidHom := by
  ext h
  obtain ⟨h, rfl⟩ := (MulAut.conj g).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [finiteRationalSpectralSubgroup, Subgroup.mem_iInf,
    RationalSpectralTest.transport]
  exact forall_congr' fun i => conj_mem_rationalSpectralSubgroup_iff g h
    (tests i).domain (tests i).element (tests i).radius (tests i).radius_pos.le

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
