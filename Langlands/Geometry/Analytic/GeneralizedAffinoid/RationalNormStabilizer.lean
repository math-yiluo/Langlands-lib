import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAutomorphism
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open stabilizers of weighted rational loci from norm-continuous orbits -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Filter
open scoped Topology Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The actual coefficient class of the displayed rational denominator. -/
abbrev denominatorClass (d : RationalChart K A) : A :=
  presentationMap K A d.denominator

/-- The actual coefficient classes of the displayed rational numerators. -/
abbrev numeratorClass (d : RationalChart K A) (j : Fin d.arity) : A :=
  presentationMap K A (d.numerators j)

/-- Compactness and unit generation give a positive denominator bound,
also when the weighted rational locus is empty. -/
theorem exists_pos_le_denominator (d : RationalChart K A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ d.locus, ε ≤ x d.denominatorClass := by
  apply (RationalPresentation.isCompact_locus K A d.radii d.denominator d.numerators).exists_forall_le'
    (BanachSpectrum.evaluation d.denominatorClass).continuous.continuousOn
  intro x hx
  exact lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
    (RationalPresentation.denominator_ne_zero K A d.radii d.denominator d.numerators
      d.generates x hx).symm

/-- Denominator displacement is measured against `ε`; numerator `j`
displacement is measured against the actual positive radius times `ε`. -/
theorem comap_mem_locus_of_displacement_lt (d : RationalChart K A) {ε : ℝ}
    (hε : ∀ x ∈ d.locus, ε ≤ x d.denominatorClass)
    (φ : BoundedAlgHom K A A)
    (hb : ‖φ.toAlgHom d.denominatorClass - d.denominatorClass‖ < ε)
    (hf : ∀ j, ‖φ.toAlgHom (d.numeratorClass j) - d.numeratorClass j‖ < d.radii j * ε)
    {x : BanachSpectrum A} (hx : x ∈ d.locus) :
    BanachSpectrum.comap φ.toBoundedRingHom x ∈ d.locus := by
  have hsmall : x.toMulRingSeminorm (φ.toAlgHom d.denominatorClass - d.denominatorClass) <
      x.toMulRingSeminorm d.denominatorClass :=
    (x.le_norm _).trans_lt (hb.trans_le (hε x hx))
  have heq : x (φ.toAlgHom d.denominatorClass) = x d.denominatorClass := by
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K)).add_eq_right_of_lt
        (map_neg_eq_map x.toMulRingSeminorm) hsmall
  intro j
  change x (φ.toAlgHom (d.numeratorClass j)) ≤
    d.radii j * x (φ.toAlgHom d.denominatorClass)
  rw [heq]
  have hnum := x.isNonarchimedean (K := K)
    (φ.toAlgHom (d.numeratorClass j) - d.numeratorClass j) (d.numeratorClass j)
  simpa only [sub_add_cancel] using hnum.trans
    (max_le ((x.le_norm _).trans ((hf j).le.trans
      (mul_le_mul_of_nonneg_left (hε x hx) (d.radii.positive j).le))) (hx j))

/-- Both actual algebra maps close to the identity preserve the exact
weighted rational subset under inverse seminorm pullback. -/
theorem locus_image_eq_of_displacement_lt (d : RationalChart K A) {ε : ℝ}
    (hε : ∀ x ∈ d.locus, ε ≤ x d.denominatorClass) (g : Aut A)
    (hb : ‖g.hom.toAlgHom d.denominatorClass - d.denominatorClass‖ < ε)
    (hf : ∀ j, ‖g.hom.toAlgHom (d.numeratorClass j) - d.numeratorClass j‖ < d.radii j * ε)
    (hib : ‖g.inv.toAlgHom d.denominatorClass - d.denominatorClass‖ < ε)
    (hif : ∀ j, ‖g.inv.toAlgHom (d.numeratorClass j) - d.numeratorClass j‖ < d.radii j * ε) :
    (fun x : BanachSpectrum A => g • x) '' d.locus = d.locus := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact comap_mem_locus_of_displacement_lt d hε g.inv hib hif hx
  · intro x hx
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    exact comap_mem_locus_of_displacement_lt d hε g.hom hb hf hx

/-- The full setwise stabilizer of the actual weighted rational locus. -/
def locusStabilizer (d : RationalChart K A) : Subgroup (Aut A) :=
  MulAction.stabilizer (Aut A) d.locus

@[simp]
theorem mem_locusStabilizer (d : RationalChart K A) (g : Aut A) :
    g ∈ d.locusStabilizer ↔
      (fun x : BanachSpectrum A => g • x) '' d.locus = d.locus := Iff.rfl

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

include hρ in
/-- Norm-continuous forward algebra orbits derive openness of the full
weighted rational-locus stabilizer in the original parameter group. -/
theorem isOpen_locusStabilizer (d : RationalChart K A) :
    IsOpen ((d.locusStabilizer.comap ρ : Subgroup G) : Set G) := by
  obtain ⟨ε, hε, hbound⟩ := d.exists_pos_le_denominator
  have hf (a : A) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ g in 𝓝 (1 : G), ‖(ρ g).hom.toAlgHom a - a‖ < δ := by
    have hc : Continuous (fun g : G => ‖(ρ g).hom.toAlgHom a - a‖) :=
      ((hρ a).sub continuous_const).norm
    have hz : ‖(ρ (1 : G)).hom.toAlgHom a - a‖ < δ := by
      rw [map_one]
      change ‖a - a‖ < δ
      simpa only [sub_self, norm_zero] using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds hz)
  have hi (a : A) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ g in 𝓝 (1 : G), ‖(ρ g).inv.toAlgHom a - a‖ < δ := by
    have horbit : Continuous (fun g : G => (ρ g).inv.toAlgHom a) := by
      apply ((hρ a).comp continuous_inv).congr
      intro g
      change (ρ (g⁻¹)).hom.toAlgHom a = (ρ g).inv.toAlgHom a
      rw [map_inv]
      rfl
    have hc : Continuous (fun g : G => ‖(ρ g).inv.toAlgHom a - a‖) :=
      (horbit.sub continuous_const).norm
    have hz : ‖(ρ (1 : G)).inv.toAlgHom a - a‖ < δ := by
      rw [map_one]
      change ‖a - a‖ < δ
      simpa only [sub_self, norm_zero] using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds hz)
  apply Subgroup.isOpen_of_mem_nhds
  filter_upwards [hf d.denominatorClass ε hε,
    Filter.eventually_all.mpr (fun j => hf (d.numeratorClass j) (d.radii j * ε)
      (mul_pos (d.radii.positive j) hε)),
    hi d.denominatorClass ε hε,
    Filter.eventually_all.mpr (fun j => hi (d.numeratorClass j) (d.radii j * ε)
      (mul_pos (d.radii.positive j) hε))] with g hb hnum hib hinum
  exact locus_image_eq_of_displacement_lt d hbound (ρ g) hb hnum hib hinum

/-- Bundle the derived full stabilizer as an open subgroup of `G`. -/
def normOpenStabilizer (d : RationalChart K A) : OpenSubgroup G :=
  ⟨d.locusStabilizer.comap ρ, isOpen_locusStabilizer ρ hρ d⟩

@[simp]
theorem mem_normOpenStabilizer (d : RationalChart K A) (g : G) :
    g ∈ normOpenStabilizer ρ hρ d ↔
      (fun x : BanachSpectrum A => (ρ g) • x) '' d.locus = d.locus := Iff.rfl

/-- Intersect the prescribed open subgroup with the full stabilizers of a
finite collection of actual weighted rational charts. -/
def finiteNormOpenStabilizer (s : Finset (RationalChart K A)) (U : OpenSubgroup G) :
    OpenSubgroup G :=
  U ⊓ OpenSubgroup.iInfOfFinite (fun d : s => normOpenStabilizer ρ hρ d.val)

@[simp]
theorem mem_finiteNormOpenStabilizer (s : Finset (RationalChart K A))
    (U : OpenSubgroup G) (g : G) :
    g ∈ finiteNormOpenStabilizer ρ hρ s U ↔
      g ∈ U ∧ ∀ d ∈ s, (fun x : BanachSpectrum A => (ρ g) • x) '' d.locus = d.locus := by
  change (g ∈ U ∧ g ∈ (⨅ d : s, (normOpenStabilizer ρ hρ d.val).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf, Subtype.forall]
  rfl

theorem finiteNormOpenStabilizer_le (s : Finset (RationalChart K A)) (U : OpenSubgroup G) :
    finiteNormOpenStabilizer ρ hρ s U ≤ U := inf_le_left

/-- Adding rational loci and shrinking the prescribed subgroup coherently
shrinks the resulting simultaneous open stabilizer. -/
theorem finiteNormOpenStabilizer_mono {s t : Finset (RationalChart K A)}
    (hst : s ⊆ t) {U V : OpenSubgroup G} (hUV : U ≤ V) :
    finiteNormOpenStabilizer ρ hρ t U ≤ finiteNormOpenStabilizer ρ hρ s V := by
  intro g hg
  obtain ⟨hU, ht⟩ := (mem_finiteNormOpenStabilizer ρ hρ t U g).mp hg
  exact (mem_finiteNormOpenStabilizer ρ hρ s V g).mpr
    ⟨hUV hU, fun d hd => ht d (hst hd)⟩

variable [CompleteSpace K]

/-- The rational-chart stabilizer is exactly that of its constructed full
represented domain, with no assumed domain-spectral continuity. -/
theorem locusStabilizer_toDomain (d : RationalChart K A) :
    DomainAutomorphism.locusStabilizer d.toDomain = d.locusStabilizer := rfl

/-- Map the derived open subgroup into the actual represented-domain
stabilizer, retaining the original bounded algebra automorphisms. -/
def normStabilizerHom (d : RationalChart K A) :
    normOpenStabilizer ρ hρ d →* DomainAutomorphism.locusStabilizer d.toDomain where
  toFun g := ⟨ρ g.val, g.property⟩
  map_one' := Subtype.ext (map_one ρ)
  map_mul' g h := Subtype.ext (map_mul ρ g.val h.val)

/-- The derived open stabilizer acts by actual bounded automorphisms on the
entire represented rational-domain algebra. -/
def normSectionAction (d : RationalChart K A) :
    normOpenStabilizer ρ hρ d →* Aut d.algebra :=
  (DomainAutomorphism.stabilizerSectionAction d.toDomain).comp (normStabilizerHom ρ hρ d)

@[simp]
theorem normSectionAction_baseMap (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) (a : A) :
    (normSectionAction ρ hρ d g).hom.toAlgHom (d.baseMap a) =
      d.baseMap ((ρ g.val).hom.toAlgHom a) :=
  DomainAutomorphism.stabilizerSectionAction_baseMap d.toDomain (normStabilizerHom ρ hρ d g) a

/-- Local bounded section operators commute with actual chart restrictions
when the same parameter preserves both rational loci. -/
theorem normSectionAction_restriction {d e : RationalChart K A} (f : d ⟶ e)
    (g : G) (hd : g ∈ normOpenStabilizer ρ hρ d)
    (he : g ∈ normOpenStabilizer ρ hρ e) :
    ((normSectionAction ρ hρ d ⟨g, hd⟩).hom).comp f.restriction =
      f.restriction.comp (normSectionAction ρ hρ e ⟨g, he⟩).hom :=
  DomainAutomorphism.stabilizerSectionMap_restriction
    ((toDomainFunctor K A).map f) (ρ g) hd he

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
