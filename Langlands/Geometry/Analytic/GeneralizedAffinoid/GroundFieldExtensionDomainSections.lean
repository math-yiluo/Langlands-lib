import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionRationalSections
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering
import Langlands.Geometry.Analytic.Spectrum.JointContinuityProof

/-! # Semilinear section operators on represented affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open CategoryTheory Filter
open scoped Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (A : PresentedAffinoidAlgebra K)

private abbrev CoefficientGroup : Type v := ↥(isometricAutomorphisms K L)

local notation "B" => algebra K L A
local notation "Γ" => CoefficientGroup K L

variable {U : Domain L (algebra K L A)} (c : Domain.FiniteRationalCover U)

local notation "D" => c.toFiniteCover

/-- The common subgroup for the operators on the actual rational cover and
all of its pairwise rational intersections. -/
def domainCoverSectionSubgroup : Subgroup Γ :=
  (⨅ i : Fin c.size, rationalSectionIsometrySubgroup K L A (c.chart i)) ⊓
    (⨅ p : Fin c.size × Fin c.size,
      rationalSectionIsometrySubgroup K L A ((c.chart p.1).inter (c.chart p.2)))

local notation "H" => domainCoverSectionSubgroup K L A c

private theorem coverSectionSubgroup_le_chart (i : Fin c.size) :
    H ≤ rationalSectionIsometrySubgroup K L A (c.chart i) :=
  inf_le_left.trans (iInf_le _ i)

private theorem coverSectionSubgroup_le_inter (i j : Fin c.size) :
    H ≤ rationalSectionIsometrySubgroup K L A ((c.chart i).inter (c.chart j)) :=
  inf_le_right.trans (iInf_le _ (i, j))

private def sectionOnChart (σ : H) (i : Fin c.size) :
    BoundedRingHom (c.chart i).algebra (c.chart i).algebra :=
  rationalSectionMap K L A (c.chart i) H (coverSectionSubgroup_le_chart K L A c i) σ

private def sectionFamily (σ : H) (a : U.algebra) (i : Fin c.size) :
    (c.chart i).algebra :=
  sectionOnChart K L A c σ i ((c.map i).restriction a)

private theorem sectionFamily_agrees_on_inter (σ : H) (a : U.algebra)
    (i j : Fin c.size) :
    (RationalChart.interLeft (c.chart i) (c.chart j)).restriction
        (sectionFamily K L A c σ a i) =
      (RationalChart.interRight (c.chart i) (c.chart j)).restriction
        (sectionFamily K L A c σ a j) := by
  let d := (c.chart i).inter (c.chart j)
  let F := RationalChart.toDomainFunctor L B
  let p := F.map (RationalChart.interLeft (c.chart i) (c.chart j))
  let q := F.map (RationalChart.interRight (c.chart i) (c.chart j))
  let α := rationalSectionMap K L A d H (coverSectionSubgroup_le_inter K L A c i j) σ
  have h₁ : p.restriction.toBoundedRingHom.comp (sectionOnChart K L A c σ i) =
      α.comp p.restriction.toBoundedRingHom :=
    rationalSectionMap_restriction K L A d H (coverSectionSubgroup_le_inter K L A c i j)
      p (coverSectionSubgroup_le_chart K L A c i) σ
  have h₂ : q.restriction.toBoundedRingHom.comp (sectionOnChart K L A c σ j) =
      α.comp q.restriction.toBoundedRingHom :=
    rationalSectionMap_restriction K L A d H (coverSectionSubgroup_le_inter K L A c i j)
      q (coverSectionSubgroup_le_chart K L A c j) σ
  change (p.restriction.toBoundedRingHom.comp (sectionOnChart K L A c σ i))
      ((c.map i).restriction a) =
    (q.restriction.toBoundedRingHom.comp (sectionOnChart K L A c σ j))
      ((c.map j).restriction a)
  rw [h₁, h₂]
  exact congrArg (fun f : Domain.Inclusion d.toDomain U => α (f.restriction a))
    (@Subsingleton.elim (Domain.Inclusion d.toDomain U) inferInstance
      (p ≫ c.map i) (q ≫ c.map j))

private theorem sectionFamily_compatible (σ : H) (a : U.algebra) :
    (D).AlgebraCompatible (sectionFamily K L A c σ a) := by
  intro i j W f g
  change Fin c.size at i j
  let d := (c.chart i).inter (c.chart j)
  let F := RationalChart.toDomainFunctor L B
  let p := F.map (RationalChart.interLeft (c.chart i) (c.chart j))
  let q := F.map (RationalChart.interRight (c.chart i) (c.chart j))
  let r : W ⟶ d.toDomain := Domain.inclusionOfSubset W d.toDomain (by
    rw [RationalChart.toDomain_locus, RationalChart.locus_inter]
    exact fun _ hx => ⟨f.subset hx, g.subset hx⟩)
  have hf : r ≫ p = f :=
    @Subsingleton.elim (Domain.Inclusion W (c.chart i).toDomain) inferInstance _ _
  have hg : r ≫ q = g :=
    @Subsingleton.elim (Domain.Inclusion W (c.chart j).toDomain) inferInstance _ _
  rw [← hf, ← hg]
  exact congrArg r.restriction (sectionFamily_agrees_on_inter K L A c σ a i j)

private def sectionGlue (σ : H) (a : U.algebra) : U.algebra :=
  (D).algebraGlue (sectionFamily K L A c σ a) (sectionFamily_compatible K L A c σ a)

private theorem restriction_sectionGlue (σ : H) (a : U.algebra) (i : Fin c.size) :
    (c.map i).restriction (sectionGlue K L A c σ a) =
      sectionOnChart K L A c σ i ((c.map i).restriction a) :=
  congrFun ((D).algebraRestrict_glue _ _) i

private theorem section_ext {a b : U.algebra}
    (h : ∀ i : Fin c.size, (c.map i).restriction a = (c.map i).restriction b) :
    a = b :=
  (D).algebra_ext_of_restrict_eq h

private def domainSectionRingHom (σ : H) : U.algebra →+* U.algebra where
  toFun := sectionGlue K L A c σ
  map_one' := by
    apply section_ext K L A c
    intro i
    simp only [restriction_sectionGlue, map_one]
    exact map_one (sectionOnChart K L A c σ i).toRingHom
  map_mul' a b := by
    apply section_ext K L A c
    intro i
    simp only [restriction_sectionGlue, map_mul]
    exact map_mul (sectionOnChart K L A c σ i).toRingHom _ _
  map_zero' := by
    apply section_ext K L A c
    intro i
    simp only [restriction_sectionGlue, map_zero]
    exact map_zero (sectionOnChart K L A c σ i).toRingHom
  map_add' a b := by
    apply section_ext K L A c
    intro i
    simp only [restriction_sectionGlue, map_add]
    exact map_add (sectionOnChart K L A c σ i).toRingHom _ _

/-- Bounded descent of the actual rational section operators to the original
stored algebra of the represented domain. -/
def domainSectionMap (σ : H) : BoundedRingHom U.algebra U.algebra where
  toRingHom := domainSectionRingHom K L A c σ
  bounded := by
    classical
    choose M hMpositive hM using fun i => (c.map i).restriction.bounded
    let C := (∑ i, M i) + 1
    have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpositive i).le
    have hC : 0 < C := by dsimp [C]; linarith
    refine ⟨(D).algebraRestrictionBound * C, mul_pos (D).algebraRestrictionBound_pos hC, fun a => ?_⟩
    have hrestrict : ‖(D).algebraRestrict (sectionGlue K L A c σ a)‖ ≤ C * ‖a‖ := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg a))).2
      intro i
      change Fin c.size at i
      have hMi : M i ≤ C := by
        refine (Finset.single_le_sum (fun j _ => (hMpositive j).le)
          (Finset.mem_univ i)).trans ?_
        dsimp [C]
        linarith
      change ‖(c.map i).restriction (sectionGlue K L A c σ a)‖ ≤ C * ‖a‖
      rw [restriction_sectionGlue]
      exact (norm_rationalSectionMap_le K L A (c.chart i) H
        (coverSectionSubgroup_le_chart K L A c i) σ _).trans
        ((hM i a).trans (mul_le_mul_of_nonneg_right hMi (norm_nonneg a)))
    exact ((D).norm_le_algebraRestrictionBound (sectionGlue K L A c σ a)).trans
      ((mul_le_mul_of_nonneg_left hrestrict (D).algebraRestrictionBound_pos.le).trans_eq
        (mul_assoc _ _ _).symm)

@[simp]
theorem restriction_domainSectionMap (σ : H) (a : U.algebra) (i : Fin c.size) :
    (c.map i).restriction (domainSectionMap K L A c σ a) =
      sectionOnChart K L A c σ i ((c.map i).restriction a) :=
  restriction_sectionGlue K L A c σ a i

@[simp]
theorem domainSectionMap_baseMap (σ : H) (a : B) :
    domainSectionMap K L A c σ (U.baseMap a) = U.baseMap (coefficientHom K L A σ a) := by
  apply section_ext K L A c
  intro i
  have hi (b : B) : (c.map i).restriction (U.baseMap b) = (c.chart i).baseMap b :=
    congrArg (fun f : BoundedAlgHom L B (c.chart i).algebra => f b) (c.map i).comp_baseMap
  rw [restriction_domainSectionMap, hi, hi]
  exact rationalSectionMap_baseMap K L A (c.chart i) H (coverSectionSubgroup_le_chart K L A c i)
    σ a

@[simp]
theorem domainSectionMap_one :
    domainSectionMap K L A c 1 = BoundedRingHom.id U.algebra := by
  apply BoundedRingHom.ext
  intro a
  apply section_ext K L A c
  intro i
  rw [restriction_domainSectionMap, sectionOnChart, rationalSectionMap_one]
  rfl

theorem domainSectionMap_mul (σ τ : H) :
    domainSectionMap K L A c (σ * τ) =
      (domainSectionMap K L A c σ).comp (domainSectionMap K L A c τ) := by
  apply BoundedRingHom.ext
  intro a
  apply section_ext K L A c
  intro i
  change (c.map i).restriction (domainSectionMap K L A c (σ * τ) a) =
    (c.map i).restriction (domainSectionMap K L A c σ (domainSectionMap K L A c τ a))
  rw [restriction_domainSectionMap, restriction_domainSectionMap, restriction_domainSectionMap]
  simp only [sectionOnChart, rationalSectionMap_mul]
  rfl

/-- The descended operator acts on scalars by the coefficient automorphism. -/
theorem domainSectionMap_scalar (σ : H) (t : L) :
    domainSectionMap K L A c σ (algebraMap L U.algebra t) =
      algebraMap L U.algebra (σ.val.val t) := by
  rw [← U.baseMap.toAlgHom.commutes t, domainSectionMap_baseMap]
  change U.baseMap (coefficientHom K L A σ (scalarMap K L A t)) = _
  rw [coefficientHom_scalar, scalarMap_apply]
  exact U.baseMap.toAlgHom.commutes _

/-- A bounded semilinear map from the domain is determined by its composite
with the ambient algebra. Untwisting by the inverse coefficient operator
reduces the assertion to the representing domain's universal property. -/
theorem semilinearDomainHom_ext {P : PresentedAffinoidAlgebra L} (σ : H)
    (f g : BoundedRingHom U.algebra P)
    (hf : ∀ t : L, f (algebraMap L U.algebra t) = algebraMap L P (σ.val.val t))
    (hg : ∀ t : L, g (algebraMap L U.algebra t) = algebraMap L P (σ.val.val t))
    (h : ∀ a : B, f (U.baseMap a) = g (U.baseMap a)) : f = g := by
  let r := domainSectionMap K L A c σ⁻¹
  let untwist (p : BoundedRingHom U.algebra P)
      (hp : ∀ t : L, p (algebraMap L U.algebra t) = algebraMap L P (σ.val.val t)) :
      BoundedAlgHom L U.algebra P := {
    toRingHom := (p.comp r).toRingHom
    commutes' t := by
      change p (domainSectionMap K L A c σ⁻¹ (algebraMap L U.algebra t)) = algebraMap L P t
      rw [domainSectionMap_scalar, hp]
      exact congrArg (algebraMap L P) (σ.val.val.apply_symm_apply t)
    bounded := (p.comp r).bounded }
  let f' := untwist f hf
  let g' := untwist g hg
  have heq : f'.comp U.baseMap = g'.comp U.baseMap := by
    apply BoundedAlgHom.ext
    intro a
    change f (domainSectionMap K L A c σ⁻¹ (U.baseMap a)) =
      g (domainSectionMap K L A c σ⁻¹ (U.baseMap a))
    rw [domainSectionMap_baseMap]
    exact h _
  obtain ⟨p, _, hunique⟩ := U.represents.2.2 P (f'.comp U.baseMap) (fun x =>
    U.represents.hasImageIn (BanachSpectrum.comap f'.toBoundedRingHom x))
  have hfg : f' = g' := (hunique f' rfl).trans (hunique g' heq.symm).symm
  apply BoundedRingHom.ext
  intro a
  let b := domainSectionMap K L A c σ a
  have hb : r b = a := by
    change ((domainSectionMap K L A c σ⁻¹).comp (domainSectionMap K L A c σ)) a = a
    rw [← domainSectionMap_mul, inv_mul_cancel, domainSectionMap_one]
    rfl
  have hab : f (r b) = g (r b) := congrArg (fun q : BoundedAlgHom L U.algebra P => q b) hfg
  simpa only [hb] using hab

/-- On the represented domain spectrum the operator induces the restriction
of the ambient coefficient map by seminorm pullback. -/
theorem comap_domainSectionMap (σ : H) (x : BanachSpectrum U.algebra) :
    BanachSpectrum.comap U.baseMap.toBoundedRingHom
      (BanachSpectrum.comap (domainSectionMap K L A c σ) x) =
    BanachSpectrum.comap (coefficientHom K L A σ).toBoundedRingHom
      (BanachSpectrum.comap U.baseMap.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro b
  change x (domainSectionMap K L A c σ (U.baseMap b)) =
    x (U.baseMap (coefficientHom K L A σ b))
  rw [domainSectionMap_baseMap]

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* ↥(isometricAutomorphisms K L))
variable (hρ : ∀ t : L, Continuous (fun g : G => ((ρ g).val t : L)))

/-- Finiteness of the rational cover and its overlap family gives a common
open subgroup for the descended operators. -/
def domainCoverSectionOpenSubgroup : OpenSubgroup G :=
  (OpenSubgroup.iInfOfFinite (fun i : Fin c.size =>
    rationalSectionOpenSubgroup K L A (c.chart i) ρ hρ)) ⊓
  (OpenSubgroup.iInfOfFinite (fun p : Fin c.size × Fin c.size =>
    rationalSectionOpenSubgroup K L A ((c.chart p.1).inter (c.chart p.2)) ρ hρ))

local notation "J" => domainCoverSectionOpenSubgroup K L A c ρ hρ

theorem mem_domainCoverSectionOpenSubgroup (g : G) :
    g ∈ J ↔ ρ g ∈ H := by
  change (g ∈ (⨅ i : Fin c.size,
      (rationalSectionOpenSubgroup K L A (c.chart i) ρ hρ).toSubgroup) ∧
    g ∈ (⨅ p : Fin c.size × Fin c.size,
      (rationalSectionOpenSubgroup K L A ((c.chart p.1).inter (c.chart p.2)) ρ hρ).toSubgroup)) ↔
    ρ g ∈ ((⨅ i : Fin c.size, rationalSectionIsometrySubgroup K L A (c.chart i)) ⊓
      (⨅ p : Fin c.size × Fin c.size,
        rationalSectionIsometrySubgroup K L A ((c.chart p.1).inter (c.chart p.2))))
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  rfl

private def sectionCoefficient (g : J) : H :=
  ⟨ρ g.val, (mem_domainCoverSectionOpenSubgroup K L A c ρ hρ g.val).mp g.property⟩

/-- Bounded semilinear section operators on the common open subgroup of any
actual finite rational cover. -/
def openDomainSectionMap (g : J) : BoundedRingHom U.algebra U.algebra :=
  domainSectionMap K L A c (sectionCoefficient K L A c ρ hρ g)

/-- The open-subgroup operator acts on the coefficient field by the
specified field automorphism. -/
theorem openDomainSectionMap_scalar (g : J) (t : L) :
    openDomainSectionMap K L A c ρ hρ g (algebraMap L U.algebra t) =
      algebraMap L U.algebra ((ρ g).val t) :=
  domainSectionMap_scalar K L A c (sectionCoefficient K L A c ρ hρ g) t

/-- Pullback by the open-subgroup section operator agrees over the ambient
spectrum with the corresponding coefficient pullback. -/
theorem comap_openDomainSectionMap (g : J) (x : BanachSpectrum U.algebra) :
    BanachSpectrum.comap U.baseMap.toBoundedRingHom
      (BanachSpectrum.comap (openDomainSectionMap K L A c ρ hρ g) x) =
    BanachSpectrum.comap (coefficientHom K L A (ρ g)).toBoundedRingHom
      (BanachSpectrum.comap U.baseMap.toBoundedRingHom x) :=
  comap_domainSectionMap K L A c (sectionCoefficient K L A c ρ hρ g) x

@[simp]
theorem openDomainSectionMap_one :
    openDomainSectionMap K L A c ρ hρ 1 = BoundedRingHom.id U.algebra := by
  have h : sectionCoefficient K L A c ρ hρ 1 = 1 :=
    Subtype.ext (map_one ρ)
  rw [openDomainSectionMap, h, domainSectionMap_one]

private theorem continuous_chartSectionOrbit (a : U.algebra) (i : Fin c.size) :
    Continuous (fun g : J =>
      sectionOnChart K L A c (sectionCoefficient K L A c ρ hρ g) i
        ((c.map i).restriction a)) := by
  let ρ' := ρ.comp (J).toSubgroup.subtype
  exact continuous_rationalSectionMap K L A (c.chart i) ρ'
    (fun t => (hρ t).comp continuous_subtype_val) H
    (coverSectionSubgroup_le_chart K L A c i)
    (fun g => (sectionCoefficient K L A c ρ hρ g).property) ((c.map i).restriction a)

private theorem dist_le_restrictionBound (a b : U.algebra) :
    dist a b ≤ (D).algebraRestrictionBound * dist ((D).algebraRestrict a)
      ((D).algebraRestrict b) := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : (D).algebraRestrict (a - b) = (D).algebraRestrict a - (D).algebraRestrict b := by
    funext i
    exact map_sub ((D).map i).restriction.toAlgHom a b
  rw [← h]
  exact (D).norm_le_algebraRestrictionBound (a - b)

/-- Norm continuity on the finite rational cover gives norm continuity of
every descended section in the actual stored domain algebra. -/
theorem continuous_openDomainSectionMap (a : U.algebra) :
    Continuous (fun g : J => openDomainSectionMap K L A c ρ hρ g a) := by
  let F (g : J) := openDomainSectionMap K L A c ρ hρ g a
  let f (g : J) := (D).algebraRestrict (F g)
  have hc : Continuous f := continuous_pi fun i => by
    change Fin c.size at i
    exact (continuous_chartSectionOrbit K L A c ρ hρ a i).congr fun g =>
      (restriction_domainSectionMap K L A c (sectionCoefficient K L A c ρ hρ g) a i).symm
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  let C := (D).algebraRestrictionBound
  have hC : 0 < C := (D).algebraRestrictionBound_pos
  filter_upwards [Metric.continuousAt_iff'.mp hc.continuousAt
    (ε / C) (div_pos hε hC)] with h hh
  apply (dist_le_restrictionBound K L A c _ _).trans_lt
  change C * dist (f h) (f g) < ε
  exact (mul_lt_mul_of_pos_left hh hC).trans_eq (by field_simp)

/-- Inverse pullback by these section operators acts jointly continuously
on the actual spectrum of the represented domain. -/
theorem continuous_openDomainSectionPoints :
    Continuous (fun p : J × BanachSpectrum U.algebra =>
      BanachSpectrum.comap (openDomainSectionMap K L A c ρ hρ p.1⁻¹) p.2) := by
  let : IsTopologicalGroup J :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype J)
  exact BanachSpectrum.continuous_comap_of_continuous_apply
    (fun g : J => openDomainSectionMap K L A c ρ hρ g⁻¹)
    (fun b => (continuous_openDomainSectionMap K L A c ρ hρ b).comp continuous_inv)

/-- Near the identity the transported section meets an arbitrary prescribed
positive spectral tolerance at every point of the represented domain. -/
theorem eventually_spectral_displacement_le (a : U.algebra) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 (1 : J), ∀ x : BanachSpectrum U.algebra,
      x (openDomainSectionMap K L A c ρ hρ g a - a) ≤ ε := by
  have hcont : Continuous (fun g : J => ‖openDomainSectionMap K L A c ρ hρ g a - a‖) :=
    ((continuous_openDomainSectionMap K L A c ρ hρ a).sub continuous_const).norm
  have hz : ‖openDomainSectionMap K L A c ρ hρ 1 a - a‖ < ε := by
    rw [openDomainSectionMap_one]
    change ‖a - a‖ < ε
    rwa [sub_self, norm_zero]
  filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hz)] with g hg x
  exact (x.le_norm _).trans hg.le

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
