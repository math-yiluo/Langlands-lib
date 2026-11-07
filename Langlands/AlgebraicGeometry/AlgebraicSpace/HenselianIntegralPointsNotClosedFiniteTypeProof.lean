import Langlands.AlgebraicGeometry.AlgebraicSpace.DoubledPointLine
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# A quasi-separated finite type space whose integral points are not closed

The closedness assertion of Conrad's Corollary 5.7 fails without separatedness. Over the
closed unit ball `O` of a nontrivially normed field `K`, choose `p ∈ O` with `0 < ‖p‖ < 1`.
Glue the affine lines `Spec O[t]` and `Spec O[s]` along `D(p t)` and `D(p (p s - 1))` by
`t = p s - 1` (`DoubledPointLine`). The result `X` is a quasi-separated scheme of finite type over
`O`. Informally, its generic fibre is the affine line with the point `t = 0` doubled by
`s = 1/p`.

The `O`-points `t = pⁿ` of the first chart are the points `s = (1 + pⁿ)/p` of the second chart,
which converge to `s = 1/p`. That point is not the image of an `O`-point: through the second
chart it would need `1/p ∈ O`, and through the first chart it would lie in the common open,
where `p s - 1` is invertible. So the image of `X(O)` in `X_K(K)` is not closed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Polynomial Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap ringTestMap_comp ringTestMap_left schemePointTopology
    schemePointTopology_eq_affine ringBaseChange ringPointBaseChangeEquiv
    schemeBaseChangeTopology_proof range_subset_open_iff_closedPoint ringTestMap
    affineRingPointEquiv spectrumAlgebraPointHomeomorph AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open HenselianIntegralPointsNotClosed

namespace DoubledPointLine

variable (R : Type u) [CommRing R] (p : R)

/-- The glued scheme as a scheme over `Spec R`. -/
def overBase : Over (Spec (CommRingCat.of R)) := Over.mk (toBase R p)

/-- The charts as morphisms over `Spec R`. -/
def chart (b : ULift.{u} Bool) : ringTest R R[X] ⟶ overBase R p :=
  Over.homMk (ι R p b) (ι_toBase R p b)

@[simp] theorem chart_left (b : ULift.{u} Bool) : (chart R p b).left = ι R p b := rfl

instance : QuasiSeparatedSpace (glued R p) :=
  CommonOpenGluing.quasiSeparatedSpace

instance : CompactSpace (glued R p) := by
  constructor
  have h : (Set.univ : Set (glued R p)) =
      Set.range (ι R p ⟨true⟩) ∪ Set.range (ι R p ⟨false⟩) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    obtain ⟨⟨b⟩, y, rfl⟩ := CommonOpenGluing.exists_ι_apply (g := g R p) x
    cases b
    · exact Or.inr ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
  rw [h]
  exact (isCompact_range (ι R p _).continuous).union (isCompact_range (ι R p _).continuous)

theorem quasiSeparated_hom : QuasiSeparated (overBase R p).hom :=
  (quasiSeparated_iff_quasiSeparatedSpace (overBase R p).hom).mpr
    (inferInstanceAs (QuasiSeparatedSpace (glued R p)))

theorem quasiCompact_hom : QuasiCompact (overBase R p).hom :=
  quasiCompact_of_compactSpace (X := glued R p) (overBase R p).hom

set_option backward.isDefEq.respectTransparency false in
theorem locallyOfFiniteType_hom : LocallyOfFiniteType (overBase R p).hom := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (CommonOpenGluing.glueData _ _ (g R p)).openCover fun b => ?_
  change LocallyOfFiniteType (ι R p b ≫ toBase R p)
  rw [ι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The space of the glued scheme is quasi-separated. -/
theorem isQuasiSeparated : IsQuasiSeparated ((schemeToSpace _).obj (overBase R p)) := by
  have := quasiSeparated_hom R p
  exact isQuasiSeparated_schemeToSpace _

/-- The space of the glued scheme is of finite type. -/
theorem finiteTypeOverRing : FiniteTypeOverRing R ((schemeToSpace _).obj (overBase R p)) :=
  HasAtlasProperty.of_scheme _ ⟨locallyOfFiniteType_hom R p, quasiCompact_hom R p⟩

section Points

/-- The point of the glued scheme given by a point of the chart `b`. -/
def chartPoint {T : Type u} [CommRing T] [Algebra R T] (b : ULift.{u} Bool)
    (q : RingPoint R (ringTest R R[X]) T) : RingPoint R (overBase R p) T :=
  q ≫ chart R p b

variable {R p}

/-- Each chart of the glued scheme is an open immersion. -/
instance (b : ULift.{u} Bool) : _root_.AlgebraicGeometry.IsOpenImmersion (chart R p b).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (ι R p b))

/-- Over a local ring, every point of the glued scheme factors through one of the charts. -/
theorem exists_chart_factor {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (x : RingPoint R (overBase R p) S) :
    ∃ (b : ULift.{u} Bool) (a : RingPoint R (ringTest R R[X]) S), a ≫ chart R p b = x := by
  obtain ⟨b, a₀, ha₀⟩ := CommonOpenGluing.exists_lift_of_isLocalRing (g := g R p) x.left
  refine ⟨b, Over.homMk a₀ ?_, ?_⟩
  · change a₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) = Spec.algebraMap R S
    rw [← ι_toBase R p b, ← Category.assoc, ha₀]
    exact Over.w x
  · exact Over.OverMorphism.ext ha₀

/-- A point of the chart `s` which is also a point of the chart `t`: if `p (p s - 1)` is a unit,
the point `s` of the second chart is the point `t = p s - 1` of the first chart. -/
theorem ringTestMap_aeval_chart_eq {T : Type u} [CommRing T] [Algebra R T] (s : T)
    (hs : IsUnit (aeval s (f₂ R p))) :
    ringTestMap R (aeval (aeval s (C p * X - 1))) ≫ chart R p ⟨true⟩ =
      ringTestMap R (aeval s) ≫ chart R p ⟨false⟩ := by
  let ω : B₂ R p →+* T := IsLocalization.Away.lift (f₂ R p) (g := (aeval s).toRingHom) hs
  have h₂ : ω.comp (algebraMap R[X] (B₂ R p)) = (aeval s).toRingHom :=
    IsLocalization.Away.lift_comp _ hs
  have h₁ : ω.comp (α R p) = (aeval (aeval s (C p * X - 1))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, α_C, ← RingHom.comp_apply, h₂]
      simp
    · rw [RingHom.comp_apply, α, coe_eval₂RingHom, eval₂_X, ← RingHom.comp_apply, h₂]
      simp
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (aeval (aeval s (C p * X - 1))).toRingHom) ≫ ι R p ⟨true⟩ =
    Spec.map (CommRingCat.ofHom (aeval s).toRingHom) ≫ ι R p ⟨false⟩
  rw [← h₁, ← h₂, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom ω) ≫ ·)
    (CommonOpenGluing.g_ι _ _ (g R p) ⟨true⟩ ⟨false⟩)

/-- A point of the chart `t` is never the point `s = 1/p` of the chart `s`, since on the
common open `p s - 1` is invertible. -/
theorem chart_true_ne {T : Type u} [CommRing T] [Algebra R T] [Nontrivial T] (c : T)
    (hc : algebraMap R T p * c = 1) (a : RingPoint R (ringTest R R[X]) T) :
    a ≫ chart R p ⟨true⟩ ≠ ringTestMap R (aeval c) ≫ chart R p ⟨false⟩ := by
  intro h
  have hl : a.left ≫ ι R p ⟨true⟩ = Spec.map (CommRingCat.ofHom (aeval c).toRingHom) ≫
      ι R p ⟨false⟩ := congrArg (fun f => f.left) h
  obtain ⟨w₀, -, hw₀⟩ := CommonOpenGluing.exists_of_comp_eq _ _ (g R p)
    (i := ⟨true⟩) (j := ⟨false⟩) (by simp) _ _ hl
  let w : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (B₂ R p)) := w₀
  have hw : w ≫ g₂ R p = Spec.map (CommRingCat.ofHom (aeval c).toRingHom) := hw₀
  have hω : CommRingCat.ofHom (algebraMap R[X] (B₂ R p)) ≫ Spec.preimage w =
      CommRingCat.ofHom (aeval c).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hw
  have hunit : IsUnit ((Spec.preimage w).hom (algebraMap R[X] (B₂ R p) (f₂ R p))) :=
    (IsLocalization.Away.algebraMap_isUnit (S := B₂ R p) (f₂ R p)).map (Spec.preimage w).hom
  have hzero : (Spec.preimage w).hom (algebraMap R[X] (B₂ R p) (f₂ R p)) = 0 := by
    have := congrArg (fun φ => φ.hom (f₂ R p)) hω
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [this]
    simp [f₂, hc]
  exact hunit.ne_zero hzero

/-- An `R`-point of the chart `s` whose image in `T` is the point `s = c` has coordinate
mapping to `c`. -/
theorem algebraMap_eq_of_chart_false {T : Type u} [CommRing T] [Algebra R T] (c : T)
    (a : RingPoint R (ringTest R R[X]) R)
    (h : ringTestMap R (Algebra.ofId R T) ≫ a ≫ chart R p ⟨false⟩ =
      ringTestMap R (aeval c) ≫ chart R p ⟨false⟩) :
    algebraMap R T (affineRingPointEquiv R R[X] R a X) = c := by
  have hm : Mono (chart R p ⟨false⟩) := by
    have : Mono (chart R p ⟨false⟩).left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  have h' : ringTestMap R (Algebra.ofId R T) ≫ a = ringTestMap R (aeval c) :=
    (cancel_mono (chart R p ⟨false⟩)).1 ((Category.assoc _ _ _).trans h)
  have ha : a = ringTestMap R (affineRingPointEquiv R R[X] R a) :=
    (affineRingPointEquiv R R[X] R).injective (affineRingPointEquiv_ringTestMap _).symm
  rw [ha, ← ringTestMap_comp] at h'
  have := congrArg (fun q => affineRingPointEquiv R R[X] T q X) h'
  simp only [affineRingPointEquiv_ringTestMap, AlgHom.comp_apply, aeval_X] at this
  exact this

end Points

end DoubledPointLine


open HenselianIntegralPointsNotClosed DoubledPointLine in
/-- **The closedness assertion of Conrad's Corollary 5.7 fails for quasi-separated spaces of
finite type.** The doubled-point line over `O` is a quasi-separated scheme of finite type
whose image of `O`-points in the rational points of the generic fibre is not closed. -/
theorem henselianIntegralPointsNotClosedOfFiniteType :
    HenselianIntegralPointsNotClosedOfFiniteTypeStatement.{u} := by
  intro K _ O hO _
  obtain ⟨p₀, hp₀, hp₁⟩ := NormedField.exists_norm_lt_one K
  let p : O := ⟨p₀, (hO p₀).mpr hp₁.le⟩
  have hp₀' : p₀ ≠ 0 := norm_pos_iff.mp hp₀
  refine ⟨(schemeToSpace _).obj (overBase O p), isQuasiSeparated O p, finiteTypeOverRing O p, ?_⟩
  let 𝒳 := (schemeToSpace _).obj (overBase O p)
  let XK := baseChange (Spec.algebraMap O K) 𝒳
  let : TopologicalSpace (RingPoints K XK K) := etaleChartTopology K XK
  let U := ringTest O O[X]
  let f : (schemeToSpace _).obj U ⟶ 𝒳 := (schemeToSpace _).map (chart O p ⟨false⟩)
  have hf : IsEtale (hom f) := isEtale_map _ inferInstance
  let d := baseChangeChart K U f hf
  let Φ : K → RingPoints K XK K := fun s =>
    d.pointMap (ringPointBaseChangeEquiv O K K U (linePoint O s))
  have hΦ : Continuous Φ := by
    have h₁ := d.continuous_pointMap
    have h₂ := @IsHomeomorph.continuous _ _ (schemePointTopology O U K)
      (schemePointTopology K (ringBaseChange O K U) K) _ (schemeBaseChangeTopology_proof O K K U)
    have h₃ := continuous_linePoint (O := O) K
    exact @Continuous.comp _ _ _ _ (schemePointTopology K d.scheme K) _ _ _ h₁
      (@Continuous.comp _ _ _ _ (schemePointTopology O U K) (schemePointTopology K d.scheme K)
        _ _ h₂ h₃)
  have hΦeq : ∀ s : K, baseChangeRingPointsEquiv O K K 𝒳 (Φ s) =
      (schemeRingPointsEquiv O (overBase O p) K).symm (chartPoint O p ⟨false⟩ (linePoint O s)) := by
    intro s
    rw [baseChangeRingPointsEquiv_baseChangeChart_pointMap, Equiv.symm_apply_apply]
    rfl
  let c : K := p₀⁻¹
  have hc : algebraMap O K p * c = 1 := mul_inv_cancel₀ hp₀'
  have hnot : Φ c ∉ Set.range fun x : RingPoints O 𝒳 O =>
      (baseChangeRingPointsEquiv O K K 𝒳).symm (RingPoints.changeRing (Algebra.ofId O K) x) := by
    rintro ⟨x, hx⟩
    have h₁ : RingPoints.changeRing (Algebra.ofId O K) x =
        (schemeRingPointsEquiv O (overBase O p) K).symm
          (chartPoint O p ⟨false⟩ (linePoint O c)) := by
      have := congrArg (baseChangeRingPointsEquiv O K K 𝒳) hx
      simp only [Equiv.apply_symm_apply] at this
      rw [this, hΦeq]
    have hx' := congrArg (schemeRingPointsEquiv O (overBase O p) K) h₁
    rw [Equiv.apply_symm_apply, schemeRingPointsEquiv_changeRing] at hx'
    obtain ⟨b, a, ha⟩ := exists_chart_factor (schemeRingPointsEquiv O (overBase O p) O x)
    rw [← ha] at hx'
    obtain ⟨b⟩ := b
    cases b
    · have hac := algebraMap_eq_of_chart_false c a hx'
      have hle : ‖c‖ ≤ 1 := by
        rw [← hac]
        exact (hO _).mp (affineRingPointEquiv O O[X] O a X).2
      have hlt : 1 < ‖c‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ hp₀).mpr hp₁
      exact absurd hle (not_le.mpr hlt)
    · exact chart_true_ne c hc (ringTestMap O (Algebra.ofId O K) ≫ a)
        ((Category.assoc _ _ _).trans hx')
  let s : ℕ → K := fun n => c * (1 + p₀ ^ n)
  have hs : Tendsto s atTop (𝓝 c) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp₁).const_add 1
    have h' := h.const_mul c
    simpa [s] using h'
  have hmem : ∀ n, Φ (s n) ∈ Set.range fun x : RingPoints O 𝒳 O =>
      (baseChangeRingPointsEquiv O K K 𝒳).symm (RingPoints.changeRing (Algebra.ofId O K) x) := by
    intro n
    refine ⟨(schemeRingPointsEquiv O (overBase O p) O).symm
      (chartPoint O p ⟨true⟩ (linePoint O (p ^ n))), ?_⟩
    apply (baseChangeRingPointsEquiv O K K 𝒳).injective
    rw [hΦeq, Equiv.apply_symm_apply]
    apply (schemeRingPointsEquiv O (overBase O p) K).injective
    rw [schemeRingPointsEquiv_changeRing, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have e : (Algebra.ofId O K).comp (aeval (p ^ n)) = aeval (aeval (s n) (C p * X - 1)) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, aeval_C, map_one, s, c]
      simp only [Algebra.ofId_apply, map_pow]
      change (p₀ ^ n : K) = p₀ * (p₀⁻¹ * (1 + p₀ ^ n)) - 1
      field_simp
      ring
    have hunit : IsUnit (aeval (s n) (f₂ O p)) := by
      rw [isUnit_iff_ne_zero]
      simp only [f₂, map_mul, map_sub, aeval_C, aeval_X, map_one, s, c]
      change p₀ * (p₀ * (p₀⁻¹ * (1 + p₀ ^ n)) - 1) ≠ 0
      rw [← mul_assoc, mul_inv_cancel₀ hp₀', one_mul, add_sub_cancel_left]
      exact mul_ne_zero hp₀' (pow_ne_zero n hp₀')
    have h := ringTestMap_aeval_chart_eq (s n) hunit
    rw [← e, ringTestMap_comp, Category.assoc] at h
    exact h
  intro hclosed
  exact hnot (hclosed.mem_of_tendsto ((hΦ.tendsto c).comp hs) (Eventually.of_forall hmem))

end Langlands.AlgebraicGeometry.AlgebraicSpace
