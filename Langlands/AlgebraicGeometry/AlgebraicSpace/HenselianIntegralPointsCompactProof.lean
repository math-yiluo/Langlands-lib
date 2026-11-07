import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPoints
import Langlands.AlgebraicGeometry.PointTopology.CompactPointProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs

/-!
# Integral points over a locally compact henselian valuation ring are quasi-compact

Conrad's Corollary 5.7 (printed pp.16–17), quasi-compactness. Let `K` be a locally compact
nontrivially normed field whose closed unit ball is a henselian subring `O`, and let `X` be a
quasi-separated algebraic space of finite type over `Spec O`. The image of `X(O)` in the
rational points of the generic fibre `X_K` is quasi-compact for the étale-chart topology.

Following Conrad: the residue field `κ` of `O` is finite, so `X(κ)` is finite
(`FiniteFieldPoints.finite_ringPoints`). For each residue point choose an affine étale chart
`U → X` with a `κ`-point over it (`FieldPointEtaleLift`). By Hensel, every `O`-point of `X`
with that residue point comes from an `O`-point of `U`. Each `U(O)` is compact because `O` is.
So the image of `X(O)` is a finite union of continuous images of compact sets.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianUnitBall

variable {K : Type u} [NontriviallyNormedField K] (O : Subring K)

/-- An element of the closed unit ball is a unit of `O` exactly when it has norm `1`. -/
theorem isUnit_iff_norm_eq_one (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) (y : O) :
    IsUnit y ↔ ‖(y : K)‖ = 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : ‖((w : O) : K)‖ * ‖(((w⁻¹ : Oˣ) : O) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
    have h2 := (hO _).1 (w : O).2
    have h3 := (hO _).1 ((w⁻¹ : Oˣ) : O).2
    nlinarith [norm_nonneg ((w : O) : K), norm_nonneg (((w⁻¹ : Oˣ) : O) : K)]
  · intro hy
    have hy0 : (y : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hy
      exact zero_ne_one hy
    have hinv : (y : K)⁻¹ ∈ O := (hO _).2 (by rw [norm_inv, hy, inv_one])
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext ?_)
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hy0

/-- The maximal ideal of `O` is the open unit ball. -/
theorem mem_maximalIdeal_iff (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) [IsLocalRing O] (y : O) :
    y ∈ IsLocalRing.maximalIdeal O ↔ ‖(y : K)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one O hO]
  have := (hO _).1 y.2
  constructor
  · intro h
    exact lt_of_le_of_ne this h
  · intro h
    exact h.ne

/-- Over a locally compact field, the closed unit ball is compact. -/
theorem compactSpace [LocallyCompactSpace K] (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) :
    CompactSpace O := by
  have : ProperSpace K := ProperSpace.of_locallyCompactSpace K
  have hset : (O : Set K) = Metric.closedBall 0 1 := by
    ext x
    rw [SetLike.mem_coe, hO, mem_closedBall_zero_iff]
  exact isCompact_iff_compactSpace.mp (hset ▸ isCompact_closedBall (0 : K) 1)

/-- Over a locally compact field, the residue field of the closed unit ball is finite. -/
theorem finite_residueField [LocallyCompactSpace K] (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    [IsLocalRing O] : Finite (IsLocalRing.ResidueField O) := by
  have := compactSpace O hO
  let _ : TopologicalSpace (IsLocalRing.ResidueField O) := ⊥
  have : DiscreteTopology (IsLocalRing.ResidueField O) := ⟨rfl⟩
  have hcont : Continuous (IsLocalRing.residue O) := by
    rw [continuous_discrete_rng]
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    have hset : IsLocalRing.residue O ⁻¹' {IsLocalRing.residue O a} =
        (fun y : O => ‖((y : K) - (a : K))‖) ⁻¹' Set.Iio 1 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iio]
      change Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ a ↔ _
      rw [Ideal.Quotient.eq, mem_maximalIdeal_iff O hO]
      rfl
    rw [hset]
    exact isOpen_Iio.preimage
      ((continuous_subtype_val.sub continuous_const).norm)
  have hc : IsCompact (Set.range (IsLocalRing.residue O)) := isCompact_range hcont
  rw [Set.range_eq_univ.mpr IsLocalRing.residue_surjective] at hc
  have := isCompact_univ_iff.mp hc
  exact finite_of_compact_of_discrete

/-- The `O`-points of an affine scheme of finite type over `O` form a compact subset of its
`K`-points. -/
theorem isCompact_range_changeRing [LocallyCompactSpace K] (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (U : Over (Spec (CommRingCat.of O))) [IsAffine U.left] [LocallyOfFiniteType U.hom] :
    @IsCompact _ (schemePointTopology O U K)
      (Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K)) := by
  have := compactSpace O hO
  have : CompactSpace (RingPoint O U O) := affineSchemeCompactness_proof O O U
  rw [schemePointTopology_eq_affine]
  exact isCompact_range (affineSchemeCoefficientContinuity_proof O O K U (Algebra.ofId O K)
    continuous_subtype_val)

end HenselianUnitBall

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap ringTestMap_left schemePointTopology ringBaseChange
    ringPointBaseChangeEquiv schemeBaseChangeTopology_proof)

namespace HenselianIntegralPointsCompact

open HenselianIntegralPointsOpen

variable {O : Type u} [CommRing O] [HenselianLocalRing O]

/-- **Lifting along a chart with a residue point.** Over a henselian local ring `O`, let
`f : U → X` be étale and let `ū` be a residue-field point of `U` over the residue point of
`x ∈ X(O)`. Then `x` is the image of an `O`-point of `U`. -/
theorem exists_point_of_residue_point (X : AlgebraicSpace (Spec (CommRingCat.of O)))
    (x : RingPoints O X O) {U : Over (Spec (CommRingCat.of O))}
    (f : (schemeToSpace _).obj U ⟶ X) (hf : IsEtale (hom f))
    (ū : RingPoint O U (IsLocalRing.ResidueField O))
    (hū : RingPoints.map f ((schemeRingPointsEquiv O U _).symm ū) =
      RingPoints.changeRing (Algebra.ofId O (IsLocalRing.ResidueField O)) x) :
    ∃ u : RingPoint O U O, RingPoints.map f ((schemeRingPointsEquiv O U O).symm u) = x := by
  let κ := IsLocalRing.ResidueField O
  have hκ : Function.Surjective (algebraMap O κ) := IsLocalRing.residue_surjective
  let a : (schemeYoneda _).obj U ⟶ X.presheaf := hom f
  let hr := X.representable_from_scheme a
  let xh : (schemeYoneda (Spec (CommRingCat.of O))).obj (ringTest O O) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := hr.pullback xh
  let p : P ⟶ ringTest O O := hr.snd xh
  let q : P ⟶ U := Functor.relativelyRepresentable.fst' hr xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a xh :=
    Functor.relativelyRepresentable.isPullback' hr xh
  let pl : P.left ⟶ Spec (CommRingCat.of O) := p.left
  have : Etale pl := hf.projection xh _ p hsq
  let π : ringTest O κ ⟶ ringTest O O := ringTestMap O (Algebra.ofId O κ)
  let ūh : ringTest O κ ⟶ U := ū
  have hmap : ∀ v : ringTest O κ ⟶ U, RingPoints.map f ((schemeRingPointsEquiv O U κ).symm v) =
      uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map v ≫ a) := by
    intro v
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  have hūa : (schemeYoneda _).map ūh ≫ a = (schemeYoneda _).map π ≫ xh := by
    apply uliftYonedaEquiv.injective
    rw [← hmap, hū]
    have e₂ : x = uliftYonedaEquiv xh := (Equiv.apply_symm_apply _ _).symm
    change X.presheaf.map π.op x = _
    rw [e₂, uliftYonedaEquiv_naturality]
    rfl
  let b : ringTest O κ ⟶ P := Functor.relativelyRepresentable.lift' hr ūh π hūa
  have hbp : b ≫ p = π := Functor.relativelyRepresentable.lift'_snd hr ūh π hūa
  have hb : b.left ≫ pl = Spec.map (CommRingCat.ofHom (algebraMap O κ)) := by
    change (b ≫ p).left = _
    rw [hbp, ringTestMap_left]
    rfl
  obtain ⟨σ, hσ, -⟩ :=
    CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective hκ pl b.left hb
  let σ' : ringTest O O ⟶ P := Over.homMk σ (by
    change σ ≫ P.hom = (ringTest O O).hom
    rw [← Over.w p]
    let rh : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O) := (ringTest O O).hom
    change σ ≫ pl ≫ rh = rh
    rw [← Category.assoc, hσ, Category.id_comp])
  have hσp : σ' ≫ p = 𝟙 _ := Over.OverMorphism.ext (by
    change σ ≫ pl = 𝟙 _
    exact hσ)
  refine ⟨σ' ≫ q, ?_⟩
  have hua : (schemeYoneda _).map (σ' ≫ q) ≫ a = xh := by
    rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hσp,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have e₁ : RingPoints.map f ((schemeRingPointsEquiv O U O).symm (σ' ≫ q)) =
      uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map (σ' ≫ q) ≫ a) := by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  rw [e₁, hua]
  exact Equiv.apply_symm_apply uliftYonedaEquiv.{u + 1} x

end HenselianIntegralPointsCompact

open HenselianIntegralPointsOpen HenselianIntegralPointsCompact in
/-- **Conrad's Corollary 5.7, quasi-compactness.** For a locally compact nontrivially normed
field `K` whose closed unit ball is a henselian subring `O`, and a quasi-separated algebraic
space `X` of finite type over `Spec O`, the image of `X(O)` in `X_K(K)` is quasi-compact for
the étale-chart topology. -/
theorem henselianIntegralPointsCompact : HenselianIntegralPointsCompactStatement.{u} := by
  intro K _ O hO hH _ X hXqs hXft
  have : IsUltrametricDist K := PointTopology.HenselianUnitBall.isUltrametricDist O hO
  have : Finite (IsLocalRing.ResidueField O) :=
    PointTopology.HenselianUnitBall.finite_residueField O hO
  let κ := IsLocalRing.ResidueField O
  let XK := baseChange (Spec.algebraMap O K) X
  let ι : RingPoints O X O → RingPoints K XK K := fun x =>
    (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K) x)
  change @IsCompact _ (etaleChartTopology K XK) (Set.range ι)
  let : TopologicalSpace (RingPoints K XK K) := etaleChartTopology K XK
  have hfin : Finite (RingPoints O X κ) :=
    FiniteFieldPoints.finite_ringPoints X hXqs hXft κ
  have hXlft : LocallyOfFiniteTypeOverBase X := by
    obtain ⟨U, a, ha, hs, hU⟩ := hXft.exists_atlas
    exact ⟨U, a, ha, hs, hU.1⟩
  -- a chart for every residue point
  choose U f hU hf ū hū using fun xr : RingPoints O X κ =>
    FieldPointEtaleLift.exists_affine_etale_point (C := O) (k := κ) X xr
  have hUlft : ∀ xr, LocallyOfFiniteType (U xr).hom := fun xr =>
    HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale hXlft (hom (f xr)) (hf xr)
  -- the image of the integral points of each chart
  let N : RingPoints O X κ → Set (RingPoints K XK K) := fun xr =>
    schemePointsMap (X := XK) (restrictAtlas (Spec.algebraMap O K) (hom (f xr))) ''
      (ringPointBaseChangeEquiv O K K (U xr) ''
        Set.range (RingPoint.changeRing (Algebra.ofId O K) :
          RingPoint O (U xr) O → RingPoint O (U xr) K))
  have hcompat : ∀ (xr : RingPoints O X κ) (v : RingPoint O (U xr) O),
      schemePointsMap (X := XK) (restrictAtlas (Spec.algebraMap O K) (hom (f xr)))
          (ringPointBaseChangeEquiv O K K (U xr) (v.changeRing (Algebra.ofId O K))) =
        ι (RingPoints.map (f xr) ((schemeRingPointsEquiv O (U xr) O).symm v)) := by
    intro xr v
    apply (baseChangeRingPointsEquiv O K K X).injective
    refine (baseChangeRingPointsEquiv_schemePointsMap (f xr) _).trans ?_
    rw [Equiv.symm_apply_apply]
    change _ = baseChangeRingPointsEquiv O K K X ((baseChangeRingPointsEquiv O K K X).symm _)
    rw [Equiv.apply_symm_apply, RingPoints.changeRing_map]
    rfl
  have hrange : Set.range ι = ⋃ xr, N xr := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      let xr : RingPoints O X κ := RingPoints.changeRing (Algebra.ofId O κ) x
      have := hU xr
      obtain ⟨u, hu⟩ := exists_point_of_residue_point X x (f xr) (hf xr) (ū xr) (hū xr)
      refine Set.mem_iUnion.2 ⟨xr, _, ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩
      rw [hcompat, hu]
    · intro hy
      obtain ⟨xr, _, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, (hcompat xr v).symm⟩
  rw [hrange]
  refine isCompact_iUnion fun xr => ?_
  have := hU xr
  have := hUlft xr
  -- the base-changed chart is an étale chart of finite type
  let UK := ringBaseChange O K (U xr)
  have hUKlft : LocallyOfFiniteType UK.hom := by
    change LocallyOfFiniteType (pullback.snd (U xr).hom (Spec.algebraMap O K))
    infer_instance
  have hUKqc : QuasiCompact UK.hom := by
    change QuasiCompact (pullback.snd (U xr).hom (Spec.algebraMap O K))
    infer_instance
  have haK : IsEtale (restrictAtlas (Spec.algebraMap O K) (hom (f xr))) := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := hf xr
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap O K) (@Etale.{u}) h
  let c : EtaleFiniteTypeChart K XK :=
    { scheme := UK
      hom := AlgebraicSpace.homMk (restrictAtlas (Spec.algebraMap O K) (hom (f xr)))
      isEtale := haK
      locallyOfFiniteType := hUKlft
      quasiCompact := hUKqc }
  have hc : Continuous[schemePointTopology K UK K, etaleChartTopology K XK]
      (schemePointsMap (X := XK) (restrictAtlas (Spec.algebraMap O K) (hom (f xr)))) :=
    c.continuous_pointMap
  have hS₀ := PointTopology.HenselianUnitBall.isCompact_range_changeRing O hO (U xr)
  have he := schemeBaseChangeTopology_proof O K K (U xr)
  have h₁ := @IsCompact.image _ _ (schemePointTopology O (U xr) K) (schemePointTopology K UK K)
    _ _ hS₀ (@IsHomeomorph.continuous _ _ (schemePointTopology O (U xr) K)
      (schemePointTopology K UK K) _ he)
  exact @IsCompact.image _ _ (schemePointTopology K UK K) (etaleChartTopology K XK) _ _ h₁ hc

end Langlands.AlgebraicGeometry.AlgebraicSpace
