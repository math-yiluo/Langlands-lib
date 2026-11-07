import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianCompletionPointEmbeddingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-!
# Integral points over a henselian valuation ring form an open set

Conrad's Corollary 5.7 (printed p.16), openness. Let `K` be a nontrivially normed field
whose closed unit ball is a henselian subring `O`, and let `X` be an algebraic space locally
of finite type over `Spec O`. The image of `X(O)` in the rational points of the generic
fibre `X_K` is open for the étale-chart topology.

Every `O`-point of `X` comes from an `O`-point of an affine étale chart `U → X`: lift the
residue point to an affine étale chart (`FieldPointEtaleLift`), then lift the resulting
residue point of the étale `O`-scheme `U ×_X Spec O` to a section (Hensel). The `O`-points
of the affine finite type `O`-scheme `U` form an open subset of `U(K)`, cut out by finitely
many closed unit balls, and étale maps are open on `K`-points because `O` is henselian.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianUnitBall

section UnitBall

variable {K : Type u} [NontriviallyNormedField K] (O : Subring K)

/-- A normed field whose closed unit ball is a subring is ultrametric. -/
theorem isUltrametricDist (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_of_norm_le_one fun x hx =>
    (hO _).1 (O.add_mem ((hO x).2 hx) O.one_mem)

/-- The closed unit ball is the valuation subring of the norm valuation. -/
theorem eq_valuationSubring [IsUltrametricDist K] (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) :
    O = (NormedField.valuation (K := K)).valuationSubring.toSubring := by
  ext x
  rw [hO, ValuationSubring.mem_toSubring, Valuation.mem_valuationSubring_iff,
    NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/-- If the closed unit ball is a henselian subring, the valuation subring of the norm
valuation is a henselian local ring. -/
theorem henselianLocalRing_valuationSubring [IsUltrametricDist K]
    (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) [hH : HenselianLocalRing O] :
    HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring := by
  have h := eq_valuationSubring O hO
  subst h
  exact hH

end UnitBall

section SmoothOpen

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]

/-- Over a field with henselian norm valuation ring, smooth morphisms of schemes are open on
rational points: glue `HenselianSmoothOpen.isOpenMap_affineSmoothPointMap` from affine
charts. -/
theorem isOpenMap_smoothSchemePointMap
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) [Smooth f.left] :
    letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
    letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
    IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  let g : RingPoint K X K → RingPoint K Y K := fun p => p ≫ f
  change IsOpenMap g
  intro W hW
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨p, hpW, rfl⟩
  obtain ⟨V, hV, hpV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := f.left (p.left (IsLocalRing.closedPoint K)))
    (U := ⊤) (by trivial)
  let : IsAffine V := hV
  have hpPre : p.left (IsLocalRing.closedPoint K) ∈ f.left ⁻¹ᵁ V := hpV
  obtain ⟨D, hD, hpD, hDPre⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := p.left (IsLocalRing.closedPoint K))
    (U := f.left ⁻¹ᵁ V) hpPre
  let : IsAffine D := hD
  have hDV : D ≤ f.left ⁻¹ᵁ V := hDPre
  let F : openOver K X D ⟶ openOver K Y V :=
    Over.homMk (f.left.resLE V D hDV) (by
      change f.left.resLE V D hDV ≫ (V.ι ≫ Y.hom) = D.ι ≫ X.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w f])
  have hF : F ≫ openOverι K Y V = openOverι K X D ≫ f := by
    apply Over.OverMorphism.ext
    change f.left.resLE V D hDV ≫ V.ι = D.ι ≫ f.left
    exact Scheme.Hom.resLE_comp_ι f.left hDV
  let : Smooth F.left := inferInstanceAs (Smooth (f.left.resLE V D hDV))
  let k : RingPoint K (openOver K X D) K → RingPoint K (openOver K Y V) K :=
    fun q => q ≫ F
  have hk : IsOpenMap k := HenselianSmoothOpen.isOpenMap_affineSmoothPointMap K F
  have hcD : Continuous (X := RingPoint K (openOver K X D) K)
      (Y := RingPoint K X K) (openPointMap K X K D) :=
    schemePointTopology_continuous_chart K X K ⟨D, hD⟩
  have hfg : openPointMap K Y K V ∘ k = g ∘ openPointMap K X K D := by
    funext q
    dsimp only [RingPoint] at q
    change (q ≫ F) ≫ openOverι K Y V = (q ≫ openOverι K X D) ≫ f
    exact (Category.assoc q _ _).trans
      ((congrArg (fun t => q ≫ t) hF).trans (Category.assoc q _ _).symm)
  have hr : Set.range p.left ⊆ D :=
    (range_subset_open_iff_closedPoint K X K D p).mpr hpD
  let q := openPointLift K X K D p hr
  have hq : openPointMap K X K D q = p := openPointMap_lift K X K D p hr
  refine ⟨openPointMap K Y K V '' (k '' (openPointMap K X K D ⁻¹' W)), ?_, ?_, ?_⟩
  · rintro z ⟨t, ⟨s, hsW, rfl⟩, rfl⟩
    exact ⟨openPointMap K X K D s, hsW, (congrFun hfg s).symm⟩
  · exact (isOpenEmbedding_schemeAffineChart K K Y ⟨V, hV⟩).isOpenMap _
      (hk _ (hW.preimage hcD))
  · refine ⟨k q, ⟨q, ?_, rfl⟩, ?_⟩
    · change openPointMap K X K D q ∈ W
      rwa [hq]
    · exact (congrFun hfg q).trans (congrArg g hq)

end SmoothOpen

section IntegralPoints

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] (O : Subring K)

/-- The `O`-points of an affine scheme locally of finite type over `O` form an open subset
of its `K`-points: they are cut out by finitely many closed unit balls. -/
theorem isOpen_range_changeRing (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (U : Over (Spec (CommRingCat.of O))) [IsAffine U.left] [LocallyOfFiniteType U.hom] :
    IsOpen[schemePointTopology O U K]
      (Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K)) := by
  rw [schemePointTopology_eq_affine]
  let A := AffineCoordinateRing O U
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType O A).out
  let T : Set (AlgPoint O A K) := ⋂ a ∈ s, (fun φ : AlgPoint O A K => φ a) ⁻¹' Metric.closedBall 0 1
  have hT : IsOpen T := isOpen_biInter_finset fun a _ =>
    (IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero).preimage (AlgPoint.continuous_eval a)
  have heq : Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K) =
      affineSchemePointEquiv O U K ⁻¹' T := by
    ext p
    constructor
    · rintro ⟨p₀, rfl⟩
      simp only [T, Set.mem_preimage, Set.mem_iInter, mem_closedBall_zero_iff]
      intro a _
      rw [affineSchemePointEquiv_changeRing]
      exact (hO _).1 (affineSchemePointEquiv O U O p₀ a).2
    · intro hp
      let φ : A →ₐ[O] K := (affineSchemePointEquiv O U K p).toAlgHom
      have hφ : ∀ a ∈ s, φ a ∈ O := by
        intro a ha
        simp only [T, Set.mem_preimage, Set.mem_iInter, mem_closedBall_zero_iff] at hp
        exact (hO _).2 (hp a ha)
      have hall : ∀ a, φ a ∈ O := by
        intro a
        have ha : a ∈ Algebra.adjoin O (s : Set A) := by
          rw [hs]
          exact Algebra.mem_top
        induction ha using Algebra.adjoin_induction with
        | mem x hx => exact hφ x hx
        | algebraMap r =>
          rw [AlgHom.commutes]
          exact r.2
        | add x y _ _ hx hy =>
          rw [map_add]
          exact O.add_mem hx hy
        | mul x y _ _ hx hy =>
          rw [map_mul]
          exact O.mul_mem hx hy
      let ψ : A →ₐ[O] O :=
        { toFun := fun a => ⟨φ a, hall a⟩
          map_one' := Subtype.ext (map_one φ)
          map_mul' := fun a b => Subtype.ext (map_mul φ a b)
          map_zero' := Subtype.ext (map_zero φ)
          map_add' := fun a b => Subtype.ext (map_add φ a b)
          commutes' := fun r => Subtype.ext (φ.commutes r) }
      refine ⟨(affineSchemePointEquiv O U O).symm (AlgPoint.ofAlgHom ψ), ?_⟩
      apply (affineSchemePointEquiv O U K).injective
      rw [affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
      ext a
      rfl
  rw [heq]
  exact isOpen_induced hT

end IntegralPoints

end HenselianUnitBall

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap ringTestMap_left schemePointTopology schemePointContinuity_proof
    ringBaseChange ringPointBaseChangeEquiv schemeBaseChangeTopology_proof)

namespace HenselianIntegralPointsOpen

section LocallyOfFiniteType

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The source of an étale map to a space locally of finite type over the base is locally of
finite type over the base. -/
theorem locallyOfFiniteType_of_isEtale (hX : LocallyOfFiniteTypeOverBase X)
    {U : Over S} (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (ha : IsEtale a) : LocallyOfFiniteType U.hom := by
  obtain ⟨V, b, hb, hbs, hV⟩ := hX.exists_atlas
  let hr := X.representable_from_scheme b
  obtain ⟨g, hg⟩ := (schemeYoneda _).map_surjective (hr.fst a)
  have hsq : IsPullback ((schemeYoneda _).map g) ((schemeYoneda _).map (hr.snd a)) b a := by
    rw [hg]
    exact hr.isPullback a
  have hs : Surjective (hr.snd a).left := hbs.projection a _ _ hsq
  have he : Etale (hr.snd a).left := hb.projection a _ _ hsq
  have hg' : Etale g.left := ha.projection b _ _ hsq.flip
  have : LocallyOfFiniteType ((hr.snd a).left ≫ U.hom) := by
    rw [Over.w (hr.snd a), ← Over.w g]
    infer_instance
  exact locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _ _ _ hs
    inferInstance inferInstance this

end LocallyOfFiniteType

section IntegralChart

variable {O : Type u} [CommRing O] [HenselianLocalRing O]

/-- **Integral points lift to affine étale charts.** Over a henselian local ring `O`, every
`O`-point of an algebraic space over `Spec O` is the image of an `O`-point of an affine
scheme with an étale map to the space. -/
theorem exists_integral_chart_point (X : AlgebraicSpace (Spec (CommRingCat.of O)))
    (x : RingPoints O X O) :
    ∃ (U : Over (Spec (CommRingCat.of O))) (f : (schemeToSpace _).obj U ⟶ X),
      IsAffine U.left ∧ IsEtale (hom f) ∧
        ∃ u : RingPoint O U O, RingPoints.map f ((schemeRingPointsEquiv O U O).symm u) = x := by
  let κ := IsLocalRing.ResidueField O
  have hκ : Function.Surjective (algebraMap O κ) := IsLocalRing.residue_surjective
  obtain ⟨U, f, hU, hf, ū, hū⟩ := FieldPointEtaleLift.exists_affine_etale_point (C := O) (k := κ)
    X (RingPoints.changeRing (Algebra.ofId O κ) x)
  refine ⟨U, f, hU, hf, ?_⟩
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
  -- the residue point of the fibre
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
  -- a section of the étale fibre through the residue point
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

end IntegralChart

section BaseChange

variable {O : Type u} [CommRing O] {K : Type u} [NontriviallyNormedField K] [Algebra O K]

/-- The base-changed chart map, read on `K`-points of the original space. -/
theorem baseChangeRingPointsEquiv_schemePointsMap {X : AlgebraicSpace (Spec (CommRingCat.of O))}
    {U : Over (Spec (CommRingCat.of O))} (f : (schemeToSpace _).obj U ⟶ X)
    (p : RingPoint K (ringBaseChange O K U) K) :
    baseChangeRingPointsEquiv O K K X
        (schemePointsMap (X := baseChange (Spec.algebraMap O K) X)
          (restrictAtlas (Spec.algebraMap O K) (hom f)) p) =
      RingPoints.map f ((schemeRingPointsEquiv O U K).symm
        ((ringPointBaseChangeEquiv O K K U).symm p)) := by
  rw [baseChangeRingPointsEquiv_apply]
  refine (mapSections_naturality f
    (PointTopology.ringTestRestrictScalarsIso O K K).inv _).trans ?_
  change mapSections f _ (ULift.up _) = mapSections f _ (ULift.up _)
  congr 2

end BaseChange

end HenselianIntegralPointsOpen

open HenselianIntegralPointsOpen in
/-- **Conrad's Corollary 5.7, openness.** For a nontrivially normed field `K` whose closed
unit ball is a henselian subring `O`, and an algebraic space `X` locally of finite type over
`Spec O`, the image of `X(O)` in `X_K(K)` is open for the étale-chart topology. The
quasi-separatedness hypothesis of the statement is not used. -/
theorem henselianIntegralPointsOpen : HenselianIntegralPointsOpenStatement.{u} := by
  intro K _ O hO hH X _ hXlft
  have : IsUltrametricDist K := PointTopology.HenselianUnitBall.isUltrametricDist O hO
  have : HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring :=
    PointTopology.HenselianUnitBall.henselianLocalRing_valuationSubring O hO
  let XK := baseChange (Spec.algebraMap O K) X
  let ι : RingPoints O X O → RingPoints K XK K := fun x =>
    (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K) x)
  change IsOpen[etaleChartTopology K XK] (Set.range ι)
  let : TopologicalSpace (RingPoints K XK K) := etaleChartTopology K XK
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, rfl⟩
  obtain ⟨U, f, hU, hf, u, hu⟩ := exists_integral_chart_point X x
  have : LocallyOfFiniteType U.hom :=
    HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale hXlft (hom f) hf
  let UK := ringBaseChange O K U
  have : LocallyOfFiniteType UK.hom := by
    change LocallyOfFiniteType (pullback.snd U.hom (Spec.algebraMap O K))
    infer_instance
  let aK : (schemeYoneda _).obj UK ⟶ XK.presheaf :=
    restrictAtlas (Spec.algebraMap O K) (hom f)
  have haK : IsEtale aK := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := hf
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap O K) (@Etale.{u}) h
  let S₀ : Set (RingPoint O U K) :=
    Set.range (RingPoint.changeRing (Algebra.ofId O K) : RingPoint O U O → RingPoint O U K)
  have hS₀ : IsOpen[schemePointTopology O U K] S₀ :=
    PointTopology.HenselianUnitBall.isOpen_range_changeRing O hO U
  have he := schemeBaseChangeTopology_proof O K K U
  have hcompat : ∀ v : RingPoint O U O,
      schemePointsMap aK (ringPointBaseChangeEquiv O K K U (v.changeRing (Algebra.ofId O K))) =
        ι (RingPoints.map f ((schemeRingPointsEquiv O U O).symm v)) := by
    intro v
    apply (baseChangeRingPointsEquiv O K K X).injective
    refine (baseChangeRingPointsEquiv_schemePointsMap f _).trans ?_
    rw [Equiv.symm_apply_apply]
    change _ = baseChangeRingPointsEquiv O K K X ((baseChangeRingPointsEquiv O K K X).symm _)
    rw [Equiv.apply_symm_apply, RingPoints.changeRing_map]
    rfl
  refine ⟨schemePointsMap aK '' (ringPointBaseChangeEquiv O K K U '' S₀), ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, (hcompat v).symm⟩
  · exact isOpenMap_schemePointsMap_of_etaleOpen
      (fun _ _ _ _ g _ => PointTopology.HenselianUnitBall.isOpenMap_smoothSchemePointMap K g)
      aK haK _ (@IsHomeomorph.isOpenMap _ _ (schemePointTopology O U K)
        (schemePointTopology K (ringBaseChange O K U) K) _ he _ hS₀)
  · refine ⟨ringPointBaseChangeEquiv O K K U (u.changeRing (Algebra.ofId O K)), ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩
    rw [hcompat, hu]

end Langlands.AlgebraicGeometry.AlgebraicSpace
