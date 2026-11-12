import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianNormedExtensionEmbedding
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantRadical
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Mathlib.RingTheory.Etale.Field

/-! # Coefficient automorphisms and finite Galois closed extension loci -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite Topology Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace ExtensionClosedRange

/-- Finite Galois invariant points of a separated algebraic space descend. -/
theorem exists_desc_of_finite_galois_fixed
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hs : IsSeparated X)
    (x : RingPoints K X L)
    (hx : ∀ σ : L ≃ₐ[K] L, RingPoints.changeRing σ.toAlgHom x = x) :
    ∃ y : RingPoints K X K, RingPoints.changeRing (Algebra.ofId K L) y = x := by
  change X.sections (ringTest K L) at x
  change ∀ σ : L ≃ₐ[K] L, X.pullback (ringTestMap K σ.toAlgHom) x = x at hx
  let π := ringTestMap K (Algebra.ofId K L)
  have : Flat π.left := inferInstanceAs (Flat (specOver K L).hom)
  have : LocallyOfFinitePresentation π.left :=
    inferInstanceAs (LocallyOfFinitePresentation (specOver K L).hom)
  have : Surjective π.left := inferInstanceAs (Surjective (specOver K L).hom)
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FinitePresentation K L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K L := {}
  have : Etale π.left := by
    change Etale (Spec.algebraMap K L)
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let P := Limits.pullback π π
  let p₁ : P ⟶ ringTest K L := pullback.fst π π
  let p₂ : P ⟶ ringTest K L := pullback.snd π π
  have hP : IsPullback p₁ p₂ π π := IsPullback.of_hasPullback π π
  have hPs := hP.map (Over.forget (Spec (CommRingCat.of K)))
  change IsPullback p₁.left p₂.left π.left π.left at hPs
  have : Etale p₁.left := MorphismProperty.of_isPullback hPs.flip ‹Etale π.left›
  have : IsReduced P.left :=
    @Langlands.AlgebraicGeometry.EtaleReduced.isReduced_of_etale_to_field P.left L _
      p₁.left ‹Etale p₁.left›
  have heq : X.pullback p₁ x = X.pullback p₂ x := by
    obtain ⟨Z, j, hj, hcl⟩ := exists_representsEqualizer_of_relative_diag
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hs
      (X.pullback p₁ x) (X.pullback p₂ x)
    have : _root_.AlgebraicGeometry.IsClosedImmersion j.left := hcl
    have : Surjective j.left := by
      constructor
      intro t
      let R : Type u := P.left.residueField t
      let T : Over (Spec (CommRingCat.of K)) :=
        Over.mk (P.left.fromSpecResidueField t ≫ P.hom)
      let r : T ⟶ P := Over.homMk (P.left.fromSpecResidueField t)
      obtain ⟨σ, hσ⟩ := exists_galois_of_hom T.hom (r ≫ p₁) (r ≫ p₂)
      have hσmap : Langlands.AlgebraicGeometry.Picard.DualNumberDouble.specOverMap
          σ.toAlgHom = ringTestMap K σ.toAlgHom := by
        apply Over.OverMorphism.ext
        rfl
      rw [hσmap] at hσ
      have hr : X.pullback r (X.pullback p₁ x) = X.pullback r (X.pullback p₂ x) := by
        calc
          X.pullback r (X.pullback p₁ x) = X.pullback (r ≫ p₁) x :=
            (pullback_comp X r p₁ x).symm
          _ = X.pullback ((r ≫ p₁) ≫ ringTestMap K σ.toAlgHom) x :=
            (congrArg (X.pullback (r ≫ p₁)) (hx σ).symm).trans
              (pullback_comp X (r ≫ p₁) (ringTestMap K σ.toAlgHom) x).symm
          _ = X.pullback (r ≫ p₂) x :=
            congrArg (fun f : T ⟶ ringTest K L => X.pullback f x) hσ.symm
          _ = X.pullback r (X.pullback p₂ x) := pullback_comp X r p₂ x
      obtain ⟨w, hw⟩ := (hj r).2 hr
      refine ⟨w.left (default : Spec (CommRingCat.of R)), ?_⟩
      have h := congrArg (fun f : T ⟶ P => f.left (default : Spec (CommRingCat.of R))) hw
      exact h.trans (P.left.fromSpecResidueField_apply t _)
    have : IsIso j.left := isIso_of_isClosedImmersion_of_surjective j.left
    let s : P ⟶ Z := Over.homMk (inv j.left) (by
      rw [IsIso.inv_comp_eq, ← Over.w j])
    have hs' : s ≫ j = 𝟙 _ := by
      apply Over.OverMorphism.ext
      change inv j.left ≫ j.left = 𝟙 P.left
      simp
    have h := (hj (𝟙 _)).1 ⟨s, hs'⟩
    simpa only [op_id, X.presheaf.map_id, types_id_apply] using h
  exact ProductPointsDescent.exists_pullback_eq X π hP x heq

section Topology

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- A chart of the original space evaluated over the extension field. -/
abbrev chartExtensionMap (c : EtaleFiniteTypeChart K X) :
    RingPoint K c.scheme L → RingPoints L (baseChange (Spec.algebraMap K L) X) L :=
  c.fieldExtension.pointMap ∘ PointTopology.ringPointBaseChangeEquiv K L L c.scheme

theorem chartExtensionMap_eval (c : EtaleFiniteTypeChart K X) (v : RingPoint K c.scheme L) :
    baseChangeRingPointsEquiv K L L X (chartExtensionMap c v) =
      RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme L).symm v) := by
  rw [chartExtensionMap, Function.comp_apply,
    baseChangeRingPointsEquiv_fieldExtension_pointMap, Equiv.symm_apply_apply]

/-- Charts defined over the original field cover all extension-valued points. -/
theorem exists_chartExtensionMap_eq (hX : LocallyOfFiniteTypeOverBase X)
    (z : RingPoints L (baseChange (Spec.algebraMap K L) X) L) :
    ∃ (c : EtaleFiniteTypeChart K X) (v : RingPoint K c.scheme L), chartExtensionMap c v = z := by
  obtain ⟨U, a, hU, ha, v, hv⟩ :=
    FieldPointEtaleLift.exists_affine_etale_point X (baseChangeRingPointsEquiv K L L X z)
  let := hU
  have hlft := locallyOfFiniteType_of_isEtale hX (hom a) ha
  let c : EtaleFiniteTypeChart K X := ⟨U, a, ha, hlft, inferInstance⟩
  refine ⟨c, v, (baseChangeRingPointsEquiv K L L X).injective ?_⟩
  rw [chartExtensionMap_eval]
  exact hv

/-- The action of a coefficient automorphism on the actual base-changed point carrier. -/
def coefficientAut (σ : L ≃ₐ[K] L) :
    RingPoints L (baseChange (Spec.algebraMap K L) X) L →
      RingPoints L (baseChange (Spec.algebraMap K L) X) L :=
  fun z => (baseChangeRingPointsEquiv K L L X).symm
    (RingPoints.changeRing σ.toAlgHom (baseChangeRingPointsEquiv K L L X z))

theorem coefficientAut_chartExtensionMap (σ : L ≃ₐ[K] L)
    (c : EtaleFiniteTypeChart K X) (v : RingPoint K c.scheme L) :
    coefficientAut σ (chartExtensionMap c v) =
      chartExtensionMap c (PointTopology.RingPoint.changeRing σ.toAlgHom v) := by
  apply (baseChangeRingPointsEquiv K L L X).injective
  rw [coefficientAut, Equiv.apply_symm_apply, chartExtensionMap_eval,
    chartExtensionMap_eval, RingPoints.changeRing_map]
  rfl

/-- An isometric coefficient automorphism is continuous on algebraic-space points. -/
theorem continuous_coefficientAut (hL : IsHenselianValuedField L)
    (hX : LocallyOfFiniteTypeOverBase X) (σ : L ≃ₐ[K] L) (hσ : Isometry σ) :
    @Continuous _ _ (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X)) (coefficientAut σ (X := X)) := by
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  refine ⟨fun W hW => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨c, v, hv⟩ := exists_chartExtensionMap_eq hX z
  let : TopologicalSpace (RingPoint K c.scheme L) := schemePointTopology K c.scheme L
  let : TopologicalSpace (RingPoint L c.fieldExtension.scheme L) :=
    schemePointTopology L c.fieldExtension.scheme L
  have he := PointTopology.schemeBaseChangeTopology_proof K L L c.scheme
  have hqopen : IsOpenMap (chartExtensionMap (L := L) c) :=
    (c.fieldExtension.isOpenMap_pointMap hL).comp he.isOpenMap
  have hqcont : Continuous (chartExtensionMap (L := L) c) :=
    c.fieldExtension.continuous_pointMap.comp he.continuous
  have hcont : Continuous (coefficientAut σ (X := X) ∘ chartExtensionMap c) := by
    have heq : coefficientAut σ (X := X) ∘ chartExtensionMap c =
        chartExtensionMap c ∘ PointTopology.RingPoint.changeRing σ.toAlgHom :=
      funext (coefficientAut_chartExtensionMap σ c)
    rw [heq]
    exact hqcont.comp (PointTopology.schemeCoefficientContinuity_proof K L L
      c.scheme σ.toAlgHom hσ.continuous)
  refine ⟨chartExtensionMap c '' ((coefficientAut σ (X := X) ∘ chartExtensionMap c) ⁻¹' W),
    ?_, hqopen _ (hW.preimage hcont), ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hw
  · refine ⟨v, ?_, hv⟩
    change coefficientAut σ (chartExtensionMap c v) ∈ W
    rwa [hv]

/-- For finite Galois extensions, the rational locus is the closed fixed-point locus. -/
theorem isClosed_range_of_finite_galois [FiniteDimensional K L] [IsGalois K L]
    (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    IsClosed[etaleChartTopology L (baseChange (Spec.algebraMap K L) X)]
      (Set.range (extensionPointMap L X)) := by
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  have hXL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) X) :=
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have : T2Space (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    t2Space_etaleChartTopology hL hXL hs.baseChange
  have hr : Set.range (extensionPointMap L X) =
      ⋂ σ : L ≃ₐ[K] L, {z | coefficientAut σ (X := X) z = z} := by
    ext z
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, rfl⟩ σ
      apply (baseChangeRingPointsEquiv K L L X).injective
      rw [coefficientAut, Equiv.apply_symm_apply, extensionPointMap, Equiv.apply_symm_apply,
        RingPoints.changeRing_comp]
      congr 1
      ext
    · intro hz
      obtain ⟨y, hy⟩ := exists_desc_of_finite_galois_fixed hs
        (baseChangeRingPointsEquiv K L L X z) (fun σ => by
          have h := congrArg (baseChangeRingPointsEquiv K L L X) (hz σ)
          simpa only [coefficientAut, Equiv.apply_symm_apply] using h)
      refine ⟨y, (baseChangeRingPointsEquiv K L L X).injective ?_⟩
      rw [extensionPointMap, Equiv.apply_symm_apply, hy]
  rw [hr]
  exact isClosed_iInter fun σ => isClosed_eq
    (continuous_coefficientAut hL hX.2 σ (FiniteExtensionEmbedding.isometry_aut hK σ)) continuous_id

/-- The embedding with its closed-image proof in the finite Galois case. -/
theorem isClosedEmbedding_of_finite_galois [FiniteDimensional K L] [IsGalois K L]
    (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    @IsClosedEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (extensionPointMap L X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  exact ⟨isEmbedding_henselianExtensionPointMap hK hL hX hs,
    isClosed_range_of_finite_galois hK hL hX hs⟩

end Topology

end ExtensionClosedRange
end Langlands.AlgebraicGeometry.AlgebraicSpace
