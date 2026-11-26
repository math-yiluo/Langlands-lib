import Langlands.Global.AdelicCyclicDistributionVectorReduction
import Langlands.Global.AdelicSplitCentreUnitaryCharacter
import Langlands.Global.AdelicArchimedeanFiniteWeights
import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Representation.Archimedean.ProductSmoothInfinitesimalCharacter
import Langlands.Representation.Archimedean.FixedCompactFiniteChoice

/-!
# Matrix coefficients of distribution vectors are generalized eigenfunctions

This module proves `IrreducibleDistributionVectorAutomorphyStatement`: a nonzero distribution
vector `ξ` of a topologically irreducible unitary representation `ρ` of `G(𝔸)` has a matrix
coefficient `g ↦ ξ (ρ g v)` that is smooth, `K_∞`-finite, `𝔷`-finite, transforms under `A_G` by a
unitary character `a ↦ a^{iν}` and is not identically zero.

`irreducibleDistributionVectorAutomorphy_of_centerConjugation` derives the statement from
`AdelicEnvelopingCenterConjugationStatement` (`Ad(G(F_∞))` fixes the center of the enveloping
algebra); the theorem `irreducibleDistributionVectorAutomorphy` combines it with the proof
`adelicEnvelopingCenterConjugation` of that statement.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff InnerProductSpace TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Archimedean Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The reduction of `IrreducibleDistributionVectorAutomorphyStatement` to the invariance of the
center of the enveloping algebra under `Ad(G(F_∞))`. -/
theorem irreducibleDistributionVectorAutomorphy_of_centerConjugation
    (hAd : AdelicEnvelopingCenterConjugationStatement.{0}) :
    IrreducibleDistributionVectorAutomorphyStatement := by
  classical
  intro F _ _ G _ _ _ hred K d hsmooth hcalc hKmax
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  intro V _ _ _ ρ ξ ρinf Vsm IsSmooth hunit hcont hirr hξ hne
  have hLie : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (InfiniteAdelicGroupPoints F G) := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  have : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let ιinf : InfiniteAdelicGroupPoints F G →* AdelicGroupPoints F G := (ofInfinite F G).toMonoidHom
  let ιfin : FiniteAdelicGroupPoints F G →* AdelicGroupPoints F G := (ofFinite F G).toMonoidHom
  have hcomm : ∀ a b, Commute (ιinf a) (ιfin b) := fun a b => factors_commute F G a b
  have hgen : ∀ x : AdelicGroupPoints F G, ∃ a b, x = ιinf a * ιfin b := by
    intro x
    refine ⟨infinite F G x, finite F G x, ?_⟩
    change x = pair F G (infinite F G x) 1 * pair F G 1 (finite F G x)
    rw [pair_mul, mul_one, one_mul]
    exact (pair_projections F G x).symm
  have hunit' : ∀ x u w, ⟪ρ x u, ρ x w⟫_ℂ = ⟪u, w⟫_ℂ := fun x =>
    (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mpr
      (Unitary.star_mul_self_of_mem (hunit x))
  have hξ' : ProductSmoothVectors.IsDistributionForm
      (A := InfiniteAdelicGroupPoints.smoothModel F d) ιinf ιfin ρ ξ := hξ
  have hσcomm : ∀ g l w, ρinf g ((ρ.comp ιfin) l w) = (ρ.comp ιfin) l (ρinf g w) :=
    fun g l w => (ProductSmoothVectors.finite_comm ιinf ιfin ρ hcomm l g w).symm
  -- the compact subgroup `K_∞`
  obtain ⟨v₀, ⟨hv₀s, L, hL, hv₀L⟩, hξv₀⟩ := hne
  obtain ⟨S, C, hSC⟩ := hξ L hL
  set Kinf := K.comap (ofInfinite F G).toMonoidHom with hKinf
  have hKc : IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G)) := by
    have he : (Kinf : Set (InfiniteAdelicGroupPoints F G)) =
        infinite F G '' ((K : Set (AdelicGroupPoints F G)) ∩ finite F G ⁻¹' {1}) := by
      ext a
      constructor
      · intro ha
        exact ⟨ofInfinite F G a, ⟨ha, finite_ofInfinite F G a⟩, infinite_ofInfinite F G a⟩
      · rintro ⟨g, ⟨hg, hg1⟩, rfl⟩
        change ofInfinite F G (infinite F G g) ∈ K
        have : ofInfinite F G (infinite F G g) = g := by
          rw [ofInfinite_eq_pair, ← hg1, pair_projections]
        rw [this]
        exact hg
    rw [he]
    exact (hKmax.1.inter_right (isClosed_singleton.preimage (finite F G).continuous)).image
      (infinite F G).continuous
  have : CompactSpace Kinf := isCompact_iff_compactSpace.mp hKc
  -- a faithful continuous finite-dimensional representation of `K_∞`
  obtain ⟨N, rho, hrho⟩ := affineLinearEmbeddingStatement_viaCorepresented F G
    (inferInstance : IsAffineHom G.X.hom) (inferInstance : LocallyOfFiniteType G.X.hom)
  have : IsClosedImmersion rho.hom.hom.left := hrho
  let τ : Representation ℂ Kinf (Fin N × NumberField.InfinitePlace F → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin N × NumberField.InfinitePlace F)
      (Fin N × NumberField.InfinitePlace F) ℂ ≃ₐ[ℂ] _).toAlgHom.toRingHom.toMonoidHom.comp
      ((placeMatrixRingHom F N).toMonoidHom.comp ((Units.coeHom _).comp
        ((RepresentationGrowth.infiniteMatrix F G rho).toMonoidHom.comp Kinf.subtype)))
  have hτ : ∀ w, Continuous fun k => τ k w := by
    intro w
    change Continuous fun k : Kinf => (placeMatrixRingHom F N
      (RepresentationGrowth.infiniteMatrix F G rho (k : InfiniteAdelicGroupPoints F G) :
        Matrix (Fin N) (Fin N) (NumberField.InfiniteAdeleRing F))).mulVec w
    simp only [placeMatrixRingHom_apply]
    apply Continuous.matrix_mulVec _ continuous_const
    apply Continuous.matrix_blockDiagonal
    apply continuous_pi
    intro v
    apply Continuous.matrix_map _ (continuous_placeRingHom F v)
    exact Units.continuous_val.comp ((RepresentationGrowth.infiniteMatrix F G rho).continuous.comp
      continuous_subtype_val)
  have hinj : Function.Injective τ := by
    intro k k' hkk'
    have h1 : placeMatrixRingHom F N
          (RepresentationGrowth.infiniteMatrix F G rho (k : InfiniteAdelicGroupPoints F G) :
            Matrix (Fin N) (Fin N) (NumberField.InfiniteAdeleRing F)) =
        placeMatrixRingHom F N
          (RepresentationGrowth.infiniteMatrix F G rho (k' : InfiniteAdelicGroupPoints F G) :
            Matrix (Fin N) (Fin N) (NumberField.InfiniteAdeleRing F)) :=
      (Matrix.toLinAlgEquiv' : Matrix (Fin N × NumberField.InfinitePlace F)
        (Fin N × NumberField.InfinitePlace F) ℂ ≃ₐ[ℂ] _).injective hkk'
    exact Subtype.ext (infiniteMatrix_injective F G rho
      (Units.ext (placeMatrixRingHom_injective F N h1)))
  let r : Kinf →ₜ* InfiniteAdelicGroupPoints F G :=
    { toMonoidHom := Kinf.subtype, continuous_toFun := continuous_subtype_val }
  -- a `K_∞`-finite smooth vector on which `ξ` does not vanish
  obtain ⟨v, hvs, hvL, hξv, hvfin⟩ := FixedCompactFiniteChoice.exists_compactFinite_ne_zero
    (ρ.comp ιfin) L ρinf hσcomm r τ hτ hinj ξ S C
    (fun w hw hwL => hSC w hw (fun l hl => hwL ⟨l, hl⟩)) hv₀s (fun j => hv₀L j j.2) hξv₀
  have hvW : v ∈ ProductSmoothVectors.smoothSubspace (InfiniteAdelicGroupPoints.smoothModel F d)
      ιinf ιfin ρ := ⟨hvs, L, hL, fun l hl => hvL ⟨l, hl⟩⟩
  have hv0 : v ≠ 0 := fun h => hξv (by rw [h, map_zero])
  have hWne : ProductSmoothVectors.smoothSubspace (InfiniteAdelicGroupPoints.smoothModel F d)
      ιinf ιfin ρ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, hvW, hv0⟩
  -- the slices of the matrix coefficient
  have hslice : ∀ b, functionInfiniteSlice F G (fun g => ξ (ρ g v)) b =
      fun a => ξ (ρ (ιinf a * ιfin b) v) := by
    intro b
    funext a
    change ξ (ρ (pair F G a b) v) = ξ (ρ (pair F G a 1 * pair F G 1 b) v)
    rw [pair_mul, mul_one, one_mul]
  have hsm : ∀ b, functionInfiniteSlice F G (fun g => ξ (ρ g v)) b ∈
      InfinitePlotSmoothFunctions F G := by
    intro b
    rw [hslice b]
    exact (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
      (ProductSmoothVectors.coefficient_contMDiff ιinf ιfin ρ hcomm hunit' ξ hξ' v hvW b)
  have hinvL : ∀ l ∈ L, ∀ g : AdelicGroupPoints F G,
      ξ (ρ (g * ofFinite F G l) v) = ξ (ρ g v) := by
    intro l hl g
    rw [map_mul, mul_apply_eq_comp]
    congr 2
    exact hvL ⟨l, hl⟩
  refine ⟨v, ⟨hvs, L, hL, fun l hl => hvL ⟨l, hl⟩⟩, ?_, ?_, ?_, ?_, ⟨1, by simpa using hξv⟩⟩
  · -- smoothness
    refine ⟨?_, hsm, L, hL, hinvL⟩
    let s : FiniteAdelicGroupPoints F G → InfinitePlotSmoothFunctions F G := fun b => ⟨_, hsm b⟩
    have hs : ∀ (b : FiniteAdelicGroupPoints F G) (l : (⟨L, hL⟩ : OpenSubgroup _)),
        s (b * l.val) = s b := by
      intro b l
      apply Subtype.ext
      funext a
      change ξ (ρ (pair F G a (b * l.val)) v) = ξ (ρ (pair F G a b) v)
      have hp : pair F G a (b * l.val) = pair F G a b * ofFinite F G l.val := by
        rw [ofFinite_eq_pair, pair_mul, mul_one]
      rw [hp]
      exact hinvL l.val l.2 _
    have hcs := continuous_evaluatePlotSmoothSlices F G hsmooth s ⟨L, hL⟩ hs
    convert hcs using 1
    funext x
    change ξ (ρ x v) = ξ (ρ (pair F G (infinite F G x) (finite F G x)) v)
    rw [pair_projections]
  · -- finiteness under `K_∞`
    let T : V →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
      { toFun := fun w g => ξ (ρ g w)
        map_add' := fun w w' => by funext g; simp
        map_smul' := fun c w => by funext g; simp }
    have hrange : (Set.range fun k : Kinf =>
        fun g : AdelicGroupPoints F G => ξ (ρ (g * ofInfinite F G k) v)) =
        T '' Set.range (fun k : Kinf =>
          (CompactSmoothFiniteDensity.restrictedRepresentation ρinf r) k v) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      funext g
      simp [T, r, ρinf, map_mul, mul_apply_eq_comp]
    unfold IsInfiniteSubgroupFiniteFunction
    rw [hrange, Submodule.span_image]
    have : Module.Finite ℂ (Submodule.span ℂ (Set.range fun k : Kinf =>
      (CompactSmoothFiniteDensity.restrictedRepresentation ρinf r) k v)) := hvfin
    exact Module.Finite.map _ _
  · -- `𝔷`-finiteness
    let D := SmoothVectorEnveloping.envelopingAction ρinf hcalc
    let v' : Langlands.Archimedean.smoothVectors 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ρinf := ⟨v, hvs⟩
    have hseg : ∀ z : AdelicEnvelopingCenter F G hsmooth, ∃ c : ℂ, (D z.val v' : V) = c • v := by
      intro z
      obtain ⟨c, hc⟩ := ProductSmoothVectors.exists_smul_of_adjointInvariant ιinf ιfin ρ hcomm
        hcalc hgen hunit' hirr hWne z.val
        (fun g => ⟨adelicEnvelopingConjugation F G hsmooth g,
          fun c X => adelicEnvelopingConjugation_ι_tmul F G hsmooth g c X,
          hAd F G hsmooth hred g z.val z.property⟩)
      exact ⟨c, hc ⟨v, hvW⟩⟩
    let ψ : AdelicEnvelopingCenter F G hsmooth →ₗ[ℂ] V :=
      { toFun := fun z => (D z.val v' : V)
        map_add' := fun z z' => by
          simp only [Subalgebra.coe_add, map_add, LinearMap.add_apply, Submodule.coe_add]
        map_smul' := fun c z => by
          simp only [Subalgebra.coe_smul, map_smul, LinearMap.smul_apply, Submodule.coe_smul,
            RingHom.id_apply] }
    let J : Ideal (AdelicEnvelopingCenter F G hsmooth) :=
      { carrier := {z | (D z.val v' : V) = 0}
        add_mem' := fun {z z'} hz hz' => by
          change (D (z + z').val v' : V) = 0
          simp only [Subalgebra.coe_add, map_add, LinearMap.add_apply, Submodule.coe_add]
          rw [show (D z.val v' : V) = 0 from hz, show (D z'.val v' : V) = 0 from hz', add_zero]
        zero_mem' := by
          change (D (0 : AdelicEnvelopingCenter F G hsmooth).val v' : V) = 0
          simp
        smul_mem' := fun c z hz => by
          change (D (c * z).val v' : V) = 0
          have hz0 : D z.val v' = 0 := Subtype.ext hz
          simp only [Subalgebra.coe_mul, map_mul, Module.End.mul_apply, hz0, map_zero]
          rfl }
    refine ⟨J, ?_, ?_⟩
    · have hJ : J.restrictScalars ℂ = LinearMap.ker ψ := by
        ext z
        rfl
      rw [hJ]
      have hle : LinearMap.range ψ ≤ ℂ ∙ v := by
        rintro _ ⟨z, rfl⟩
        obtain ⟨c, hc⟩ := hseg z
        exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
      have : FiniteDimensional ℂ (LinearMap.range ψ) := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.equiv ψ.quotKerEquivRange.symm
    · intro z hz b h
      have hz0 : D z.val v' = 0 := Subtype.ext hz
      have hSmem : ∀ f : InfiniteAdelicGroupPoints F G → ℂ,
          ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞ f →
            f ∈ InfinitePlotSmoothFunctions F G :=
        fun f hf => (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth f).mpr hf
      have hΘ : ∀ (X : GroupLieAlgebra 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
            (InfiniteAdelicGroupPoints F G)) (f : InfinitePlotSmoothFunctions F G),
          ((InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth hcalc
            (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) f :
              InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) =
            groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) X f := by
        intro X f
        rw [InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction_real_generator]
        rfl
      have hmem : (fun a => ξ (ρ (ιinf a * ιfin b) v)) ∈ InfinitePlotSmoothFunctions F G :=
        hslice b ▸ h
      have hT := ProductSmoothVectors.coefficient_envelopingAction ιinf ιfin ρ hcomm hcalc hunit' ξ
        hξ' (InfinitePlotSmoothFunctions F G) hSmem
        (InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth hcalc) hΘ v hvW b z.val
        hmem
      have hsub : (⟨functionInfiniteSlice F G (fun g => ξ (ρ g v)) b, h⟩ :
          InfinitePlotSmoothFunctions F G) = ⟨fun a => ξ (ρ (ιinf a * ιfin b) v), hmem⟩ :=
        Subtype.ext (hslice b)
      apply Subtype.ext
      change ((InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth hcalc z.val
        ⟨functionInfiniteSlice F G (fun g => ξ (ρ g v)) b, h⟩ :
          InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) = 0
      rw [hsub, hT]
      funext a
      change ξ (ρ (ιinf a * ιfin b) (D z.val v' : V)) = 0
      rw [hz0]
      simp
  · -- the character of `A_G`
    have hscalar : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G,
        ∃ m₀ : ℂ, ρ a = m₀ • ContinuousLinearMap.id ℂ V := by
      intro a ha
      apply exists_eq_scalar_of_unitary_commute ρ hunit' hirr (ρ a)
      intro g
      have hc := RestrictionSplitCentre.canonicalSubgroup_le_center F G ha
      change ρ a * ρ g = ρ g * ρ a
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc g)]
    have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv0
    let c : AdelicGroupPoints F G → ℂ := fun a => ⟪v, ρ a v⟫_ℂ / ⟪v, v⟫_ℂ
    have hcw : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ w : V,
        ρ a w = c a • w := by
      intro a ha w
      obtain ⟨m₀, hm₀⟩ := hscalar a ha
      have hm₀v : c a = m₀ := by
        change ⟪v, ρ a v⟫_ℂ / ⟪v, v⟫_ℂ = m₀
        rw [hm₀]
        change ⟪v, m₀ • v⟫_ℂ / ⟪v, v⟫_ℂ = m₀
        rw [inner_smul_right, mul_div_assoc, div_self hvv, mul_one]
      rw [hm₀v, hm₀]
      rfl
    have hccont : Continuous c := by
      have h1 : Continuous fun a : AdelicGroupPoints F G => ρ a v :=
        hcont.comp (continuous_id.prodMk continuous_const)
      exact (continuous_const.inner h1).div_const _
    have hcmul : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G,
        ∀ b ∈ RestrictionSplitCentre.canonicalSubgroup F G, c (a * b) = c a * c b := by
      intro a ha b hb
      have h1 := hcw (a * b) (Subgroup.mul_mem _ ha hb) v
      rw [map_mul, mul_apply_eq_comp, hcw b hb, map_smul, hcw a ha, smul_smul] at h1
      exact smul_left_injective ℂ hv0 (h1.symm.trans (by rw [mul_comm]))
    have hcnorm : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ‖c a‖ = 1 := by
      intro a ha
      have h1 : ‖ρ a v‖ = ‖v‖ := by
        have h := hunit' a v v
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
        have h' : ‖ρ a v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
      rw [hcw a ha, norm_smul] at h1
      have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      field_simp at h1
      exact h1
    obtain ⟨ν, hν⟩ := RestrictionSplitCentre.exists_realParameter_of_unitary F G hred c hccont
      hcmul hcnorm
    refine ⟨ν, fun a ha g => ?_⟩
    rw [map_mul, mul_apply_eq_comp, hcw a ha, map_smul, smul_eq_mul, hν a ha]

/-- **Matrix coefficients of distribution vectors of irreducible unitary representations of
`G(𝔸)` are generalized eigenfunctions** (`IrreducibleDistributionVectorAutomorphyStatement`). -/
theorem irreducibleDistributionVectorAutomorphy : IrreducibleDistributionVectorAutomorphyStatement :=
  irreducibleDistributionVectorAutomorphy_of_centerConjugation adelicEnvelopingCenterConjugation.{0}

end Langlands.Global
