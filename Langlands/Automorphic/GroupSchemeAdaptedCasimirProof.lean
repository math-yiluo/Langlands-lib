import Langlands.Automorphic.GroupSchemeAdaptedCasimirStatement
import Langlands.Geometry.Manifold.AdaptedCasimirAssembly
import Langlands.Global.InfiniteAdelicChartFormula
import Langlands.Global.InfinitePlaceMatrixRealization
import Langlands.Group.MatrixCartanInvolution
import Langlands.Group.PolynomialStarCompactConjugacy
import Langlands.Group.ClosedPolarCompact
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage

/-! # Proof of the adapted Casimir statement on the infinite adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints
open Langlands.GroupScheme

section Entries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {K : Type*} [RCLike K] {n : Type*} [Fintype n]

/-- Entries of `P * f x * Q` are smooth when the entries of `f` are. -/
theorem contMDiff_mul_entries {f : M → Matrix n n K}
    (hf : ∀ i j, ContMDiff I 𝓘(ℝ, K) ∞ (fun x => f x i j)) (P Q : Matrix n n K) (i j : n) :
    ContMDiff I 𝓘(ℝ, K) ∞ (fun x => (P * f x * Q) i j) := by
  have hpi : ContMDiff I 𝓘(ℝ, n → n → K) ∞ (fun x => fun a b => f x a b) :=
    contMDiff_pi_space.mpr fun a => contMDiff_pi_space.mpr fun b => hf a b
  let L : (n → n → K) →L[ℝ] K := ∑ a, ∑ b,
    (ContinuousLinearMap.mulLeftRight ℝ K (P i a) (Q b j)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => K) b).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => n → K) a))
  have hL : ∀ x, (P * f x * Q) i j = L (fun a b => f x a b) := by
    intro x
    simp only [L, Matrix.mul_apply, Finset.sum_mul, _root_.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    rw [Finset.sum_comm]
  simp_rw [hL]
  exact (L.contDiff (n := ∞)).contMDiff.comp hpi

end Entries

section RangeTransport

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]
  {X Y : Type*} [Group X] [Group Y]

theorem star_mem_range_of_range_eq (f : X →* GL n 𝕜) (g : Y →* GL n 𝕜) (h : f.range = g.range)
    (hg : ∀ q ∈ g.range, star q ∈ g.range) : ∀ q ∈ f.range, star q ∈ f.range := by
  rw [h]
  exact hg

theorem isPolynomiallyDefined_range_of_range_eq (f : X →* GL n 𝕜) (g : Y →* GL n 𝕜)
    (h : f.range = g.range)
    (hg : Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined g.range) :
    Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined f.range := by
  rw [h]
  exact hg

end RangeTransport

section CartanSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {X : Type*} [Group X]
  (R : X →* GL (Fin n) 𝕜) (hR : Function.Injective R)
  (hstar : ∀ g ∈ R.range, star g ∈ R.range) (a : GL (Fin n) 𝕜) (ha : a ∈ R.range)

/-- The entries of the Cartan involution of a family are smooth when the entries of the family
and of its inverse are. -/
theorem contMDiff_cartan_entries {f : M → X}
    (hfinv : ∀ i j, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun m => (R (f m)⁻¹).val i j)) (i j : Fin n) :
    ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun m =>
      (R (Langlands.Group.MatrixCartanInvolution.cartan R hR hstar a ha (f m))).val i j) := by
  have hstarent (k l : Fin n) : ContMDiff I 𝓘(ℝ, 𝕜) ∞
      (fun m => ((R (f m)⁻¹).val)ᴴ k l) := by
    simp only [Matrix.conjTranspose_apply]
    have h := ((RCLike.conjCLE (K := 𝕜) : 𝕜 →L[ℝ] 𝕜).contDiff (n := ∞)).contMDiff.comp
      (hfinv l k)
    convert h using 2 with m
    simp [RCLike.conjCLE_apply, RCLike.star_def]
  have h := contMDiff_mul_entries hstarent
    (Langlands.Group.MatrixCartanInvolution.cartanCenter a).val
    ((Langlands.Group.MatrixCartanInvolution.cartanCenter a)⁻¹).val i j
  convert h using 2 with m
  rw [Langlands.Group.MatrixCartanInvolution.val_map_cartan]

end CartanSmooth

set_option synthInstance.maxHeartbeats 200000 in
/-- **The adapted Casimir element on the infinite adelic points.** -/
theorem adelicAdaptedCasimir : AdelicAdaptedCasimirStatement.{u} := by
  intro F _ _ G _ Kinf d hsmooth hG hK
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  have : LieGroup 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothLieGroup F G hsmooth
  have : IsTopologicalGroup (InfiniteAdelicGroupPoints F G) :=
    G.affinePointsIsTopologicalGroup (CommAlgCat.of F (InfiniteAdeleRing F))
  -- the place-wise closed self-adjoint realizations
  have hGv (v : NumberField.InfinitePlace F) :
      IsConnectedReductive (InfinitePlaceGroupPoints.completionBaseChange F G v) :=
    InfinitePlaceGroupPoints.isConnectedReductive_completionBaseChange F G hG v
  have hdata (v : NumberField.InfinitePlace F) := SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement
    v.Completion (InfinitePlaceGroupPoints.completionBaseChange F G v) (hGv v)
  choose N ρ hρclosed hρstar using hdata
  have hρ (v : NumberField.InfinitePlace F) := And.intro (hρclosed v) (hρstar v)
  let := fun v : NumberField.InfinitePlace F =>
    (InfinitePlaceGroupPoints.completionBaseChange F G v).affinePointsTopologicalSpace
      (CommAlgCat.of v.Completion v.Completion)
  let R : ∀ v, InfinitePlaceGroupPoints F G v →* GL (Fin (N v)) v.Completion := fun v =>
    InfinitePlaceGroupPoints.realizationMatrix F G v (ρ v)
  have hRce (v : NumberField.InfinitePlace F) : Topology.IsClosedEmbedding (R v) :=
    ((ρ v).isClosedEmbedding_affineMatrix (CommAlgCat.of v.Completion v.Completion)
      (hρ v).1).comp
      (InfinitePlaceGroupPoints.completionBaseChangeHomeomorph F G v).toHomeomorph.isClosedEmbedding
  have hRinj (v : NumberField.InfinitePlace F) : Function.Injective (R v) := (hRce v).injective
  have hRrange (v : NumberField.InfinitePlace F) :
      (R v).range = ((ρ v).affineMatrix (CommAlgCat.of v.Completion v.Completion)).range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(InfinitePlaceGroupPoints.completionBaseChangeHomeomorph F G v).symm x, ?_⟩
      exact congrArg ((ρ v).affineMatrix (CommAlgCat.of v.Completion v.Completion))
        ((InfinitePlaceGroupPoints.completionBaseChangeHomeomorph F G v).apply_symm_apply x)
  have hRstar := fun v : NumberField.InfinitePlace F =>
    star_mem_range_of_range_eq (R v) _ (hRrange v) (hρstar v)
  have hRpoly := fun v : NumberField.InfinitePlace F =>
    isPolynomiallyDefined_range_of_range_eq (R v) _ (hRrange v)
      (@MatrixRepresentation.affineMatrix_range_isPolynomiallyDefined _ _ _ _ _ _ (ρ v) (hρclosed v)
        v.Completion _ _)
  -- conjugate the compact projections of `Kinf` into the unitary groups
  let Kv : ∀ v : NumberField.InfinitePlace F, Subgroup (GL (Fin (N v)) v.Completion) :=
    fun v => Kinf.map ((R v).comp (atPlace F G v).toMonoidHom)
  have hKv_compact (v : NumberField.InfinitePlace F) :
      IsCompact ((Kv v : Subgroup (GL (Fin (N v)) v.Completion)) : Set (GL (Fin (N v)) v.Completion)) := by
    rw [Subgroup.coe_map]
    exact hK.1.image ((hRce v).continuous.comp (atPlace F G v).continuous)
  have hKv_le (v : NumberField.InfinitePlace F) : Kv v ≤ (R v).range := by
    rintro _ ⟨k, _, rfl⟩
    exact ⟨_, rfl⟩
  have hRclosed (v : NumberField.InfinitePlace F) :
      IsClosed (SetLike.coe (R v).range : Set (GL (Fin (N v)) v.Completion)) := by
    rw [MonoidHom.coe_range]
    exact (hRce v).isClosed_range
  have hconj := fun v : NumberField.InfinitePlace F =>
    Langlands.Group.PolynomialStarCompactConjugacy.exists_conj_unitary (R v).range (Kv v)
      (hRclosed v) (hRpoly v) (hRstar v) (hKv_compact v) (hKv_le v)
  choose a ha hau using hconj
  -- the Cartan involution
  let θv := fun v : NumberField.InfinitePlace F =>
    Langlands.Group.MatrixCartanInvolution.cartan (R v) (hRinj v) (hRstar v) (a v) (ha v)
  let θ : InfiniteAdelicGroupPoints F G → InfiniteAdelicGroupPoints F G :=
    fun g => (completions F G).symm (fun v => θv v (atPlace F G v g))
  have hθat (g : InfiniteAdelicGroupPoints F G) (v : NumberField.InfinitePlace F) :
      atPlace F G v (θ g) = θv v (atPlace F G v g) := by
    rw [← completions_apply]
    simp only [θ, ContinuousMulEquiv.apply_symm_apply]
  have hext (g g' : InfiniteAdelicGroupPoints F G)
      (h : ∀ v, atPlace F G v g = atPlace F G v g') : g = g' :=
    (completions F G).injective (funext h)
  have hθθ (g : InfiniteAdelicGroupPoints F G) : θ (θ g) = g :=
    hext _ _ fun v => by
      rw [hθat, hθat]
      exact Langlands.Group.MatrixCartanInvolution.cartan_cartan _ _ _ _ _ _
  have hθ1 : θ 1 = 1 :=
    hext _ _ fun v => by
      rw [hθat, map_one]
      exact Langlands.Group.MatrixCartanInvolution.cartan_one _ _ _ _ _
  -- smoothness of the realization entries
  have hplace (v : NumberField.InfinitePlace F) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, Fin d → v.Completion) ∞ (atPlace F G v) :=
    (contMDiff_iff_places F G 𝓘(ℝ, smoothModel F d) hsmooth id).mp contMDiff_id v
  have hentry (v : NumberField.InfinitePlace F) (i j : Fin (N v)) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
        (fun g => (R v (atPlace F G v g)).val i j) :=
    (InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix F G v 𝓘(ℝ, smoothModel F d)
      hsmooth (ρ v) (hρclosed v) (atPlace F G v)).mp (hplace v) i j
  -- the conjugated matrix representations
  let φ := fun v : NumberField.InfinitePlace F =>
    (Units.coeHom _).comp ((MulAut.conj (a v)⁻¹).toMonoidHom.comp
      ((R v).comp (atPlace F G v).toMonoidHom))
  have hφ_apply (v : NumberField.InfinitePlace F) (g : InfiniteAdelicGroupPoints F G) :
      φ v g = ((a v)⁻¹ * R v (atPlace F G v g) * a v).val := by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Units.coeHom_apply]
    rfl
  have hφsm (v : NumberField.InfinitePlace F) (i j : Fin (N v)) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞ (fun g => φ v g i j) := by
    have h := contMDiff_mul_entries (hentry v) ((a v)⁻¹).val (a v).val i j
    convert h using 2 with g
    rw [hφ_apply, Units.val_mul, Units.val_mul]
  have hθsm : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d) ∞ θ := by
    apply (contMDiff_iff_places F G 𝓘(ℝ, smoothModel F d) hsmooth θ).mpr
    intro v
    apply (InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix F G v 𝓘(ℝ, smoothModel F d)
      hsmooth (ρ v) (hρclosed v) (fun g => atPlace F G v (θ g))).mpr
    intro i j
    have hinvent (k l : Fin (N v)) : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
        (fun g => (R v (atPlace F G v g)⁻¹).val k l) := by
      have h := (hentry v k l).comp (contMDiff_inv 𝓘(ℝ, smoothModel F d) ∞)
      convert h using 2 with g
      simp only [Function.comp_apply, map_inv]
    have h := contMDiff_cartan_entries (R v) (hRinj v) (hRstar v) (a v) (ha v)
      (f := atPlace F G v) hinvent i j
    convert h using 2 with g
    rw [hθat]
  -- joint injectivity of the differentials
  have hinj : ∀ X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G),
      (∀ v, Langlands.Geometry.Manifold.MatrixCoefficientLie.matrixDifferential
        𝓘(ℝ, smoothModel F d) (φ v) X = 0) → X = 0 := by
    intro X hX
    apply eq_zero_of_zeroDeriv_realization F G hsmooth ρ hρclosed X
    intro v i j
    have hφZ (k l : Fin (N v)) :
        Langlands.Geometry.Manifold.ZeroDirectionalDerivative.ZeroDeriv X
          (fun g => φ v g k l) := by
      refine ⟨mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (fun g => φ v g k l) 1,
        ((hφsm v k l).mdifferentiableAt (by simp)).hasMFDerivAt, ?_⟩
      have h := congrArg (fun m => m k l) (hX v)
      exact h
    have hsum : Langlands.Geometry.Manifold.ZeroDirectionalDerivative.ZeroDeriv X
        (fun g => ∑ l, ∑ k, (a v).val i k * φ v g k l * ((a v)⁻¹).val l j) :=
      Langlands.Geometry.Manifold.ZeroDirectionalDerivative.zeroDeriv_finset_sum _
        fun l _ => Langlands.Geometry.Manifold.ZeroDirectionalDerivative.zeroDeriv_finset_sum _
          fun k _ =>
            ((Langlands.Geometry.Manifold.ZeroDirectionalDerivative.zeroDeriv_const _).mul
              (hφZ k l)).mul
              (Langlands.Geometry.Manifold.ZeroDirectionalDerivative.zeroDeriv_const _)
    refine hsum.congr (Filter.Eventually.of_forall fun g => ?_)
    have hR : (R v (atPlace F G v g)).val =
        (a v).val * φ v g * ((a v)⁻¹).val := by
      rw [hφ_apply, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    show _ = (R v (atPlace F G v g)).val i j
    rw [hR]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  -- the fixed points of the involution lie in `Kinf`
  let L : Subgroup (InfiniteAdelicGroupPoints F G) := ⨅ v : NumberField.InfinitePlace F,
    (Langlands.Group.MatrixCartanInvolution.cartanUnitary (R v) (a v)).comap
      (atPlace F G v).toMonoidHom
  have hmemL (g : InfiniteAdelicGroupPoints F G) :
      g ∈ L ↔ ∀ v, atPlace F G v g ∈
        Langlands.Group.MatrixCartanInvolution.cartanUnitary (R v) (a v) := by
    simp only [L, Subgroup.mem_iInf, Subgroup.mem_comap]
    rfl
  have hLset : (L : Set (InfiniteAdelicGroupPoints F G)) = (completions F G) ⁻¹'
      (Set.univ.pi fun v => (Langlands.Group.MatrixCartanInvolution.cartanUnitary (R v) (a v) :
        Set (InfinitePlaceGroupPoints F G v))) := by
    ext g
    rw [SetLike.mem_coe, hmemL, Set.mem_preimage, Set.mem_univ_pi]
    rfl
  have hLc : IsCompact (L : Set (InfiniteAdelicGroupPoints F G)) := by
    rw [hLset]
    exact (completions F G).toHomeomorph.isCompact_preimage.mpr
      (isCompact_univ_pi fun v =>
        Langlands.Group.MatrixCartanInvolution.isCompact_cartanUnitary (R v) (a v) (hRce v))
  have hle : Kinf ≤ L := by
    intro k hk
    rw [hmemL]
    intro v
    exact (Langlands.Group.MatrixCartanInvolution.mem_cartanUnitary_iff (R v) (a v) _).mpr
      (hau v _ ⟨k, hk, rfl⟩)
  have hLK : L = Kinf := hK.2 L hLc hle
  have hKfix (g : InfiniteAdelicGroupPoints F G) (hg : θ g = g) :
      g ∈ (Kinf : Set (InfiniteAdelicGroupPoints F G)) := by
    rw [SetLike.mem_coe, ← hLK, hmemL]
    intro v
    apply Langlands.Group.MatrixCartanInvolution.mem_cartanUnitary_of_cartan_eq (R v) (hRinj v)
      (hRstar v) (a v) (ha v)
    have h := hθat g v
    rw [hg] at h
    exact h.symm
  -- assemble
  obtain ⟨n, X, J, hspan, hcurve, hcent⟩ :=
    Langlands.Geometry.Manifold.AdaptedCasimirAssembly.exists_adapted_casimir
      (E := smoothModel F d) (G := InfiniteAdelicGroupPoints F G)
      (𝕜' := fun v : NumberField.InfinitePlace F => v.Completion)
      (N' := fun v : NumberField.InfinitePlace F => Fin (N v)) φ hφsm θ hθsm hθθ hθ1
      (fun v g => by
        rw [hφ_apply, hφ_apply, hθat]
        exact Langlands.Group.MatrixCartanInvolution.val_conj_cartan_mul_conjTranspose (R v)
          (hRinj v) (hRstar v) (a v) (ha v) (atPlace F G v g))
      hinj (Kinf : Set (InfiniteAdelicGroupPoints F G)) hKfix
  exact ⟨n, X, J, hspan, hcurve, hcent⟩

end Langlands.Automorphic.GroupSchemeFunctions
