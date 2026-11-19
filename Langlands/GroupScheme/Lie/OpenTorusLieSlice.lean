import Langlands.GroupScheme.Lie.RegularTorusLieSlice
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.Topology.Algebra.MvPolynomial

/-! # An open set in the regular torus Lie slice over a complete field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology Langlands.AlgebraicGeometry.TangentSmoothness
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

open MatrixRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [NontriviallyNormedField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} {d e : ℕ}

private theorem ΓSpecIso_hom_scalarMap_identity (a : k) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) a) = a := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a) = a
  exact Iso.inv_hom_id_apply _ _

private theorem coefficientCoordinates_rationalPointEquiv
    (p : RationalPoint k (coefficientSpace (Fin d) (CommRingCat.of k))) :
    coefficientCoordinates (rationalPointEquiv k _ p) = coefficientCoordinates p := by
  funext i
  change ((rationalPointEquiv k _ p).left.appTop) _ = p.left.appTop _
  rw [rationalPointEquiv_left]
  rfl

private theorem continuous_constantCoefficientPoint :
    let Y := coefficientSpace (Fin d) (CommRingCat.of k)
    letI : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
    Continuous (fun v : Fin d → k => rationalPointEquiv k Y (constantCoefficientPoint v)) := by
  let Y := coefficientSpace (Fin d) (CommRingCat.of k)
  let A := MvPolynomial (Fin d) k
  let : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
  let f : ringTest k A ⟶ Y := coefficientPoint _ fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv (MvPolynomial.X i)
  let ψ := (spectrumAlgebraPointHomeomorph k k A).trans
    (AlgPoint.polynomialPointHomeomorph (R := k) (S := k) (Fin d))
  have hf : Continuous[inferInstance, schemePointTopology k Y k]
      (fun p : RingPoint k (ringTest k A) k => (p ≫ f : RingPoint k Y k)) := by
    have h := schemePointContinuity_proof k k (ringTest k A) Y f
    rwa [schemePointTopology_eq_affine k (ringTest k A) k] at h
  have hψp (v : Fin d → k) : ψ.symm v = ringTestMap k (MvPolynomial.aeval v) := by
    let φ : A →ₐ[k] k := MvPolynomial.aeval v
    have hφ : affineRingPointEquiv k A k (ringTestMap k φ) = φ := by
      apply AlgHom.coe_ringHom_injective
      change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom = φ.toRingHom
      rw [Spec.preimage_map]
      rfl
    change ψ.symm v = ringTestMap k φ
    apply ψ.injective
    rw [Homeomorph.apply_symm_apply]
    funext i
    simp only [ψ, Homeomorph.trans_apply, spectrumAlgebraPointHomeomorph_apply]
    change v i = affineRingPointEquiv k A k (ringTestMap k φ) (MvPolynomial.X i)
    rw [hφ]
    exact (MvPolynomial.aeval_X v i).symm
  have heq (v : Fin d → k) : rationalPointEquiv k Y (constantCoefficientPoint v) = ψ.symm v ≫ f := by
    apply coefficientCoordinates_injective
    have hcoords : coefficientCoordinates f = fun i =>
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv (MvPolynomial.X i) :=
      coefficientCoordinates_coefficientPoint _ _
    rw [coefficientCoordinates_rationalPointEquiv, hψp, coefficientCoordinates_comp, hcoords,
      constantCoefficientPoint, coefficientCoordinates_coefficientPoint]
    funext i
    let φ : CommRingCat.of A ⟶ CommRingCat.of k :=
      CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom
    have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) (MvPolynomial.X i)
    have hi : φ (MvPolynomial.X i) = v i := MvPolynomial.aeval_X v i
    change (Scheme.ΓSpecIso (CommRingCat.of k)).inv (φ (MvPolynomial.X i)) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (MvPolynomial.X i)) at h
    rw [hi] at h
    exact h
  simpa only [Function.comp_def, ← heq] using hf.comp ψ.symm.continuous

private theorem rationalPointEquiv_eq_constantCoefficientPoint_of_coordinates
    (v : Fin d → k) (p : RingPoint k (coefficientSpace (Fin d) (CommRingCat.of k)) k)
    (hp : (fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (coefficientCoordinates p i)) = v) :
    p = rationalPointEquiv k _ (constantCoefficientPoint v) := by
  apply coefficientCoordinates_injective
  rw [coefficientCoordinates_rationalPointEquiv, constantCoefficientPoint,
    coefficientCoordinates_coefficientPoint]
  funext i
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).injective
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom (coefficientCoordinates p i) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (v i))
  rw [Iso.inv_hom_id_apply]
  exact congrFun hp i

variable [CompleteSpace k]

private theorem constantCoefficientPoint_mem_open_sliceImage [IsAffineHom G.X.hom]
    [Smooth G.X.hom] (ρ : MatrixRepresentation G (Fin d))
    (B : Matrix (Fin d) (Fin e) k) (t₀ : Fin e → k)
    (h : ∀ v : Fin d → k, ∃ (ξ : lieKernel G k) (t' : Fin e → k),
      ρ.tangentMatrix k ξ *ᵥ (B *ᵥ t₀) + B *ᵥ t' = v) :
    ∃ U : Set (Fin d → k), IsOpen U ∧ B *ᵥ t₀ ∈ U ∧ ∀ v ∈ U,
      ∃ (g : G.affinePoints (.of (CommRingCat.of k) k)) (t : Fin e → k),
        ρ.affineAction (.of (CommRingCat.of k) k) g (B *ᵥ t) = v := by
  let X := G.X ⊗ coefficientSpace (Fin e) (CommRingCat.of k)
  let Y := coefficientSpace (Fin d) (CommRingCat.of k)
  let f : X ⟶ Y := sliceMap ρ B
  let p : RationalPoint k X := slicePoint t₀
  have : Smooth X.hom := smooth_tensor _ _ inferInstance
    (inferInstanceAs (Smooth (𝔸(ULift.{u} (Fin e); Spec (CommRingCat.of k)) ↘ _)))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)) ↘ _))
  have := locallyOfFinitePresentation_of_comp_eq f.left (Over.w f)
  let V := f.left.smoothLocus
  have hp : p.left (IsLocalRing.closedPoint k) ∈ V :=
    mem_smoothLocus_of_isTangentSurjectiveAt f.left (Over.w f)
      (Over.w p) (isTangentSurjectiveAt_sliceMap ρ B t₀ h)
  let fV := openOverι k X V ≫ f
  have : Smooth fV.left := by
    change Smooth (V.ι ≫ f.left)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  let : TopologicalSpace (RingPoint k Y k) := schemePointTopology k Y k
  let : TopologicalSpace (RingPoint k (openOver k X V) k) :=
    schemePointTopology k (openOver k X V) k
  let s : RingPoint k (openOver k X V) k → RingPoint k Y k := fun q => q ≫ fV
  let a : (Fin d → k) → RingPoint k Y k :=
    fun v => rationalPointEquiv k Y (constantCoefficientPoint v)
  let q := rationalPointEquiv k X p
  have hq : Set.range q.left ⊆ V := by
    apply (range_subset_open_iff_closedPoint k X k V q).2
    change (rationalPointEquiv k X p).left (IsLocalRing.closedPoint k) ∈ V
    rw [rationalPointEquiv_left]
    exact hp
  have hB : B.map (algebraMap k k) = B := by
    ext i j
    simp
  have hscalar {r : ℕ} (t : Fin r → k) :
      (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (t j))) = t :=
    funext fun j => ΓSpecIso_hom_scalarMap_identity (t j)
  have hqp : q ≫ f = a (B *ᵥ t₀) := by
    apply rationalPointEquiv_eq_constantCoefficientPoint_of_coordinates
    have h₁ : q = lift 1 (rationalPointEquiv k _ (constantCoefficientPoint t₀)) := by
      change (ringTestSelfIso k).hom ≫
          lift (1 : RationalPoint k G.X) (constantCoefficientPoint t₀) ≫
            𝟙 (G.X ⊗ coefficientSpace (Fin e) (CommRingCat.of k)) =
        lift 1 ((ringTestSelfIso k).hom ≫ constantCoefficientPoint t₀ ≫ 𝟙 _)
      rw [Category.comp_id, Category.comp_id, comp_lift, MonObj.comp_one]
    change (fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (coefficientCoordinates (q ≫ sliceMap ρ B) i)) = _
    rw [h₁, affineCoordinates_sliceMap ρ B (.of (CommRingCat.of k) k)]
    rw [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
      coefficientCoordinates_rationalPointEquiv, constantCoefficientPoint,
      coefficientCoordinates_coefficientPoint]
    change B.map (algebraMap k k) *ᵥ _ = _
    rw [hB, hscalar]
  have hLift : (openPointLift k X k V q hq ≫ openOverι k X V) = q :=
    openPointMap_lift k X k V q hq
  refine ⟨a ⁻¹' Set.range s, (isOpenMap_smoothSchemePointMap k fV).isOpen_range.preimage
    continuous_constantCoefficientPoint, ?_, ?_⟩
  · exact ⟨openPointLift k X k V q hq, by dsimp only [s, fV]; rw [← Category.assoc, hLift, hqp]⟩
  · rintro v ⟨qV, hqV⟩
    let r := qV ≫ openOverι k X V
    let g := r ≫ fst G.X (coefficientSpace (Fin e) (CommRingCat.of k))
    let x := r ≫ snd G.X (coefficientSpace (Fin e) (CommRingCat.of k))
    let t : Fin e → k := fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).hom (coefficientCoordinates x i)
    have hr : lift g x = r := by
      dsimp only [g, x]
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hrf : r ≫ f = a v := Category.assoc _ _ _ |>.trans hqV
    have hc := affineCoordinates_sliceMap ρ B (.of (CommRingCat.of k) k) g x
    rw [hr, hrf, coefficientCoordinates_rationalPointEquiv, constantCoefficientPoint,
      coefficientCoordinates_coefficientPoint] at hc
    change (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (v j))) =
      (ρ.affineMatrix (.of (CommRingCat.of k) k) g : Matrix (Fin d) (Fin d) k) *ᵥ
        (B.map (algebraMap k k) *ᵥ t) at hc
    rw [hscalar, hB] at hc
    refine ⟨g, t, ?_⟩
    exact hc.symm

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] (c : FiniteCoordinates G d)
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- A nonempty analytic open set in the image of the actual torus Lie slice,
where the bracket matrix plus a fixed projection is invertible. -/
theorem exists_open_regularTorusLieSlice (hT : IsTorus T.toGrp) :
    ∃ D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k,
      let B := torusCentralizerMatrix c j
      D * B = 1 ∧ ∃ U : Set (Fin d → k), IsOpen U ∧ U.Nonempty ∧ ∀ v ∈ U,
        IsUnit (adjointMatrixAt c k v + B * D) ∧
        ∃ (g : G.affinePoints (.of (CommRingCat.of k) k))
          (t : Fin (Module.finrank k (torusCentralizerCoordinates c j)) → k),
          (adjointRepresentation c).affineAction (.of (CommRingCat.of k) k) g (B *ᵥ t) = v := by
  let B := torusCentralizerMatrix c j
  obtain ⟨D, hD, t₀, ht₀⟩ := regularTorusLieSlice k G d c T j hT
  let P := B * D
  have h : ∀ v : Fin d → k, ∃ (ξ : lieKernel G k)
      (t' : Fin (Module.finrank k (torusCentralizerCoordinates c j)) → k),
      (adjointRepresentation c).tangentMatrix k ξ *ᵥ (B *ᵥ t₀) + B *ᵥ t' = v := by
    intro v
    obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr ht₀ v
    let ξ := ((c.equiv (.of (CommRingCat.of k) k)).symm x).toMul
    have hξ : c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul ξ) = x := by
      simp only [ξ, ofMul_toMul, LinearEquiv.apply_symm_apply]
    refine ⟨ξ, D *ᵥ x, ?_⟩
    rw [← adjointMatrixAt_mulVec, hξ, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
    exact hx
  obtain ⟨U, hU, htU, hslice⟩ := constantCoefficientPoint_mem_open_sliceImage
    (adjointRepresentation c) B t₀ h
  let δ : (Fin d → k) → k := fun v => (adjointMatrixAt c k v + P).det
  have hδ : Continuous δ := by
    have he (v : Fin d → k) : MvPolynomial.eval v (adjointSliceDeterminant c 1 P) = δ v := by
      change MvPolynomial.aeval v (adjointSliceDeterminant c 1 P) = δ v
      rw [aeval_adjointSliceDeterminant]
      simp [δ, Algebra.algebraMap_self, Matrix.map_id]
    rw [← funext he]
    exact MvPolynomial.continuous_eval _
  have hn : IsOpen {v | δ v ≠ 0} := isOpen_ne_fun hδ continuous_const
  refine ⟨D, hD, U ∩ {v | δ v ≠ 0}, hU.inter hn,
    ⟨B *ᵥ t₀, htU, ((Matrix.isUnit_iff_isUnit_det _).mp ht₀).ne_zero⟩, ?_⟩
  intro v hv
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv.2), hslice v hv.1⟩

/-- The regular torus Lie slice has nonempty open image in finite Lie coordinates
over a complete nontrivially normed field. -/
def OpenTorusLieSliceStatement : Prop :=
  ∀ (k : Type u) [NontriviallyNormedField k] [CompleteSpace k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (d : ℕ) (c : FiniteCoordinates G d)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsTorus T.toGrp →
      ∃ D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k,
        let B := torusCentralizerMatrix c j
        D * B = 1 ∧ ∃ U : Set (Fin d → k), IsOpen U ∧ U.Nonempty ∧ ∀ v ∈ U,
          IsUnit (adjointMatrixAt c k v + B * D) ∧
          ∃ (g : G.affinePoints (.of (CommRingCat.of k) k))
            (t : Fin (Module.finrank k (torusCentralizerCoordinates c j)) → k),
            (adjointRepresentation c).affineAction (.of (CommRingCat.of k) k) g (B *ᵥ t) = v

theorem openTorusLieSlice : OpenTorusLieSliceStatement.{u} :=
  fun _ _ _ _ _ _ _ c _ j hT => exists_open_regularTorusLieSlice c j hT

end Langlands.GroupScheme.Lie
