import Langlands.Representation.Aubert.General.DynamicUnipotentVectorFiltrationProof
import Langlands.Analysis.Local.TwistedConjugationFiltration
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Mathlib.Basic.ENNReal.BigOperators

/-! # Haar scaling of displacement by a Levi point on the actual radical -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Matrix

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme GroupScheme.Dynamic.GradedCoordinates GroupScheme.Corepresented
  GroupScheme.RelativeRoot Langlands.AlgebraicGeometry.PointTopology
  Langlands.HaarModulus Langlands.HaarModulus.VectorFiltration Langlands.QuotientIntegration

attribute [local instance] Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
  [IsAffineHom U.X.hom] (m : rationalPoints Z)

/-- The Lie determinant of the displacement by an actual Levi point. -/
def unipotentDisplacementDeterminant : k :=
  LinearMap.det ((LinearMap.id : Additive (lieKernel U k) →ₗ[k] Additive (lieKernel U k)) -
    ((Dynamic.centralizerAdjointAction hZ hU).differential (toBase (baseTest k) ≫ m)).toLinearMap)

section Filtration

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G)

local instance displacementAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance displacementAmbientTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

local instance displacementAmbientTopologicalGroup : IsTopologicalGroup (RationalPoint k G.X) :=
  rationalPoint_isTopologicalGroup k G

include hG in
/-- Use the graded rational coordinates to present the displacement by a
finite sequence of invertible vector displacements. Each matrix block is a
block of `1 - Ad(m)` in the corresponding Lie coordinates. -/
private theorem exists_displacementVectorFiltration
    (hdet : unipotentDisplacementDeterminant hZ hU m ≠ 0) :
    ∃ (N : ℕ) (F : ℕ → Subgroup (RationalPoint k G.X)) (n : ℕ → ℕ)
      (q : ∀ r, F r → Fin (n r) → k)
      (D : ∀ r, (Fin (n r) → k) ≃ₗ[k] (Fin (n r) → k)),
      F 0 = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ∧ F N = ⊥ ∧
      (∀ r < N, F (r + 1) ≤ F r) ∧
      (∀ r, (m ≫ iZ.hom.hom : RationalPoint k G.X) ∈ Subgroup.normalizer (F r : Set _)) ∧
      (∀ r < N, ∀ x y : F r, q r (x * y) = q r x + q r y) ∧
      (∀ r < N, ∀ x : F r, q r x = 0 ↔ (x : RationalPoint k G.X) ∈ F (r + 1)) ∧
      (∀ r < N, Continuous (q r)) ∧
      (∀ r < N, IsOpenMap (q r)) ∧
      (∀ r < N, Function.Surjective (q r)) ∧
      (∀ r < N, ∀ x y : F r, (y : RationalPoint k G.X) =
        (m ≫ iZ.hom.hom : RationalPoint k G.X) * x *
          (m ≫ iZ.hom.hom : RationalPoint k G.X)⁻¹ → D r (q r x) = q r x - q r y) ∧
      (∏ r ∈ Finset.range N, (LinearEquiv.det (D r) : k)) =
        unipotentDisplacementDeterminant hZ hU m := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have := isAffineHom_affineCoordinates G
  have := AffineCoordinates.formallySmooth_algebra G hG.smooth
  have := AffineCoordinates.finiteType_algebra G hG.smooth
  obtain ⟨n, dd, x, hd, -, hx, hbij⟩ := exists_aeval_bijective_cyclicTail
    (AffineCoordinates.corepresentation G) (cocharModelAction G χ) (idExponent_ne_zero (k := k)) 1
  have hg : m ≫ iZ.hom.hom ∈ (torusCentralizer χ).carrier _ :=
    mem_torusCentralizer_of_centralizer G χ hZ m
  let J := centralizerMatrix G χ hx hbij hZ m
  let B := 1 - J
  let Φ := lieCoordEquiv G χ hU hd hx hbij
  have hconj : (LinearMap.id - ((Dynamic.centralizerAdjointAction hZ hU).differential
      (toBase (baseTest k) ≫ m)).toLinearMap) =
      Φ.symm.toLinearMap ∘ₗ Matrix.toLin' B ∘ₗ Φ.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply Φ.injective
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, B,
      Matrix.toLin'_one]
    rw [Matrix.toLin'_apply]
    exact congrArg (Φ v - ·) (lieCoord_differential G χ hU hd hx hbij hZ m v)
  have hB : B.det = unipotentDisplacementDeterminant hZ hU m := by
    have hc := LinearMap.det_conj (Matrix.toLin' B) Φ.symm
    rw [LinearEquiv.symm_symm] at hc
    rw [unipotentDisplacementDeterminant, hconj, hc, LinearMap.det_toLin']
  have hB0 : B.det ≠ 0 := hB ▸ hdet
  have hJtri : J.BlockTriangular dd :=
    conjMatrix_blockTriangular (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (constantFamily_naturality G (m ≫ iZ.hom.hom))
      (constantFamily_fixed G _ χ hg) idExponent_ne_zero hx hbij.2
  have hBprod : B.det = ∏ s ∈ Finset.univ.image dd, (B.toSquareBlock dd s).det :=
    (Matrix.blockTriangular_one.sub hJtri).det
  have hblock (s : ℕ) : (B.toSquareBlock dd s).det ≠ 0 := by
    by_cases hs : s ∈ Finset.univ.image dd
    · rw [hBprod] at hB0
      exact Finset.prod_ne_zero_iff.1 hB0 s hs
    · have : IsEmpty {i // dd i = s} :=
        ⟨fun i => hs (Finset.mem_image.2 ⟨i.1, Finset.mem_univ _, i.2⟩)⟩
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
  set N := Finset.univ.sup dd
  have hN : ∀ i, dd i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  let nr : ℕ → ℕ := fun r => Fintype.card {i // dd i = r + 1}
  let eqv : ∀ r, {i // dd i = r + 1} ≃ Fin (nr r) := fun r => Fintype.equivFin _
  let M (r : ℕ) : Matrix (Fin (nr r)) (Fin (nr r)) k :=
    (B.toSquareBlock dd (r + 1)).reindex (eqv r) (eqv r)
  have hM (r : ℕ) : (M r).det = (B.toSquareBlock dd (r + 1)).det := Matrix.det_reindex_self _ _
  let D (r : ℕ) : (Fin (nr r) → k) ≃ₗ[k] (Fin (nr r) → k) :=
    LinearMap.equivOfDetNeZero (Matrix.toLin' (M r))
      (by rw [LinearMap.det_toLin', hM]; exact hblock _)
  let F := rationalFiltration G χ
  have hF0 : ∀ r, F r ≤ F 0 := rationalFiltration_le_zero G χ
  let q : ∀ r, F r → Fin (nr r) → k := fun r p j =>
    ratCoord G χ x ⟨p.1, hF0 r p.2⟩ ((eqv r).symm j).1
  have hqmul : ∀ r, ∀ p p' : F r, q r (p * p') = q r p + q r p' := by
    intro r p p'
    funext j
    change ratCoord G χ x (⟨p.1, hF0 r p.2⟩ * ⟨p'.1, hF0 r p'.2⟩) ((eqv r).symm j).1 = _
    exact ratCoord_mul G χ hx ⟨p.1, hF0 r p.2⟩ ⟨p'.1, hF0 r p'.2⟩ p.2 p'.2 ((eqv r).symm j).2
  let v : ∀ r, (Fin (nr r) → k) → Fin n → k := fun r w i =>
    if h : dd i = r + 1 then w (eqv r ⟨i, h⟩) else 0
  have hvmem : ∀ r w, ratPoint G χ x hbij (v r w) ∈ F r := by
    intro r w
    refine (mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r)
      ⟨_, ratPoint_mem G χ hbij (v r w)⟩).2 fun i hi => ?_
    rw [ratCoord_ratPoint]
    simp only [v, show ¬ dd i = r + 1 by omega, ↓reduceDIte]
  let sec : ∀ r, (Fin (nr r) → k) → F r := fun r w => ⟨ratPoint G χ x hbij (v r w), hvmem r w⟩
  have hqsec : ∀ r w, q r (sec r w) = w := by
    intro r w
    funext j
    change ratCoord G χ x ⟨ratPoint G χ x hbij (v r w), _⟩ ((eqv r).symm j).1 = w j
    rw [ratCoord_ratPoint]
    simp only [v, ((eqv r).symm j).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]
  have hsec_cont : ∀ r, Continuous (sec r) := by
    intro r
    refine Continuous.subtype_mk ((continuous_ratPoint G χ hbij).comp ?_) _
    refine continuous_pi fun i => ?_
    by_cases h : dd i = r + 1
    · simp only [v, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [v, h, ↓reduceDIte]
      exact continuous_const
  refine ⟨N, F, nr, q, D, rationalFiltration_zero G χ,
    rationalFiltration_eq_bot G χ hd hx hbij hN, fun r _ => rationalFiltration_succ_le G χ r,
    fun r => mem_normalizer_rationalFiltration G χ hg r, fun r _ => hqmul r, ?_, ?_,
    fun r _ => isOpenMap_of_continuous_section (q r) (hqmul r) (sec r) (hsec_cont r) (hqsec r),
    fun r _ w => ⟨sec r w, hqsec r w⟩, ?_, ?_⟩
  · intro r _ p
    have h0 := (mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r)
      ⟨p.1, hF0 r p.2⟩).1 p.2
    rw [show (p.1 ∈ F (r + 1)) ↔ _ from
      mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r + 1) ⟨p.1, hF0 r p.2⟩]
    constructor
    · intro hq i hi
      by_cases hir : dd i = r + 1
      · have h := congrFun hq (eqv r ⟨i, hir⟩)
        simpa [q] using h
      · exact h0 i (by omega)
    · intro h
      funext j
      exact h _ (by have := ((eqv r).symm j).2; omega)
  · intro r _
    refine continuous_pi fun j => ?_
    exact (continuous_ratCoord G χ ((eqv r).symm j).1).comp
      (continuous_subtype_val.subtype_mk _)
  · intro r _ p p' hy
    funext j
    have hp' : (⟨p'.1, hF0 r p'.2⟩ : F 0) =
        ⟨m ≫ iZ.hom.hom * p.1 * (m ≫ iZ.hom.hom)⁻¹,
          conj_mem_rationalFiltration G χ hg (hF0 r p.2)⟩ := Subtype.ext hy
    change (Matrix.toLin' (M r) (q r p)) j = (q r p) j -
      ratCoord G χ x ⟨p'.1, hF0 r p'.2⟩ ((eqv r).symm j).1
    let C := (J.toSquareBlock dd (r + 1)).reindex (eqv r) (eqv r)
    have hMC : M r = 1 - C := by
      ext a b
      simp only [M, B, C, Matrix.reindex_apply, Matrix.toSquareBlock, Matrix.toSquareBlockProp,
        Matrix.toBlock_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, Subtype.coe_inj,
        Equiv.apply_eq_iff_eq]
    rw [hMC, map_sub, Matrix.toLin'_one, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply,
      hp', ratCoord_conj G χ hd hx hbij hg ⟨p.1, hF0 r p.2⟩ p.2 ((eqv r).symm j).2,
      Matrix.toLin'_apply, sum_filter_eq_sum_fin dd (r + 1)]
    rfl
  · have hdetD (r : ℕ) : (LinearEquiv.det (D r) : k) = (B.toSquareBlock dd (r + 1)).det := by
      rw [LinearEquiv.coe_det]
      change LinearMap.det (Matrix.toLin' (M r)) = _
      rw [LinearMap.det_toLin', hM]
    simp only [hdetD]
    rw [prod_range_det_toSquareBlock dd B hd hN, ← hBprod, hB]

include hG in
/-- For a nonzero Lie displacement determinant the actual radical Haar
measure pushes forward by its inverse absolute value. -/
theorem map_dynamicUnipotentDisplacement
    [LocallyCompactSpace (RationalPoint k G.X)]
    [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
    (hUc : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
    (hm : m ≫ iZ.hom.hom ∈ Subgroup.normalizer
      ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
    (hdet : unipotentDisplacementDeterminant hZ hU m ≠ 0)
    (radicalMeasure : Measure ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))) [radicalMeasure.IsHaarMeasure] :
    radicalMeasure.map (twistedConjugationMap (normalizerConj _ ⟨m ≫ iZ.hom.hom, hm⟩)) =
      ((distribHaarChar k (Units.mk0 (unipotentDisplacementDeterminant hZ hU m) hdet) : ℝ≥0∞))⁻¹ • radicalMeasure := by
  have : SecondCountableTopology (RationalPoint k G.X) :=
    rationalPoint_secondCountableTopology k G
  obtain ⟨N, F, n, q, D, hF0, hFN, hFle, hFg, hqmul, hqker, hqc, hqo, hqs, hqD, hprod⟩ :=
    exists_displacementVectorFiltration hZ hU m hG hdet
  have hcover (x : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) :
      ∃ K : OpenSubgroup ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))),
        IsCompact (K : Set ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))) ∧ x ∈ K := by
    obtain ⟨K, hK, hxK⟩ := BruhatTits.dynamicUnipotentCompactOpenContainment k G hG χ
      {x} (isCompact_singleton)
    exact ⟨K, hK, hxK (Set.mem_singleton x)⟩
  revert hcover radicalMeasure hm hUc
  generalize (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) = V at hF0 ⊢
  intro hUc hm radicalMeasure _ hcover
  subst V
  have he := map_twistedConjugationMap_of_vectorFiltration N F hUc hFN hcover hFle
    (m ≫ iZ.hom.hom) (fun r _ => hFg r) n q hqmul hqker hqc hqo hqs D
    (fun r hr x => hqD r hr x _ rfl) radicalMeasure
  rw [he]
  congr 1
  have hprod' : (∏ r ∈ Finset.range N, LinearEquiv.det (D r)) =
      Units.mk0 (unipotentDisplacementDeterminant hZ hU m) hdet := by
    apply Units.ext
    rw [Units.coe_prod]
    exact hprod
  rw [displacementFiltrationFactor, ← Finset.range_eq_Ico,
    ← ENNReal.prod_inv_distrib, ← ENNReal.ofNNReal_finsetProd, ← map_prod, hprod']
  intro i _ j _ _
  exact Or.inr ENNReal.coe_ne_top

end Filtration

end Langlands.Aubert.General.RationalPointFamily
