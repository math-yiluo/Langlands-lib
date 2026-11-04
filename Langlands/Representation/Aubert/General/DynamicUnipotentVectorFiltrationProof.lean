import Langlands.Representation.Aubert.General.DynamicUnipotentVectorFiltrationStatement
import Langlands.GroupScheme.Dynamic.UnipotentRationalFiltration

/-! # Proof of the vector filtration of a rational dynamic unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme GroupScheme.Dynamic.GradedCoordinates GroupScheme.Corepresented
  GroupScheme.RelativeRoot Langlands.AlgebraicGeometry.PointTopology

/-- Reindexing a sum over the coordinates of a fixed weight. -/
theorem sum_filter_eq_sum_fin {n : ℕ} (d : Fin n → ℕ) (s : ℕ) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) :
    ∑ j ∈ Finset.univ.filter (fun j => d j = s), f j =
      ∑ a : Fin (Fintype.card {i // d i = s}), f ((Fintype.equivFin {i // d i = s}).symm a).1 := by
  rw [Finset.sum_subtype (Finset.univ.filter (fun j => d j = s)) (p := fun j => d j = s)
    (fun j => by simp)]
  exact (Equiv.sum_comp (Fintype.equivFin {i // d i = s}).symm (fun a => f a.1)).symm

/-- The determinants of the weight blocks over the weights `1, …, N` multiply to the
determinant over the weights that occur, if all weights lie in `1, …, N`. -/
theorem prod_range_det_toSquareBlock {k : Type u} [Field k] {n : ℕ} (d : Fin n → ℕ)
    (J : Matrix (Fin n) (Fin n) k) {N : ℕ} (hd : ∀ i, 0 < d i) (hN : ∀ i, d i ≤ N) :
    ∏ r ∈ Finset.range N, (J.toSquareBlock d (r + 1)).det =
      ∏ s ∈ Finset.univ.image d, (J.toSquareBlock d s).det := by
  classical
  rw [← Finset.prod_image (s := Finset.range N) (g := fun r => r + 1)
    (f := fun s => (J.toSquareBlock d s).det) (fun a _ b _ h => Nat.succ_injective h)]
  symm
  apply Finset.prod_subset
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    refine Finset.mem_image.2 ⟨d i - 1, Finset.mem_range.2 ?_, ?_⟩
    · have := hd i
      have := hN i
      omega
    · have := hd i
      omega
  · intro s _ hs
    have : IsEmpty {i // d i = s} := ⟨fun i => hs (Finset.mem_image.2 ⟨i.1, Finset.mem_univ _, i.2⟩)⟩
    exact Matrix.det_isEmpty

/-- **The vector filtration of a rational dynamic unipotent subgroup** (proof of
`DynamicUnipotentVectorFiltrationStatement`). -/
theorem dynamicUnipotentVectorFiltration : DynamicUnipotentVectorFiltrationStatement.{u} := by
  intro k _ _ _ _ G hG _ _ _ χ Z U iZ iU hZ hU _ _ e c m
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isAffineHom_affineCoordinates G
  have := AffineCoordinates.formallySmooth_algebra G hG.smooth
  have := AffineCoordinates.finiteType_algebra G hG.smooth
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  obtain ⟨n, dd, x, hd, -, hx, hbij⟩ := exists_aeval_bijective_cyclicTail
    (AffineCoordinates.corepresentation G) (cocharModelAction G χ) (idExponent_ne_zero (k := k)) 1
  have hg : m ≫ iZ.hom.hom ∈ (torusCentralizer χ).carrier _ :=
    mem_torusCentralizer_of_centralizer G χ hZ m
  set J := centralizerMatrix G χ hx hbij hZ m with hJdef
  have hJ : J.det =
      (rationalCharacterEval ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m :
        k) := by
    rw [rationalCharacterEval_determinantCharacter G χ hU hZ m c,
      det_differential G χ hU hd hx hbij hZ m]
  have hJ0 : J.det ≠ 0 := by
    rw [hJ]
    exact Units.ne_zero _
  have hJprod : J.det = ∏ s ∈ Finset.univ.image dd, (J.toSquareBlock dd s).det :=
    det_conjMatrix (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (constantFamily_naturality G (m ≫ iZ.hom.hom))
      (constantFamily_fixed G _ χ (mem_torusCentralizer_of_centralizer G χ hZ m))
      idExponent_ne_zero hx hbij.2
  have hblock : ∀ s, (J.toSquareBlock dd s).det ≠ 0 := by
    intro s
    by_cases hs : s ∈ Finset.univ.image dd
    · rw [hJprod] at hJ0
      exact Finset.prod_ne_zero_iff.1 hJ0 s hs
    · have : IsEmpty {i // dd i = s} :=
        ⟨fun i => hs (Finset.mem_image.2 ⟨i.1, Finset.mem_univ _, i.2⟩)⟩
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
  set N := Finset.univ.sup dd with hNdef
  have hN : ∀ i, dd i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  let nr : ℕ → ℕ := fun r => Fintype.card {i // dd i = r + 1}
  let eqv : ∀ r, {i // dd i = r + 1} ≃ Fin (nr r) := fun r => Fintype.equivFin _
  let M : ∀ r, Matrix (Fin (nr r)) (Fin (nr r)) k := fun r =>
    (J.toSquareBlock dd (r + 1)).reindex (eqv r) (eqv r)
  have hM : ∀ r, (M r).det = (J.toSquareBlock dd (r + 1)).det := fun r =>
    Matrix.det_reindex_self _ _
  let L : ∀ r, (Fin (nr r) → k) ≃ₗ[k] (Fin (nr r) → k) := fun r =>
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
  refine ⟨N, F, nr, q, L, rationalFiltration_zero G χ,
    rationalFiltration_eq_bot G χ hd hx hbij hN, fun r _ => rationalFiltration_succ_le G χ r,
    fun r _ => mem_normalizer_rationalFiltration G χ hg r, fun r _ => hqmul r, ?_, ?_,
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
    change ratCoord G χ x ⟨p'.1, hF0 r p'.2⟩ ((eqv r).symm j).1 =
      Matrix.toLin' (M r) (q r p) j
    rw [hp', ratCoord_conj G χ hd hx hbij hg ⟨p.1, hF0 r p.2⟩ p.2 ((eqv r).symm j).2,
      Matrix.toLin'_apply, sum_filter_eq_sum_fin dd (r + 1)]
    rfl
  · apply Units.ext
    rw [Units.coe_prod]
    have hdetL : ∀ r, (LinearEquiv.det (L r) : k) = (J.toSquareBlock dd (r + 1)).det := by
      intro r
      rw [LinearEquiv.coe_det]
      change LinearMap.det (Matrix.toLin' (M r)) = _
      rw [LinearMap.det_toLin', hM]
    simp only [hdetL]
    rw [prod_range_det_toSquareBlock dd J hd hN, ← hJprod, hJ]

end Langlands.Aubert.General.RationalPointFamily
