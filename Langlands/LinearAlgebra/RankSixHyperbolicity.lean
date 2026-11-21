import Langlands.LinearAlgebra.SymmetricHyperbolicPair
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Hyperbolicity of rank-six symmetric forms with an isotropic plane -/

noncomputable section

universe u v

open Matrix

namespace Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- The quadratic form of the symmetric hyperbolic pairing on two scalar coordinates. -/
def hyperbolicPlane (K : Type u) [Field K] : QuadraticForm K (K × K) :=
  LinearMap.BilinMap.toQuadraticMap
    (((LinearMap.mul K K).compl₁₂ (LinearMap.fst K K K) (LinearMap.snd K K K)) +
      ((LinearMap.mul K K).compl₁₂ (LinearMap.snd K K K) (LinearMap.fst K K K)))

@[simp]
theorem hyperbolicPlane_apply {K : Type u} [Field K] (x : K × K) :
    hyperbolicPlane K x = x.1 * x.2 + x.2 * x.1 := rfl

/-- The orthogonal sum of three standard hyperbolic planes. -/
def threeHyperbolicPlanes (K : Type u) [Field K] :
    QuadraticForm K ((K × K) × (K × K) × (K × K)) :=
  (hyperbolicPlane K).prod ((hyperbolicPlane K).prod (hyperbolicPlane K))

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

private theorem exists_isotropic_in_complement (hS : B.IsSymm) (P : HyperbolicPair B)
    {x y : V} (hx : P.x = x) (hli : LinearIndependent K ![x, y])
    (hxy : B x y = 0) (hyy : B y y = 0) :
    ∃ z : P.orthogonalComplement, z ≠ 0 ∧ B z z = 0 := by
  let z := ((P.split hS).symm y).2
  let a := B P.y y
  have h : (z : V) = y - a • x := by
    rw [P.split_symm_snd, hx, hxy, zero_smul, sub_zero]
  have hxx : B x x = 0 := by rw [← hx, P.xx]
  have hyx := (hS.eq y x).trans hxy
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have ha : y - a • x = 0 := h.symm.trans (congrArg Subtype.val hz)
    have hrel : (-a) • x + (1 : K) • y = 0 := by rw [neg_smul, one_smul, add_comm, ← sub_eq_add_neg, ha]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) _ _ hrel).2
  · rw [h]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hxx, hxy, hyx, hyy,
      smul_zero, sub_zero]

/-- Reindexing a basis leaves the Gram determinant unchanged. -/
theorem det_reindex_basis {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (b : Module.Basis I K V) (e : I ≃ J) :
    (LinearMap.BilinForm.toMatrix (b.reindex e) B).det = (LinearMap.BilinForm.toMatrix b B).det := by
  have h : LinearMap.BilinForm.toMatrix (b.reindex e) B = Matrix.reindex e e (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [h, Matrix.det_reindex_self]

private theorem det_eq_neg_sq_in_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : Module.Basis I K V) (s : K)
    (h : (LinearMap.BilinForm.toMatrix b B).det = -(s ^ 2)) :
    ∃ t : K, (LinearMap.BilinForm.toMatrix c B).det = -(t ^ 2) := by
  refine ⟨(b.toMatrix c).det * s, ?_⟩
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, h]
  ring

private theorem exists_isotropic_of_binary_det (c : Module.Basis (Fin 2) K V)
    (ho : B.IsOrthoᵢ c) (hB : B.Nondegenerate) (hS : B.IsSymm)
    (s : K) (hd : (LinearMap.BilinForm.toMatrix c B).det = -(s ^ 2)) :
    ∃ z : V, z ≠ 0 ∧ B z z = 0 := by
  let a := B (c 0) (c 0)
  let b := B (c 1) (c 1)
  have ha : a ≠ 0 := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
    (v := c) ho hB 0
  have h01 : B (c 0) (c 1) = 0 := ho (by decide : (0 : Fin 2) ≠ 1)
  have h10 : B (c 1) (c 0) = 0 := (hS.eq _ _).trans h01
  have h : a * b = -(s ^ 2) := by
    rw [Matrix.det_fin_two] at hd
    simpa only [LinearMap.BilinForm.toMatrix_apply, h01, h10, zero_mul, sub_zero] using hd
  have hi : LinearIndependent K ![c 0, c 1] := by
    have he : ![c 0, c 1] = ⇑c := by funext i; fin_cases i <;> rfl
    rw [he]
    exact c.linearIndependent
  refine ⟨(s / a) • c 0 + c 1, ?_, ?_⟩
  · intro hz
    have hrel : (s / a) • c 0 + (1 : K) • c 1 = 0 := by simpa only [one_smul] using hz
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hi) _ _ hrel).2
  · simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      h01, h10, smul_eq_mul, mul_zero, zero_add, add_zero]
    change s / a * (s / a * a) + b = 0
    rw [div_mul_cancel₀ _ ha, div_mul_eq_mul_div, ← pow_two]
    rw [show s ^ 2 = -(a * b) by rw [h, neg_neg], neg_div, mul_comm a b, mul_div_cancel_right₀ _ ha,
      neg_add_cancel]

private theorem finrank_complement [FiniteDimensional K V] (P : HyperbolicPair B) (hS : B.IsSymm) :
    2 + Module.finrank K P.orthogonalComplement = Module.finrank K V := by
  have h := (P.split hS).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.one_add] using h

private def isometryEquiv_split (P : HyperbolicPair B) (hS : B.IsSymm) :
    ((hyperbolicPlane K).prod (B.restrict P.orthogonalComplement).toQuadraticMap).IsometryEquiv B.toQuadraticMap where
  toLinearEquiv := P.split hS
  map_app' p := by
    change B (P.split hS p) (P.split hS p) = p.1.1 * p.1.2 + p.1.2 * p.1.1 + B p.2 p.2
    exact P.split_pairing hS p p

private def lastPlaneIso (P : HyperbolicPair B) (hS : B.IsSymm)
    [Subsingleton P.orthogonalComplement] : (hyperbolicPlane K).IsometryEquiv B.toQuadraticMap := by
  let : Unique P.orthogonalComplement := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  let e : (K × K) ≃ₗ[K] V :=
    (LinearEquiv.prodUnique (R := K) (M := K × K) (M₂ := P.orthogonalComplement)).symm.trans (P.split hS)
  refine { toLinearEquiv := e, map_app' := fun p => ?_ }
  change B (P.split hS (p, 0)) (P.split hS (p, 0)) = p.1 * p.2 + p.2 * p.1
  rw [P.split_pairing]
  simp

/-- A nondegenerate six-dimensional symmetric form with an isotropic plane and
  Gram determinant negative a square is a sum of three hyperbolic planes. -/
theorem rankSix_hyperbolic [FiniteDimensional K V] [Invertible (2 : K)]
    (hS : B.IsSymm) (hB : B.Nondegenerate) (c : Module.Basis (Fin 6) K V)
    (s : K) (hd : (LinearMap.BilinForm.toMatrix c B).det = -(s ^ 2))
    (x y : V) (hli : LinearIndependent K ![x, y]) (hxx : B x x = 0) (hxy : B x y = 0) (hyy : B y y = 0) :
    Nonempty ((threeHyperbolicPlanes K).IsometryEquiv B.toQuadraticMap) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero _
  have hx : x ≠ 0 := by
    intro hx
    have hrel : (1 : K) • x + (0 : K) • y = 0 := by simp [hx]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) _ _ hrel).1
  obtain ⟨P, hPx⟩ := HyperbolicPair.exists_with_first hS hB h2 x hx hxx
  let W₁ := P.orthogonalComplement
  let B₁ := B.restrict W₁
  have hS₁ : B₁.IsSymm := ⟨fun p q => hS.eq (p : V) q⟩
  have hB₁ : B₁.Nondegenerate := P.nondegenerate_restrict hS hB
  obtain ⟨z, hz, hzz⟩ := exists_isotropic_in_complement hS P hPx hli hxy hyy
  obtain ⟨Q, _⟩ := HyperbolicPair.exists_with_first hS₁ hB₁ h2 z hz hzz
  let W₂ := Q.orthogonalComplement
  let B₂ := B₁.restrict W₂
  have hS₂ : B₂.IsSymm := ⟨fun p q => hS₁.eq (p : W₁) q⟩
  have hB₂ : B₂.Nondegenerate := Q.nondegenerate_restrict hS₁ hB₁
  have hdim : Module.finrank K V = 6 := by rw [Module.finrank_eq_card_basis c, Fintype.card_fin]
  have hdim₁ : 2 + Module.finrank K W₁ = Module.finrank K V := finrank_complement P hS
  have hdim₂ : 2 + Module.finrank K W₂ = Module.finrank K W₁ := finrank_complement Q hS₁
  have hd₂ : Module.finrank K W₂ = 2 := by omega
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hS₂)
  let e₂ := finCongr hd₂
  let b₂ := b.reindex e₂
  have hb₂ : B₂.IsOrthoᵢ b₂ := by
    intro i j hij
    change B₂ (b₂ i) (b₂ j) = 0
    simp only [b₂, Module.Basis.reindex_apply]
    exact hb (fun h => hij (e₂.symm.injective h))
  let b₀ := P.splitBasis hS (Q.splitBasis hS₁ b₂)
  let e : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin 6 := (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  obtain ⟨t, ht⟩ := det_eq_neg_sq_in_basis c (b₀.reindex e) s hd
  rw [det_reindex_basis b₀ e] at ht
  dsimp only [b₀] at ht
  rw [P.det_splitBasis, Q.det_splitBasis, neg_neg] at ht
  obtain ⟨w, hw, hww⟩ := exists_isotropic_of_binary_det b₂ hb₂ hB₂ hS₂ t ht
  obtain ⟨T, _⟩ := HyperbolicPair.exists_with_first hS₂ hB₂ h2 w hw hww
  have hdim₃ := finrank_complement T hS₂
  have hr : Module.finrank K T.orthogonalComplement = 0 := by omega
  let : Subsingleton T.orthogonalComplement := Module.finrank_zero_iff.mp hr
  let i₃ := lastPlaneIso T hS₂
  let i₂ := (QuadraticMap.IsometryEquiv.refl (hyperbolicPlane K)).prod i₃
  let i₁ := (QuadraticMap.IsometryEquiv.refl (hyperbolicPlane K)).prod (i₂.trans (isometryEquiv_split Q hS₁))
  exact ⟨i₁.trans (isometryEquiv_split P hS)⟩

/-- An isotropic plane and a negative-square Gram determinant force a nondegenerate
  symmetric form in dimension six to be hyperbolic in characteristic different from two. -/
def RankSixHyperbolicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [Invertible (2 : K)]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (c : Module.Basis (Fin 6) K V),
    B.IsSymm → B.Nondegenerate →
    (∃ s : K, (LinearMap.BilinForm.toMatrix c B).det = -(s ^ 2)) →
    (∃ x y : V, LinearIndependent K ![x, y] ∧ B x x = 0 ∧ B x y = 0 ∧ B y y = 0) →
    Nonempty ((threeHyperbolicPlanes K).IsometryEquiv B.toQuadraticMap)

theorem rankSixHyperbolicity : RankSixHyperbolicityStatement.{u, v} := by
  intro K _ _ V _ _ _ B c hs hb ⟨s, hd⟩ ⟨x, y, hi, hxx, hxy, hyy⟩
  exact rankSix_hyperbolic hs hb c s hd x y hi hxx hxy hyy

end Langlands.SymmetricBilinear
