import Langlands.GroupScheme.Composition.CayleyOrthogonalFrame
import Langlands.LinearAlgebra.QuadraticWittExtension

/-! # Classification of Cayley algebras by the norm -/

noncomputable section

universe u

open Module LinearMap

namespace Langlands.GroupScheme.CayleyDatum

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

variable {K : Type u} [Field K] (c d : CayleyDatum K)

local notation "V" => CayleyVector K

private theorem form_isometry (e : c.norm.IsometryEquiv d.norm) (x y : V) :
    d.form (e x) (e y) = c.form x y := by
  simp only [form_apply, ← map_add e, e.map_app]

private theorem exists_orthogonal_nonzero_norm (h2 : (2 : K) ≠ 0) {ι : Type} [Fintype ι]
    (v : ι → V) (hv : c.form.iIsOrtho v) (hn : ∀ i, c.norm (v i) ≠ 0)
    (hcard : Fintype.card ι < 8) : ∃ z, (∀ i, c.form (v i) z = 0) ∧ c.norm z ≠ 0 := by
  have hdiag (i : ι) : c.form (v i) (v i) ≠ 0 := by
    rw [c.form_self]
    exact mul_ne_zero h2 (hn i)
  have hlin := LinearMap.BilinForm.linearIndependent_of_iIsOrtho hv hdiag
  let W := Submodule.span K (Set.range v)
  let b : Basis ι K W := Basis.span hlin
  have hb (i : ι) : (b i : V) = v i := Basis.coe_span_apply hlin i
  have hW : (c.form.restrict W).Nondegenerate := by
    refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
      (c.form.restrict W) b ?_).mpr ?_
    · intro i j hij
      change c.form (b i : V) (b j : V) = 0
      rw [hb, hb]
      exact hv hij
    · intro i
      change c.form (b i : V) (b i : V) ≠ 0
      rw [hb]
      exact hdiag i
  have hs : c.form.IsSymm := ⟨c.form_comm⟩
  let T := c.form.orthogonal W
  have hT : (c.form.restrict T).Nondegenerate := by
    apply (c.form.restrict_nondegenerate_iff_isCompl_orthogonal hs.isRefl).mpr
    change IsCompl T (c.form.orthogonal (c.form.orthogonal W))
    rw [c.form.orthogonal_orthogonal c.norm_nondegenerate hs.isRefl W]
    exact (c.form.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hW).symm
  let : Nontrivial T := Module.nontrivial_of_finrank_pos (R := K) (by
    change 0 < finrank K (c.form.orthogonal W)
    rw [c.form.finrank_orthogonal c.norm_nondegenerate W, finrank_span_eq_card hlin]
    simpa [CayleyVector] using Nat.sub_pos_of_lt hcard)
  have hex : ∃ z : T, c.norm (z : V) ≠ 0 := by
    by_contra! hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : T)
    apply hz (hT.1 z fun w => ?_)
    change c.form (z : V) (w : V) = 0
    rw [c.form_apply, ← Submodule.coe_add, hzero, hzero, hzero, sub_zero, sub_zero]
  obtain ⟨z, hz⟩ := hex
  exact ⟨z, fun i => z.property (v i) (Submodule.subset_span ⟨i, rfl⟩), hz⟩

private theorem exists_pure_pair (h2 : (2 : K) ≠ 0) :
    ∃ x y : V, c.trace x = 0 ∧ c.trace y = 0 ∧ c.form x y = 0 ∧
      c.norm x ≠ 0 ∧ c.norm y ≠ 0 := by
  obtain ⟨x, hx, hnx⟩ := c.exists_orthogonal_nonzero_norm h2 (fun _ : Unit => c.unit)
    (fun _ _ hij => (hij (Subsingleton.elim _ _)).elim) (by simp [c.norm_unit]) (by decide)
  have hxu : c.form c.unit x = 0 := hx ()
  have hux : c.form x c.unit = 0 := (c.form_comm _ _).trans hxu
  obtain ⟨y, hy, hny⟩ := c.exists_orthogonal_nonzero_norm h2 ![c.unit, x]
    (by
      intro i j hij
      change c.form (![c.unit, x] i) (![c.unit, x] j) = 0
      fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i <;> simp [c.norm_unit, hnx]) (by decide)
  exact ⟨x, y, hux, (c.form_comm _ _).trans (hy 0), hy 1, hnx, hny⟩

private structure Frame (c : CayleyDatum K) where
  x : V
  y : V
  z : V
  trace_x : c.trace x = 0
  trace_y : c.trace y = 0
  form_xy : c.form x y = 0
  form_z : ∀ i, c.form (c.leftFrameBlock x y c.unit i) z = 0
  norm_x : c.norm x ≠ 0
  norm_y : c.norm y ≠ 0
  norm_z : c.norm z ≠ 0

private theorem exists_matching_frames (h2 : (2 : K) ≠ 0)
    (e₀ : c.norm.IsometryEquiv d.norm) :
    ∃ (f : Frame c) (g : Frame d), c.norm f.x = d.norm g.x ∧
      c.norm f.y = d.norm g.y ∧ c.norm f.z = d.norm g.z := by
  have huv : d.norm (e₀ c.unit) = d.norm d.unit := by rw [e₀.map_app, c.norm_unit, d.norm_unit]
  obtain ⟨e₁, he₁, _⟩ := Langlands.QuadraticForm.exists_isometryEquiv_map_vector d.norm h2 huv
    (huv.symm ▸ (d.norm_unit.symm ▸ one_ne_zero))
  let e := e₀.trans e₁
  have he : e c.unit = d.unit := he₁
  obtain ⟨x, y, hx, hy, hxy, hnx, hny⟩ := c.exists_pure_pair h2
  let x' := e x
  let y' := e y
  have hx' : d.trace x' = 0 := by
    rw [trace, ← he]
    exact (c.form_isometry d e x c.unit).trans hx
  have hy' : d.trace y' = 0 := by
    rw [trace, ← he]
    exact (c.form_isometry d e y c.unit).trans hy
  have hxy' : d.form x' y' = 0 := (c.form_isometry d e x y).trans hxy
  let A := c.leftFrameBlock x y c.unit
  let B := d.leftFrameBlock x' y' d.unit
  have hnorm (i : Fin 4) : d.norm (B i) = c.norm (A i) := by
    fin_cases i <;> simp [A, B, x', y', leftFrameBlock, c.norm_unit, d.norm_unit,
      c.norm_mul, d.norm_mul, c.mul_unit, d.mul_unit, e.map_app]
  have hA := c.orthogonal_leftFrameBlock h2 hx hy hxy c.unit
  have hB := d.orthogonal_leftFrameBlock h2 hx' hy' hxy' d.unit
  have hdiag (i : Fin 4) : c.norm (A i) ≠ 0 := by
    fin_cases i <;> simp [A, leftFrameBlock, c.norm_unit, c.norm_mul, c.mul_unit, hnx, hny]
  let b := Pi.basisFun K (Fin 4)
  let I : (Fin 4 → K) →ₗ[K] V := b.constr K A
  let J : (Fin 4 → K) →ₗ[K] V := b.constr K B
  have hI (i : Fin 4) : I (b i) = A i := b.constr_basis K A i
  have hJ (i : Fin 4) : J (b i) = B i := b.constr_basis K B i
  let S := c.norm.comp I
  have hSp (i j : Fin 4) : S.polarBilin (b i) (b j) = c.form (A i) (A j) := by
    rw [show S = c.norm.comp I from rfl, QuadraticMap.polarBilin_comp]
    change c.form (I (b i)) (I (b j)) = _
    rw [hI, hI]
  have hJp (i j : Fin 4) : (d.norm.comp J).polarBilin (b i) (b j) = d.form (B i) (B j) := by
    rw [QuadraticMap.polarBilin_comp]
    change d.form (J (b i)) (J (b j)) = _
    rw [hJ, hJ]
  have hS : S.polarBilin.Nondegenerate := by
    refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
      S.polarBilin b ?_).mpr ?_
    · exact fun _ _ hij => (hSp _ _).trans (hA hij)
    · intro i
      rw [hSp, c.form_self]
      exact mul_ne_zero h2 (hdiag i)
  have hSJ : d.norm.comp J = S := by
    apply QuadraticMap.polarBilin_injective (isUnit_iff_ne_zero.mpr h2)
    apply b.ext
    intro i
    apply b.ext
    intro j
    change (d.norm.comp J).polarBilin (b i) (b j) = S.polarBilin (b i) (b j)
    rw [hSp, hJp]
    by_cases hij : i = j
    · subst j
      rw [d.form_self, c.form_self, hnorm]
    · rw [hA hij, hB hij]
  let : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨a, ha⟩ := Langlands.QuadraticForm.exists_isometryEquiv_match_embeddings d.norm S hS
    (e.toLinearEquiv.toLinearMap.comp I) J (fun w => e.map_app (I w))
    (fun w => DFunLike.congr_fun hSJ w)
  have hab (i : Fin 4) : a (e (A i)) = B i := by
    have h := ha (b i)
    change a (e (I (b i))) = J (b i) at h
    rwa [hI, hJ] at h
  obtain ⟨z, hz, hnz⟩ := c.exists_orthogonal_nonzero_norm h2 A hA hdiag (by decide)
  let z' := a (e z)
  have hz' (i : Fin 4) : d.form (B i) z' = 0 := by
    rw [← hab]
    exact (c.form_isometry d (e.trans a) (A i) z).trans (hz i)
  have hnz' : d.norm z' = c.norm z := (e.trans a).map_app z
  exact ⟨⟨x, y, z, hx, hy, hxy, hz, hnx, hny, hnz⟩,
    ⟨x', y', z', hx', hy', hxy', hz', (e.map_app x).symm ▸ hnx,
      (e.map_app y).symm ▸ hny, hnz'.symm ▸ hnz⟩,
    (e.map_app x).symm, (e.map_app y).symm, hnz'.symm⟩

namespace Frame

variable {c d}

private def vector (f : Frame c) := c.leftFrame f.x f.y f.z

private def basis (f : Frame c) (h2 : (2 : K) ≠ 0) : Basis (Fin 4 ⊕ Fin 4) K V :=
  c.leftFrameBasis h2 f.trace_x f.trace_y f.form_xy f.form_z f.norm_x f.norm_y f.norm_z

private theorem basis_apply (f : Frame c) (h2 : (2 : K) ≠ 0) (i : Fin 4 ⊕ Fin 4) :
    f.basis h2 i = f.vector i := c.leftFrameBasis_apply h2 _ _ _ _ _ _ _ i

private theorem vector_unit (f : Frame c) : f.vector (Sum.inl 0) = c.unit := rfl

private theorem vector_x (f : Frame c) : f.vector (Sum.inl 1) = f.x := c.mul_unit _

private theorem vector_y (f : Frame c) : f.vector (Sum.inl 2) = f.y := c.mul_unit _

private theorem vector_z (f : Frame c) : f.vector (Sum.inr 0) = f.z := rfl

private theorem orthogonal (f : Frame c) (h2 : (2 : K) ≠ 0) : c.form.iIsOrtho f.vector := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact c.orthogonal_leftFrameBlock h2 f.trace_x f.trace_y f.form_xy c.unit
      (fun h => hij (congrArg Sum.inl h))
  · exact c.form_leftFrameBlock_cross f.trace_x f.trace_y f.form_xy f.form_z i j
  · exact (c.form_comm _ _).trans
      (c.form_leftFrameBlock_cross f.trace_x f.trace_y f.form_xy f.form_z j i)
  · exact c.orthogonal_leftFrameBlock h2 f.trace_x f.trace_y f.form_xy f.z
      (fun h => hij (congrArg Sum.inr h))

private theorem trace_zero (f : Frame c) (h2 : (2 : K) ≠ 0) {i : Fin 4 ⊕ Fin 4}
    (hi : i ≠ Sum.inl 0) : c.trace (f.vector i) = 0 := f.orthogonal h2 hi

private theorem map_mul_of_generator (f : Frame c) (g : Frame d) (h2 : (2 : K) ≠ 0)
    (e : V ≃ₗ[K] V) (he : ∀ i, e (f.vector i) = g.vector i)
    (hnx : c.norm f.x = d.norm g.x) (hny : c.norm f.y = d.norm g.y)
    (hnz : c.norm f.z = d.norm g.z) :
    (∀ v, e (c.multiplication f.x v) = d.multiplication g.x (e v)) ∧
    (∀ v, e (c.multiplication f.y v) = d.multiplication g.y (e v)) ∧
    (∀ v, e (c.multiplication f.z v) = d.multiplication g.z (e v)) := by
  have extend (x y : V) (h : ∀ i, e (c.multiplication x (f.vector i)) =
      d.multiplication y (e (f.vector i))) (v : V) :
      e (c.multiplication x v) = d.multiplication y (e v) := by
    have hm : e.toLinearMap.comp (c.multiplication x) =
        (d.multiplication y).comp e.toLinearMap := (f.basis h2).ext fun i => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, f.basis_apply] using h i
    exact DFunLike.congr_fun hm v
  refine ⟨extend _ _ ?_, extend _ _ ?_, extend _ _ ?_⟩
  · intro i
    rw [he]
    rcases i with i | i
    · change e (c.multiplication f.x (c.leftFrameBlock f.x f.y c.unit i)) = _
      change _ = d.multiplication g.x (d.leftFrameBlock g.x g.y d.unit i)
      rw [c.mul_leftFrameBlock_x f.trace_x, d.mul_leftFrameBlock_x g.trace_x, map_smul, hnx]
      congr 1
      exact he (Sum.inl _)
    · change e (c.multiplication f.x (c.leftFrameBlock f.x f.y f.z i)) = _
      change _ = d.multiplication g.x (d.leftFrameBlock g.x g.y g.z i)
      rw [c.mul_leftFrameBlock_x f.trace_x, d.mul_leftFrameBlock_x g.trace_x, map_smul, hnx]
      congr 1
      exact he (Sum.inr _)
  · intro i
    rw [he]
    rcases i with i | i
    · change e (c.multiplication f.y (c.leftFrameBlock f.x f.y c.unit i)) = _
      change _ = d.multiplication g.y (d.leftFrameBlock g.x g.y d.unit i)
      rw [c.mul_leftFrameBlock_y f.trace_x f.trace_y f.form_xy,
        d.mul_leftFrameBlock_y g.trace_x g.trace_y g.form_xy, map_smul, hny]
      congr 1
      exact he (Sum.inl _)
    · change e (c.multiplication f.y (c.leftFrameBlock f.x f.y f.z i)) = _
      change _ = d.multiplication g.y (d.leftFrameBlock g.x g.y g.z i)
      rw [c.mul_leftFrameBlock_y f.trace_x f.trace_y f.form_xy,
        d.mul_leftFrameBlock_y g.trace_x g.trace_y g.form_xy, map_smul, hny]
      congr 1
      exact he (Sum.inr _)
  · have hcz : c.trace f.z = 0 := f.trace_zero h2 (i := Sum.inr 0) (by simp)
    have hdz : d.trace g.z = 0 := g.trace_zero h2 (i := Sum.inr 0) (by simp)
    have hczx : c.form f.z f.x = 0 := by
      rw [← f.vector_z, ← f.vector_x]
      exact f.orthogonal h2 (by simp)
    have hczy : c.form f.z f.y = 0 := by
      rw [← f.vector_z, ← f.vector_y]
      exact f.orthogonal h2 (by simp)
    have hdzx : d.form g.z g.x = 0 := by
      rw [← g.vector_z, ← g.vector_x]
      exact g.orthogonal h2 (by simp)
    have hdzy : d.form g.z g.y = 0 := by
      rw [← g.vector_z, ← g.vector_y]
      exact g.orthogonal h2 (by simp)
    have hc := c.mul_leftFrameBlock_of_orthogonal f.trace_x f.trace_y hcz hczx hczy
    have hd := d.mul_leftFrameBlock_of_orthogonal g.trace_x g.trace_y hdz hdzx hdzy
    intro i
    rw [he]
    rcases i with i | i
    · change e (c.multiplication f.z (c.leftFrameBlock f.x f.y c.unit i)) =
        d.multiplication g.z (d.leftFrameBlock g.x g.y d.unit i)
      rw [hc, hd, c.mul_unit, d.mul_unit, map_smul]
      congr 1
      exact he (Sum.inr i)
    · change e (c.multiplication f.z (c.leftFrameBlock f.x f.y f.z i)) =
        d.multiplication g.z (d.leftFrameBlock g.x g.y g.z i)
      rw [hc, hd, c.mul_self, d.mul_self, hcz, hdz, zero_smul, zero_smul, zero_sub, zero_sub,
        ← neg_smul, ← neg_smul, c.leftFrameBlock_smul, d.leftFrameBlock_smul,
        map_smul, map_smul, hnz]
      congr 2
      exact he (Sum.inl i)

private theorem map_mul (f : Frame c) (g : Frame d) (h2 : (2 : K) ≠ 0)
    (e : V ≃ₗ[K] V) (he : ∀ i, e (f.vector i) = g.vector i)
    (hnx : c.norm f.x = d.norm g.x) (hny : c.norm f.y = d.norm g.y)
    (hnz : c.norm f.z = d.norm g.z) (v w : V) :
    e (c.multiplication v w) = d.multiplication (e v) (e w) := by
  obtain ⟨hx, hy, hz⟩ := f.map_mul_of_generator g h2 e he hnx hny hnz
  have hblock (t : V) (j : Fin 4) : e (c.leftFrameBlock f.x f.y t j) =
      d.leftFrameBlock g.x g.y (e t) j := by
    fin_cases j <;> simp [leftFrameBlock, hx, hy]
  have extend (i : Fin 4 ⊕ Fin 4) (h : ∀ j,
      e (c.multiplication (f.vector i) (f.vector j)) =
        d.multiplication (g.vector i) (g.vector j)) :
      e (c.multiplication (f.vector i) w) = d.multiplication (e (f.vector i)) (e w) := by
    rw [he]
    have hm : e.toLinearMap.comp (c.multiplication (f.vector i)) =
        (d.multiplication (g.vector i)).comp e.toLinearMap := (f.basis h2).ext fun j => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, f.basis_apply, he] using h j
    exact DFunLike.congr_fun hm w
  have hm : e.toLinearMap.comp (c.multiplication.flip w) =
      (d.multiplication.flip (e w)).comp e.toLinearMap := by
    apply (f.basis h2).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, f.basis_apply]
    by_cases hu : i = Sum.inl 0
    · subst i
      rw [he, f.vector_unit, g.vector_unit, c.unit_mul, d.unit_mul]
    by_cases hix : i = Sum.inl 1
    · subst i
      rw [he, f.vector_x, g.vector_x]
      exact hx w
    by_cases hiy : i = Sum.inl 2
    · subst i
      rw [he, f.vector_y, g.vector_y]
      exact hy w
    by_cases hiz : i = Sum.inr 0
    · subst i
      rw [he, f.vector_z, g.vector_z]
      exact hz w
    have horth (a : CayleyDatum K) (k : Frame a) :
        a.trace (k.vector i) = 0 ∧ a.form (k.vector i) k.x = 0 ∧
          a.form (k.vector i) k.y = 0 ∧ a.form (k.vector i) k.z = 0 := by
      refine ⟨k.trace_zero h2 hu, ?_, ?_, ?_⟩
      · rw [← k.vector_x]; exact k.orthogonal h2 hix
      · rw [← k.vector_y]; exact k.orthogonal h2 hiy
      · rw [← k.vector_z]; exact k.orthogonal h2 hiz
    obtain ⟨hct, hcx, hcy, hcz⟩ := horth c f
    obtain ⟨hdt, hdx, hdy, hdz⟩ := horth d g
    have hcomm (a : CayleyDatum K) (k : Frame a) (ht : a.trace (k.vector i) = 0)
        (ho : a.form (k.vector i) k.z = 0) :
        a.multiplication (k.vector i) k.z = -a.multiplication k.z (k.vector i) := by
      apply eq_neg_of_add_eq_zero_left
      have ht' : a.trace k.z = 0 := k.trace_zero h2 (i := Sum.inr 0) (by simp)
      rw [a.mul_add_mul_comm, ht, ht', ho, zero_smul, zero_smul, zero_smul, zero_add, sub_zero]
    have hc := c.mul_leftFrameBlock_of_orthogonal f.trace_x f.trace_y hct hcx hcy
    have hd := d.mul_leftFrameBlock_of_orthogonal g.trace_x g.trace_y hdt hdx hdy
    apply extend i
    intro j
    rcases j with j | j
    · change e (c.multiplication (f.vector i) (c.leftFrameBlock f.x f.y c.unit j)) =
        d.multiplication (g.vector i) (d.leftFrameBlock g.x g.y d.unit j)
      rw [hc, hd, c.mul_unit, d.mul_unit, map_smul, hblock, he]
    · change e (c.multiplication (f.vector i) (c.leftFrameBlock f.x f.y f.z j)) =
        d.multiplication (g.vector i) (d.leftFrameBlock g.x g.y g.z j)
      rw [hc, hd, map_smul, hblock, hcomm c f hct hcz, hcomm d g hdt hdz, map_neg, hz, he]
  exact DFunLike.congr_fun hm v

end Frame

/-- A linear isomorphism of the unital multiplications preserves the intrinsic norm. -/
theorem norm_eq_of_preserves_mul_unit (e : V ≃ₗ[K] V) (hu : e c.unit = d.unit)
    (hm : ∀ x y, e (c.multiplication x y) = d.multiplication (e x) (e y)) (x : V) :
    d.norm (e x) = c.norm x := by
  by_cases hx : ∃ a : K, x = a • c.unit
  · obtain ⟨a, rfl⟩ := hx
    rw [map_smul, hu, d.norm.map_smul, c.norm.map_smul, d.norm_unit, c.norm_unit]
  have h : c.trace x • x - c.norm x • c.unit =
      d.trace (e x) • x - d.norm (e x) • c.unit := by
    apply e.injective
    calc
      _ = e (c.multiplication x x) := congrArg e (c.mul_self x).symm
      _ = d.multiplication (e x) (e x) := hm x x
      _ = _ := by rw [d.mul_self, map_sub, map_smul, map_smul, hu]
  have hrel : (c.trace x - d.trace (e x)) • x = (c.norm x - d.norm (e x)) • c.unit := by
    rw [sub_smul, sub_smul, ← sub_eq_zero]
    calc
      _ = (c.trace x • x - c.norm x • c.unit) -
          (d.trace (e x) • x - d.norm (e x) • c.unit) := by abel
      _ = 0 := sub_eq_zero.mpr h
  have ht : c.trace x - d.trace (e x) = 0 := by
    by_contra hne
    apply hx
    refine ⟨(c.trace x - d.trace (e x))⁻¹ * (c.norm x - d.norm (e x)), ?_⟩
    rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hun : c.unit ≠ 0 := by
    intro h
    have hnorm := c.norm_unit
    rw [h, map_zero] at hnorm
    exact zero_ne_one hnorm
  rw [ht, zero_smul] at hrel
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hrel.symm).resolve_right hun)).symm

/-- Isometric nonsingular Cayley norms give a linear isomorphism of the unital
multiplications in characteristic different from two. -/
theorem exists_preserves_mul_unit_of_norm_isometry (h2 : (2 : K) ≠ 0)
    (e₀ : c.norm.IsometryEquiv d.norm) :
    ∃ e : V ≃ₗ[K] V, e c.unit = d.unit ∧
      ∀ x y, e (c.multiplication x y) = d.multiplication (e x) (e y) := by
  obtain ⟨f, g, hx, hy, hz⟩ := c.exists_matching_frames d h2 e₀
  let e := (f.basis h2).equiv (g.basis h2) (Equiv.refl _)
  have he (i : Fin 4 ⊕ Fin 4) : e (f.vector i) = g.vector i := by
    rw [← f.basis_apply h2, ← g.basis_apply h2]
    simp only [e, Basis.equiv_apply, Equiv.refl_apply]
  have hu : e c.unit = d.unit := by
    simpa only [f.vector_unit, g.vector_unit] using he (Sum.inl 0)
  exact ⟨e, hu, f.map_mul g h2 e he hx hy hz⟩

/-- Over a field of characteristic different from two, the nonsingular norm
classifies Cayley data up to a linear isomorphism preserving the unit and product. -/
def NormClassificationStatement : Prop :=
  ∀ (K : Type u) [Field K], (2 : K) ≠ 0 → ∀ c d : CayleyDatum K,
    Nonempty (c.norm.IsometryEquiv d.norm) ↔
      ∃ e : CayleyVector K ≃ₗ[K] CayleyVector K, e c.unit = d.unit ∧
        ∀ x y, e (c.multiplication x y) = d.multiplication (e x) (e y)

/-- The two implications of the Cayley norm classification. -/
theorem normClassification : NormClassificationStatement.{u} := by
  intro K _ h2 c d
  constructor
  · rintro ⟨e⟩
    exact c.exists_preserves_mul_unit_of_norm_isometry d h2 e
  · rintro ⟨e, hu, hm⟩
    exact ⟨⟨e, c.norm_eq_of_preserves_mul_unit d e hu hm⟩⟩

end Langlands.GroupScheme.CayleyDatum
