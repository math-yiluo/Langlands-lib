import Langlands.Representation.Archimedean.RealLeviBlockHaar

/-!
# The integral over a block orthogonal group in block lower unitriangular coordinates

Tools for the proof of `RealLeviParabolicIntegrationStatement`.

For a monotone block function `cl : Fin N → ι`, `CoordM cl` are the positions `(p, q)` with
`q < p` in the same block, and `lowerM cl Z` is the block diagonal lower unitriangular matrix with
the entries `Z`. The theorem `leviBorel` says, by strong induction on `N`:

* `Z ↦ ∏_l G_l(lowerM Z)^{-1}` is integrable;
* there is `C > 0` with `∫_{Kc cl} F = C ∫ F(lowerM Z) dZ` for every smooth `F` on `GL_N(ℝ)` with
  `F(diag(t) u g) = δ_B(t) F(g)`.

In the induction step the first block (of size `a`) is split off: `∫_{Kc cl}` is an iterated
integral over `O(a) × Kc (clR cl)` (`integral_Kc_eq`); the `O(a)`-integral is computed by
`integral_eq_borel` applied to a Levi slice, the `Kc (clR cl)`-integral by the induction
hypothesis applied to the other Levi slice, and the coordinates are put together by the
measure-preserving equivalence `embedM`, with `lowerM (embedM (Z₁, Z')) = diag(n̄(Z₁), lowerM Z')`.
The two exchanges of the order of integration are justified by the bound
`‖F(y κ)‖ ≤ C ∏_l G_l(y)^{-1}` (`norm_le_gram_inv`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviLeviBorel

open GramFormula MaximalParabolicIntegration RealLeviChartGram RealLeviChartIntegrable
  RealLeviTwoBlock RealLeviBorel RealLeviBlockHaar RealPrincipalSeriesDuality
  Langlands.GeneralLinear

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O

local instance borelSpaceK_lb (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {ι : Type*} [LinearOrder ι]

/-! ## Block diagonal lower unitriangular matrices -/

section Chart

/-- The coordinates `Z_{pq}`, `q < p` in the same block. -/
abbrev CoordM {N : ℕ} (cl : Fin N → ι) := {pq : Fin N × Fin N // cl pq.1 = cl pq.2 ∧ pq.2 < pq.1}

/-- The block diagonal lower unitriangular matrix with the entries `Z_{pq}`. -/
def lowerM {N : ℕ} (cl : Fin N → ι) (Z : CoordM cl → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun p q => if h : cl p = cl q ∧ q < p then Z ⟨(p, q), h⟩ else if p = q then 1 else 0

variable {N : ℕ} (cl : Fin N → ι)

theorem lowerM_isLowerTriangular (Z : CoordM cl → ℝ) : (lowerM cl Z).IsLowerTriangular := by
  intro p q hpq
  have hpq' : p < q := hpq
  have h1 : ¬ (cl p = cl q ∧ q < p) := fun h => lt_asymm hpq' h.2
  simp [lowerM, h1, hpq'.ne]

theorem det_lowerM (Z : CoordM cl → ℝ) : (lowerM cl Z).det = 1 := by
  rw [det_of_isLowerTriangular _ (lowerM_isLowerTriangular cl Z)]
  refine Finset.prod_eq_one fun p _ => ?_
  simp [lowerM]

theorem isUnit_lowerM (Z : CoordM cl → ℝ) : IsUnit (lowerM cl Z) :=
  (isUnit_iff_isUnit_det _).mpr (by rw [det_lowerM]; exact isUnit_one)

/-- `lowerM cl Z` as an element of `GL_N(ℝ)`. -/
def lowerMGL (Z : CoordM cl → ℝ) : Langlands.GeneralLinear N ℝ :=
  (isUnit_lowerM cl Z).unit

theorem lowerMGL_val (Z : CoordM cl → ℝ) :
    ((lowerMGL cl Z : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) = lowerM cl Z :=
  IsUnit.unit_spec _

theorem gram_lowerM_pos (Z : CoordM cl → ℝ) (l : ℕ) : 0 < gram l (lowerM cl Z) := by
  have h := gram_pos (lowerMGL cl Z) l
  rwa [lowerMGL_val] at h

theorem continuous_lowerM : Continuous (lowerM cl) := by
  refine continuous_matrix fun p q => ?_
  simp only [lowerM, of_apply]
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const

end Chart

/-! ## Splitting off the first block -/

section Peel

variable {a M : ℕ} {cl : Fin (a + M) → ι} {c0 : ι}

/-- The coordinates of `N̄_B` of the first block and the coordinates of the remaining blocks as
coordinates of `cl`. -/
def toCoordM (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0) :
    CoordC (vcl a) ⊕ CoordM (clR cl) → CoordM cl
  | .inl x => ⟨(Fin.castAdd M x.1.1, Fin.castAdd M x.1.2), (h1 _).trans (h1 _).symm,
      Fin.lt_def.mpr x.2⟩
  | .inr z => ⟨(Fin.natAdd a z.1.1, Fin.natAdd a z.1.2), z.2.1,
      (Fin.natAdd_lt_natAdd_iff a).mpr z.2.2⟩

theorem toCoordM_bijective (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)
    (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r)) : Function.Bijective (toCoordM h1) := by
  constructor
  · rintro (⟨⟨i, j⟩, hx⟩ | ⟨⟨r, s⟩, hz⟩) (⟨⟨i', j'⟩, hy⟩ | ⟨⟨r', s'⟩, hw⟩) h <;>
      replace h := congrArg Subtype.val h <;>
      simp only [toCoordM, Prod.mk.injEq] at h
    · rw [Fin.castAdd_inj, Fin.castAdd_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exact absurd h.1 (castAdd_ne_natAdd _ _)
    · exact absurd h.1 (natAdd_ne_castAdd _ _)
    · rw [Fin.natAdd_inj, Fin.natAdd_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · rintro ⟨⟨p, q⟩, h⟩
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => exact ⟨.inl ⟨(i, j), Fin.lt_def.mp h.2⟩, rfl⟩
      | right s =>
        exfalso
        have h' := h.1
        rw [h1] at h'
        exact (h2 s).ne h'
    | right r =>
      induction q using Fin.addCases with
      | left j =>
        exfalso
        have h' := h.1
        rw [h1] at h'
        exact (h2 r).ne h'.symm
      | right s => exact ⟨.inr ⟨(r, s), h.1, (Fin.natAdd_lt_natAdd_iff a).mp h.2⟩, rfl⟩

/-- `(Z₁, Z') ↦ Z`: the coordinates of the first block and of the remaining blocks put
together. -/
def embedM (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)
    (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r)) :
    ((CoordC (vcl a) → ℝ) × (CoordM (clR cl) → ℝ)) ≃ᵐ (CoordM cl → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : CoordC (vcl a) ⊕ CoordM (clR cl) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.ofBijective _ (toCoordM_bijective h1 h2)))

variable (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0) (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r))

theorem measurePreserving_embedM : MeasurePreserving (embedM h1 h2) volume volume := by
  have e1 := measurePreserving_piCongrLeft (fun _ : CoordM cl => (volume : Measure ℝ))
    (Equiv.ofBijective _ (toCoordM_bijective h1 h2))
  have e2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : CoordC (vcl a) ⊕ CoordM (clR cl) => ℝ)
  exact e1.comp e2

theorem embedM_inl (Z₁ : CoordC (vcl a) → ℝ) (Z' : CoordM (clR cl) → ℝ) (x : CoordC (vcl a)) :
    embedM h1 h2 (Z₁, Z') (toCoordM h1 (.inl x)) = Z₁ x := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordM_bijective h1 h2)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : CoordC (vcl a) ⊕ CoordM (clR cl) => ℝ)).symm (Z₁, Z')) (.inl x)
  exact h

theorem embedM_inr (Z₁ : CoordC (vcl a) → ℝ) (Z' : CoordM (clR cl) → ℝ) (z : CoordM (clR cl)) :
    embedM h1 h2 (Z₁, Z') (toCoordM h1 (.inr z)) = Z' z := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordM_bijective h1 h2)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : CoordC (vcl a) ⊕ CoordM (clR cl) => ℝ)).symm (Z₁, Z')) (.inr z)
  exact h

/-- `lowerM (embedM (Z₁, Z')) = diag(n̄(Z₁), lowerM Z')`. -/
theorem lowerM_embedM (Z₁ : CoordC (vcl a) → ℝ) (Z' : CoordM (clR cl) → ℝ) :
    lowerM cl (embedM h1 h2 (Z₁, Z')) = dg (lowerC (vcl a) Z₁) (lowerM (clR cl) Z') := by
  ext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j =>
      rw [dg_castAdd_castAdd]
      by_cases hij : j < i
      · have hij' : vcl a j < vcl a i := Fin.lt_def.mp hij
        rw [lowerM, of_apply, dite_eq_left ⟨(h1 i).trans (h1 j).symm,
          Fin.lt_def.mpr (Fin.lt_def.mp hij)⟩, lowerC, of_apply, dite_eq_left hij']
        exact embedM_inl h1 h2 Z₁ Z' ⟨(i, j), hij'⟩
      · have hij' : ¬ vcl a j < vcl a i := fun h => hij (Fin.lt_def.mpr h)
        rw [lowerM, of_apply,
          dite_eq_right fun h => hij (Fin.lt_def.mpr (Fin.lt_def.mp h.2)), lowerC, of_apply,
          dite_eq_right hij']
        simp only [Fin.castAdd_inj]
    | right s =>
      have hn : ¬ (cl (Fin.castAdd M i) = cl (Fin.natAdd a s) ∧
          Fin.natAdd a s < Fin.castAdd M i) := fun h => by
        have h' := h.1
        rw [h1] at h'
        exact (h2 s).ne h'
      rw [dg_castAdd_natAdd, lowerM, of_apply, dite_eq_right hn,
        ite_eq_right (castAdd_ne_natAdd i s)]
  | right r =>
    induction q using Fin.addCases with
    | left j =>
      have hn : ¬ (cl (Fin.natAdd a r) = cl (Fin.castAdd M j) ∧
          Fin.castAdd M j < Fin.natAdd a r) := fun h => by
        have h' := h.1
        rw [h1] at h'
        exact (h2 r).ne h'.symm
      rw [dg_natAdd_castAdd, lowerM, of_apply, dite_eq_right hn,
        ite_eq_right (natAdd_ne_castAdd r j)]
    | right s =>
      rw [dg_natAdd_natAdd]
      by_cases hrs : clR cl r = clR cl s ∧ s < r
      · rw [lowerM, of_apply, dite_eq_left ⟨hrs.1, (Fin.natAdd_lt_natAdd_iff a).mpr hrs.2⟩,
          lowerM, of_apply, dite_eq_left hrs]
        exact embedM_inr h1 h2 Z₁ Z' ⟨(r, s), hrs⟩
      · rw [lowerM, of_apply,
          dite_eq_right fun h => hrs ⟨h.1, (Fin.natAdd_lt_natAdd_iff a).mp h.2⟩,
          lowerM, of_apply, dite_eq_right hrs]
        simp only [Fin.natAdd_inj]

theorem lowerMGL_embedM (Z₁ : CoordC (vcl a) → ℝ) (Z' : CoordM (clR cl) → ℝ) :
    lowerMGL cl (embedM h1 h2 (Z₁, Z')) =
      dgGL (lowerCGL (vcl_monotone a) Z₁, lowerMGL (clR cl) Z') := by
  ext : 1
  rw [lowerMGL_val, dgGL_val, lowerCGL_val, lowerMGL_val]
  exact lowerM_embedM h1 h2 Z₁ Z'

end Peel

/-! ## Gram determinants of block diagonal matrices -/

theorem prod_gram_inv_dg {a M : ℕ} (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (hB : B.det = 1) :
    ∏ l : Fin (a + M), gram (l : ℕ) (dg A B) ^ (-1 : ℝ) =
      (∏ i : Fin a, gram (i : ℕ) A ^ (-1 : ℝ)) * ∏ r : Fin M, gram (r : ℕ) B ^ (-1 : ℝ) := by
  have hBB : (B * Bᵀ).det = 1 := by rw [det_mul, det_transpose, hB, mul_one]
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.val_castAdd, gram_dg_of_le A B i.2.le, hBB, mul_one]
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [Fin.val_natAdd, gram_dg_add]

/-! ## The integration formula -/

/-- **The integral over `Kc cl` in block lower unitriangular coordinates.** For a monotone block
function `cl`, `Z ↦ ∏_l G_l(lowerM Z)^{-1}` is integrable, and there is `C > 0` with
`∫_{Kc cl} F = C ∫ F(lowerM Z) dZ` for every smooth `F` with `F(diag(t) u g) = δ_B(t) F(g)`. -/
theorem leviBorel : ∀ (N : ℕ) (cl : Fin N → ι), Monotone cl →
    Integrable (fun Z : CoordM cl → ℝ => ∏ l : Fin N, gram (l : ℕ) (lowerM cl Z) ^ (-1 : ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ F : Langlands.GeneralLinear N ℝ → ℂ,
      ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
        ∫ k, F (k : Langlands.GeneralLinear N ℝ) ∂μc cl =
          (C : ℂ) * ∫ Z : CoordM cl → ℝ, F (lowerMGL cl Z) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro cl hcl
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (CoordM cl) := ⟨fun x => x.1.1.elim0⟩
    have hvol := volume_univ_of_isEmpty (CoordM cl) ℝ
    have : IsFiniteMeasure (volume : Measure (CoordM cl → ℝ)) :=
      ⟨by rw [hvol]; exact ENNReal.one_lt_top⟩
    refine ⟨?_, 1, one_pos, fun F _ _ => ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact integrable_const _
    · have e1 : ∀ k : Kc cl, F (k : Langlands.GeneralLinear 0 ℝ) = F 1 :=
        fun k => congrArg F (Subsingleton.elim _ _)
      have e2 : ∀ Z : CoordM cl → ℝ, F (lowerMGL cl Z) = F 1 :=
        fun Z => congrArg F (Subsingleton.elim _ _)
      simp only [e1, e2, integral_const, probReal_univ, one_smul, Complex.ofReal_one, one_mul]
      rw [Measure.real, hvol, ENNReal.toReal_one, one_smul]
  · obtain ⟨a, ha1, haN, hfirst, hrest⟩ := exists_first_block cl hcl hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le haN
    have h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = cl ⟨0, hN⟩ := fun j => hfirst _ (by simp)
    have h2 : ∀ r : Fin M, cl ⟨0, hN⟩ < cl (Fin.natAdd a r) := fun r => hrest _ (by simp)
    have hclR : Monotone (clR cl) := fun r s hrs => hcl (by
      rw [Fin.le_def] at hrs ⊢
      simp only [Fin.val_natAdd]
      omega)
    obtain ⟨hIR, CR, hCR, hBFR⟩ := ih M (by omega) (clR cl) hclR
    obtain ⟨Ca, hCa, hBFa⟩ := integral_eq_borel a
    have hmp := measurePreserving_embedM h1 h2
    -- the Gram bound is integrable
    have hI : Integrable fun Z : CoordM cl → ℝ =>
        ∏ l : Fin (a + M), gram (l : ℕ) (lowerM cl Z) ^ (-1 : ℝ) := by
      refine (hmp.integrable_comp_emb (embedM h1 h2).measurableEmbedding).mp ?_
      have e : (fun Z : CoordM cl → ℝ =>
          ∏ l : Fin (a + M), gram (l : ℕ) (lowerM cl Z) ^ (-1 : ℝ)) ∘ embedM h1 h2 =
          fun z => (∏ i : Fin a, gram (i : ℕ) (lowerC (vcl a) z.1) ^ (-1 : ℝ)) *
            ∏ r : Fin M, gram (r : ℕ) (lowerM (clR cl) z.2) ^ (-1 : ℝ) := by
        funext z
        obtain ⟨Z₁, Z'⟩ := z
        simp only [Function.comp_apply]
        rw [lowerM_embedM, prod_gram_inv_dg _ _ (det_lowerM _ _)]
      rw [e]
      exact (integrable_prod_gram_inv (vcl_monotone a)).mul_prod hIR
    refine ⟨hI, Ca * CR, mul_pos hCa hCR, fun F hFs hF => ?_⟩
    obtain ⟨B, hB⟩ := exists_bound hFs
    have hFc : Continuous fun k : Kc cl => F (k : Langlands.GeneralLinear (a + M) ℝ) :=
      hFs.continuous.comp continuous_subtype_val
    -- the first exchange of the order of integration (compact × compact)
    have hG : Integrable (Function.uncurry fun (k₁ : unitaryCompact ℝ a) (k₂ : Kc (clR cl)) =>
        F (dgGL ((k₁ : Langlands.GeneralLinear a ℝ), (k₂ : Langlands.GeneralLinear M ℝ))))
        ((haarK a).prod (μc (clR cl))) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
      show Continuous fun p : unitaryCompact ℝ a × Kc (clR cl) =>
        F (dgGL ((p.1 : Langlands.GeneralLinear a ℝ), (p.2 : Langlands.GeneralLinear M ℝ)))
      exact hFs.continuous.comp (continuous_dgGL.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)))
    -- the `O(a)`-integral
    have hstep3 : ∀ k₂ : Kc (clR cl),
        ∫ k₁ : unitaryCompact ℝ a,
          F (dgGL ((k₁ : Langlands.GeneralLinear a ℝ), (k₂ : Langlands.GeneralLinear M ℝ)))
            ∂haarK a =
        (Ca : ℂ) * ∫ Z₁ : CoordC (vcl a) → ℝ,
          F (dgGL (lowerCGL (vcl_monotone a) Z₁, (k₂ : Langlands.GeneralLinear M ℝ))) := by
      intro k₂
      have e1 : ∀ g : Langlands.GeneralLinear a ℝ,
          dgGL (g, 1) * dgGL (1, (k₂ : Langlands.GeneralLinear M ℝ)) =
            dgGL (g, (k₂ : Langlands.GeneralLinear M ℝ)) := by
        intro g
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      have h := hBFa (sliceL F (dgGL (1, (k₂ : Langlands.GeneralLinear M ℝ))))
        (contMDiff_sliceL hFs _) (sliceL_covariant hF _)
      simp only [sliceL, e1, abs_det_unitary, lowerCGL_val, det_lowerC (vcl_monotone a), abs_one,
        one_pow, inv_one, Complex.ofReal_one, mul_one] at h
      exact h
    -- the second exchange of the order of integration (compact × chart)
    have hH : Integrable (Function.uncurry fun (k₂ : Kc (clR cl)) (Z₁ : CoordC (vcl a) → ℝ) =>
        F (dgGL (lowerCGL (vcl_monotone a) Z₁, (k₂ : Langlands.GeneralLinear M ℝ))))
        ((μc (clR cl)).prod volume) := by
      obtain ⟨c', hc'⟩ : ∃ c' : ℝ,
          c' = ∏ r : Fin M, gram (r : ℕ) (1 : Matrix (Fin M) (Fin M) ℝ) ^ (-1 : ℝ) := ⟨_, rfl⟩
      refine ((integrable_const (B * c')).mul_prod
        (integrable_prod_gram_inv (vcl_monotone a))).mono' ?_ (ae_of_all _ fun p => ?_)
      · refine (continuous_comp_of_val hFs ?_).aestronglyMeasurable
        simp only [dgGL_val, lowerCGL_val]
        exact continuous_dg.comp ((continuous_lowerC.comp continuous_snd).prodMk
          (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)))
      · show ‖F (dgGL (lowerCGL (vcl_monotone a) p.2, (p.1 : Langlands.GeneralLinear M ℝ)))‖ ≤
          B * c' * ∏ i : Fin a, gram (i : ℕ) (lowerC (vcl a) p.2) ^ (-1 : ℝ)
        have e : dgGL (lowerCGL (vcl_monotone a) p.2, (p.1 : Langlands.GeneralLinear M ℝ)) =
            dgGL (lowerCGL (vcl_monotone a) p.2, 1) *
              dgGL (1, (p.1 : Langlands.GeneralLinear M ℝ)) := by
          rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
        have hk : dgGL ((1 : Langlands.GeneralLinear a ℝ), (p.1 : Langlands.GeneralLinear M ℝ)) ∈
            unitaryCompact ℝ (a + M) :=
          dgGL_mem_unitaryCompact (one_mem _) p.1.2.1
        have hy : gram 0 ((dgGL (lowerCGL (vcl_monotone a) p.2, 1) :
            Langlands.GeneralLinear (a + M) ℝ) : Matrix (Fin (a + M)) (Fin (a + M)) ℝ) = 1 := by
          rw [dgGL_val, RealLeviTorus.gram_zero_eq, det_dg, lowerCGL_val, det_lowerC (vcl_monotone a), Units.val_one,
            det_one]
          norm_num
        have h := norm_le_gram_inv hF hB _ hy hk
        rw [dgGL_val, lowerCGL_val, Units.val_one, prod_gram_inv_dg _ _ det_one, ← hc'] at h
        rw [e]
        refine h.trans (le_of_eq ?_)
        ring
    -- the `Kc (clR cl)`-integral
    have hstep5 : ∀ Z₁ : CoordC (vcl a) → ℝ,
        ∫ k₂ : Kc (clR cl),
          F (dgGL (lowerCGL (vcl_monotone a) Z₁, (k₂ : Langlands.GeneralLinear M ℝ)))
            ∂μc (clR cl) =
        (CR : ℂ) * ∫ Z' : CoordM (clR cl) → ℝ, F (lowerMGL cl (embedM h1 h2 (Z₁, Z'))) := by
      intro Z₁
      have e1 : ∀ h : Langlands.GeneralLinear M ℝ,
          dgGL (1, h) * dgGL (lowerCGL (vcl_monotone a) Z₁, 1) =
            dgGL (lowerCGL (vcl_monotone a) Z₁, h) := by
        intro h
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      have e2 : ∀ k₂ : Kc (clR cl),
          |((k₂ : Langlands.GeneralLinear M ℝ) : Matrix (Fin M) (Fin M) ℝ).det| = 1 :=
        fun k₂ => abs_det_unitary ⟨_, k₂.2.1⟩
      have h := hBFR (sliceR F (dgGL (lowerCGL (vcl_monotone a) Z₁, 1)))
        (contMDiff_sliceR hFs _) (sliceR_covariant hF _)
      simp only [sliceR, e1, e2, lowerMGL_val, det_lowerM, abs_one, one_pow, Complex.ofReal_one,
        mul_one] at h
      rw [h]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun Z' => ?_)
      exact congrArg F (lowerMGL_embedM h1 h2 Z₁ Z').symm
    -- integrability of `Z ↦ F(lowerM Z)`
    have hInt : Integrable fun Z : CoordM cl → ℝ => F (lowerMGL cl Z) := by
      refine (hI.const_mul B).mono' (continuous_comp_of_val hFs ?_).aestronglyMeasurable
        (ae_of_all _ fun Z => ?_)
      · simp only [lowerMGL_val]
        exact continuous_lowerM cl
      · have h := norm_le_gram_inv hF hB (lowerMGL cl Z)
          (by rw [lowerMGL_val, RealLeviTorus.gram_zero_eq, det_lowerM, one_pow])
          (one_mem (unitaryCompact ℝ (a + M)))
        simpa only [mul_one, lowerMGL_val] using h
    have hInt2 := hmp.integrable_comp_of_integrable hInt
    have h3 := hmp.integral_comp' (fun Z => F (lowerMGL cl Z))
    rw [Measure.volume_eq_prod] at h3 hInt2
    rw [integral_Kc_eq h1 h2 hFc]
    simp only [dgK_val]
    rw [integral_integral_swap hG, integral_congr_ae (ae_of_all _ hstep3), integral_const_mul,
      integral_integral_swap hH, integral_congr_ae (ae_of_all _ hstep5), integral_const_mul,
      ← integral_prod (fun z => F (lowerMGL cl (embedM h1 h2 z))) hInt2, h3, Complex.ofReal_mul,
      mul_assoc]

end RealLeviLeviBorel

end Langlands.Archimedean
