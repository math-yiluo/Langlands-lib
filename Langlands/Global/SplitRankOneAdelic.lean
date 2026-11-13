import Langlands.Global.SplitRankOneLocalBounds
import Langlands.Global.PrimitiveAdelicGL2
import Langlands.Global.AdelicGroupNormOne
import Langlands.Global.AdelicSplitRankOneOrbitHeightBound

/-! # The split rank-one rational-orbit height bound

At every place we choose local bound data `(h_v, mu_v)`: a matrix and a scalar satisfying
the determinant-norm relation `(‖mu_v‖² ‖det h_v‖^k)^d = ‖η(g_v)‖²` and the upper bound
`‖ρ(g_v) ν(x)‖ ≤ B_v ‖mu_v‖ ‖h_v x‖^k`. At the finitely many bad places these data come from a
genuine binary-form similitude; at the good finite places (integral representation matrix,
unit character value) they are `h_v = 1`, `mu_v = 1`, which satisfy only the upper bound and
the relation, not an exact action identity. These data glue to an adelic `GL₂` matrix `h`; the
product formula for the line character makes `∏ ‖mu_v‖ · √|det h|^k = 1` on norm-one points,
and the `GL₂` Hermite bound produces a nonzero rational `r` with `H(h r) ≤ C √|det h|`. The
rational orbit point attached to `r` then has height at most a uniform constant. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Finset NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.SplitRankOne

open Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.Global.RepresentationGrowth

section Local

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {j : n} {i : T.toGrp ⟶ G} {α : characterLattice T}

/-- The binary-form coefficient bound `max(1, max_{l ≤ k} ‖w_l‖)` at a normed extension
field. -/
def wbound (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K] : ℝ :=
  max 1 ((range (D.k + 1)).sup' ⟨0, mem_range.mpr (Nat.succ_pos _)⟩ fun l => ‖wvec ρ j D.xm K l‖)

theorem one_le_wbound (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K] :
    1 ≤ wbound D K :=
  le_max_left _ _

theorem norm_wvec_le_wbound (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K]
    {l : ℕ} (hl : l ≤ D.k) : ‖wvec ρ j D.xm K l‖ ≤ wbound D K :=
  (le_sup' (fun l => ‖wvec ρ j D.xm K l‖) (mem_range.mpr (Nat.lt_succ_of_le hl))).trans
    (le_max_right _ _)

theorem wbound_eq_one (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K]
    (h : ∀ l ≤ D.k, ‖wvec ρ j D.xm K l‖ ≤ 1) : wbound D K = 1 :=
  max_eq_left (sup'_le _ _ fun l hl => h l (Nat.lt_succ_iff.mp (mem_range.mp hl)))

/-- **Local similitude.** Over a normed extension field, every point acts on the binary form
through a `GL₂`-substitution `h` and a scalar `mu` with
`(‖mu‖² ‖det h‖^k)^d = ‖η(g)‖²`. -/
theorem CellData.exists_local_similitude [Infinite F] (hG : IsConnectedReductive G)
    (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K]
    (g : G.affinePoints (CommAlgCat.of F K)) :
    ∃ (h : Matrix (Fin 2) (Fin 2) K) (mu : K), mu ≠ 0 ∧ h.det ≠ 0 ∧
      (‖mu‖ ^ 2 * ‖h.det‖ ^ D.k) ^ D.d =
        ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ ^ 2 ∧
      ∀ x : Fin 2 → K, ‖(ρ.affineMatrix (CommAlgCat.of F K) g : Matrix n n K) *ᵥ
          nu D.k (wvec ρ j D.xm K) x‖ = ‖mu‖ * ‖nu D.k (wvec ρ j D.xm K) (h *ᵥ x)‖ := by
  obtain ⟨c, ⟨h, mu, hmu, hdet, hc, hact⟩, hcd⟩ := D.exists_similitude hG K g
  refine ⟨h, mu, hmu, hdet, ?_, fun x => by rw [hact, norm_smul]⟩
  have hnc : ‖c‖ ^ D.d = ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ ^ 2 := by
    rw [← norm_pow c D.d, hcd, norm_pow]
  rw [← hnc, ← hc, norm_mul, norm_pow, norm_pow]

/-- **Archimedean local bound.** -/
theorem CellData.exists_infinite_local [Infinite F] (hG : IsConnectedReductive G)
    (D : CellData ρ j i α) (K : Type u) [NormedField K] [Algebra F K]
    (g : G.affinePoints (CommAlgCat.of F K)) :
    ∃ (h : Matrix (Fin 2) (Fin 2) K) (mu : K), mu ≠ 0 ∧ h.det ≠ 0 ∧
      (‖mu‖ ^ 2 * ‖h.det‖ ^ D.k) ^ D.d =
        ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ ^ 2 ∧
      ∀ x : Fin 2 → K, ‖(ρ.affineMatrix (CommAlgCat.of F K) g : Matrix n n K) *ᵥ
          nu D.k (wvec ρ j D.xm K) x‖ ≤
        ((D.k + 1) * wbound D K) * ‖mu‖ * ‖h *ᵥ x‖ ^ D.k := by
  obtain ⟨h, mu, hmu, hdet, hrel, hact⟩ := D.exists_local_similitude hG K g
  refine ⟨h, mu, hmu, hdet, hrel, fun x => ?_⟩
  rw [hact]
  calc ‖mu‖ * ‖nu D.k (wvec ρ j D.xm K) (h *ᵥ x)‖
      ≤ ‖mu‖ * (((D.k + 1) * wbound D K) * ‖h *ᵥ x‖ ^ D.k) :=
        mul_le_mul_of_nonneg_left
          (norm_nu_le D.k _ (fun l hl => norm_wvec_le_wbound D K hl) _) (norm_nonneg mu)
    _ = ((D.k + 1) * wbound D K) * ‖mu‖ * ‖h *ᵥ x‖ ^ D.k := by ring

/-- **Ultrametric local bound.** Over an ultrametric field, there are bound data `(h, mu)`
with the determinant-norm relation and the upper bound `‖ρ(g) ν(x)‖ ≤ wbound · ‖mu‖ · ‖h x‖^k`.
When the representation matrix is integral and the character value is a unit, the data are
`h = 1`, `mu = 1`; they then satisfy only this upper bound and the relation, not an exact
similitude identity. Otherwise they come from a genuine local similitude. -/
theorem CellData.exists_finite_local [Infinite F] (hG : IsConnectedReductive G)
    (D : CellData ρ j i α) (K : Type u) [NormedField K] [IsUltrametricDist K] [Algebra F K]
    (g : G.affinePoints (CommAlgCat.of F K)) :
    ∃ (h : Matrix (Fin 2) (Fin 2) K) (mu : K), mu ≠ 0 ∧ h.det ≠ 0 ∧
      (‖mu‖ ^ 2 * ‖h.det‖ ^ D.k) ^ D.d =
        ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ ^ 2 ∧
      ((∀ a b, ‖(ρ.affineMatrix (CommAlgCat.of F K) g : Matrix n n K) a b‖ ≤ 1) →
        ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ = 1 → h = 1 ∧ mu = 1) ∧
      ∀ x : Fin 2 → K, ‖(ρ.affineMatrix (CommAlgCat.of F K) g : Matrix n n K) *ᵥ
          nu D.k (wvec ρ j D.xm K) x‖ ≤ wbound D K * ‖mu‖ * ‖h *ᵥ x‖ ^ D.k := by
  have hB0 : 0 ≤ wbound D K := zero_le_one.trans (one_le_wbound D K)
  by_cases hgood : (∀ a b, ‖(ρ.affineMatrix (CommAlgCat.of F K) g : Matrix n n K) a b‖ ≤ 1) ∧
      ‖((etaUnits D.eta (CommAlgCat.of F K) g : Kˣ) : K)‖ = 1
  · refine ⟨1, 1, one_ne_zero, by simp, ?_, fun _ _ => ⟨rfl, rfl⟩, fun x => ?_⟩
    · rw [hgood.2]
      simp
    · rw [norm_one, mul_one, Matrix.one_mulVec]
      exact (norm_mulVec_le_of_norm_le_one _ hgood.1 _).trans
        (norm_nu_le_ultra D.k _ hB0 (fun l hl => norm_wvec_le_wbound D K hl) x)
  · obtain ⟨h, mu, hmu, hdet, hrel, hact⟩ := D.exists_local_similitude hG K g
    refine ⟨h, mu, hmu, hdet, hrel, fun h1 h2 => absurd ⟨h1, h2⟩ hgood, fun x => ?_⟩
    rw [hact]
    calc ‖mu‖ * ‖nu D.k (wvec ρ j D.xm K) (h *ᵥ x)‖
        ≤ ‖mu‖ * (wbound D K * ‖h *ᵥ x‖ ^ D.k) :=
          mul_le_mul_of_nonneg_left
            (norm_nu_le_ultra D.k _ hB0 (fun l hl => norm_wvec_le_wbound D K hl) _)
            (norm_nonneg mu)
      _ = wbound D K * ‖mu‖ * ‖h *ᵥ x‖ ^ D.k := by ring

end Local

section Adelic

variable {F : Type u} [Field F] [NumberField F]

/-- The finite projection as an `F`-algebra map. -/
def finiteAlgHom (v : FinitePlace F) : Adeles F →ₐ[F] FiniteCompletion F v :=
  { finiteProjection F v with commutes' := fun _ => rfl }

/-- The infinite projection as an `F`-algebra map. -/
def infiniteAlgHom (w : InfinitePlace F) : Adeles F →ₐ[F] InfiniteCompletion F w :=
  { infiniteProjection F w with commutes' := fun _ => rfl }

/-- Almost all finite components of finitely many adeles are integral. -/
theorem eventually_norm_finiteProjection_le_one {Idx : Type*} [Finite Idx] (x : Idx → Adeles F) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite, ∀ i, ‖finiteProjection F v (x i)‖ ≤ 1 := by
  have h : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => (x i).2.property
  filter_upwards [h] with v hv i
  change ‖(x i).2 v‖ ≤ 1
  simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff] using hv i

/-- Algebra maps out of the adeles commute with matrix action on principal vectors. -/
theorem map_mulVec_rational {m m' : ℕ} {K : Type*} [CommRing K] [Algebra F K]
    (φ : Adeles F →ₐ[F] K) (A : Matrix (Fin m') (Fin m) (Adeles F)) (u : Fin m → F) :
    (fun a => φ ((A *ᵥ PrimitiveAdelicHeight.rational F m u) a)) =
      A.map φ *ᵥ fun b => algebraMap F K (u b) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
    PrimitiveAdelicHeight.rational]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact φ.commutes (u b)

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The local point of an adelic point along an algebra map out of the adeles. -/
abbrev localPoint {K : Type u} [CommRing K] [Algebra F K] (φ : Adeles F →ₐ[F] K)
    (g : AdelicGroupPoints F G) : G.affinePoints (CommAlgCat.of F K) :=
  G.affinePointMap (CommAlgCat.ofHom φ) g

theorem affineMatrix_localPoint {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) {K : Type u}
    [CommRing K] [Algebra F K] (φ : Adeles F →ₐ[F] K) (g : AdelicGroupPoints F G) :
    (ρ.affineMatrix (CommAlgCat.of F K) (localPoint φ g) : Matrix (Fin n) (Fin n) K) =
      (adelicMatrix F G ρ g : Matrix (Fin n) (Fin n) (Adeles F)).map φ := by
  rw [localPoint, affinePointMap_apply, affineMatrix_naturality]
  rfl

theorem etaUnits_localPoint (eta : rationalCharacters G) {K : Type u} [CommRing K]
    [Algebra F K] (φ : Adeles F →ₐ[F] K) (g : AdelicGroupPoints F G) :
    ((etaUnits eta (CommAlgCat.of F K) (localPoint φ g) : Kˣ) : K) =
      φ ((AdelicGroupPoints.character F G eta.toMul g : Ideles F) : Adeles F) :=
  congrArg Units.val
    (AdelicGroupPoints.characterUnits_naturality F G eta.toMul (CommAlgCat.ofHom φ) g)

end Adelic

section Products

/-- Splitting a weighted product of triple products. -/
theorem prod_mul_mul_pow_pow {Idx : Type*} (s : Finset Idx) (a b c : Idx → ℝ) (m : Idx → ℕ) (k : ℕ) :
    ∏ i ∈ s, (a i * b i * c i ^ k) ^ m i =
      (∏ i ∈ s, a i ^ m i) * (∏ i ∈ s, b i ^ m i) * (∏ i ∈ s, c i ^ m i) ^ k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- Splitting a product of triple products. -/
theorem prod_mul_mul_pow {Idx : Type*} (s : Finset Idx) (a b c : Idx → ℝ) (k : ℕ) :
    ∏ i ∈ s, (a i * b i * c i ^ k) =
      (∏ i ∈ s, a i) * (∏ i ∈ s, b i) * (∏ i ∈ s, c i) ^ k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

end Products

section Glue

variable {F : Type u} [Field F] [NumberField F]

/-- **Gluing.** Invertible local `2 × 2` matrices at all places, almost all of them the
identity, are the local components of one adelic invertible matrix. -/
theorem exists_adelicGL_of_local
    (hi : ∀ w : InfinitePlace F, Matrix (Fin 2) (Fin 2) (InfiniteCompletion F w))
    (hf : ∀ v : FinitePlace F, Matrix (Fin 2) (Fin 2) (FiniteCompletion F v))
    (hdi : ∀ w, (hi w).det ≠ 0) (hdf : ∀ v, (hf v).det ≠ 0)
    (hone : ∀ᶠ v in Filter.cofinite, hf v = 1) :
    ∃ A : AdelicGL F 2, (∀ w, A.val.map (infiniteProjection F w) = hi w) ∧
      ∀ v, A.val.map (finiteProjection F v) = hf v := by
  classical
  let M : Matrix (Fin 2) (Fin 2) (Adeles F) := fun a b =>
    ((fun w => hi w a b), RestrictedProduct.mk (fun v => hf v a b) (by
      filter_upwards [hone] with v hv
      rw [hv, Matrix.one_apply]
      split_ifs
      · exact (v.adicCompletionIntegers F).one_mem
      · exact (v.adicCompletionIntegers F).zero_mem))
  have hMi : ∀ w, M.map (infiniteProjection F w) = hi w := fun w => by ext a b; rfl
  have hMf : ∀ v, M.map (finiteProjection F v) = hf v := fun v => by ext a b; rfl
  have hdi' : ∀ w, infiniteProjection F w M.det = (hi w).det := fun w => by
    rw [← hMi w]; exact RingHom.map_det (infiniteProjection F w) M
  have hdf' : ∀ v, finiteProjection F v M.det = (hf v).det := fun v => by
    rw [← hMf v]; exact RingHom.map_det (finiteProjection F v) M
  have hdet : IsUnit M.det := by
    refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => ?_, ?_⟩
    · change IsUnit (infiniteProjection F w M.det)
      rw [hdi' w]
      exact (hdi w).isUnit
    · refine RestrictedProduct.isUnit_of_eventually_isUnit (fun v => ?_) ?_
      · change IsUnit (finiteProjection F v M.det)
        rw [hdf' v]
        exact (hdf v).isUnit
      · filter_upwards [hone] with v hv
        have h1 : finiteProjection F v M.det = 1 := by rw [hdf' v, hv, Matrix.det_one]
        refine ⟨?_, ?_⟩
        · change finiteProjection F v M.det ∈ v.adicCompletionIntegers F
          rw [h1]
          exact (v.adicCompletionIntegers F).one_mem
        · convert isUnit_one
          exact h1
  exact ⟨Matrix.nonsingInvUnit M hdet, hMi, hMf⟩

end Glue

section Main

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {α : characterLattice T}

omit [NumberField F] in
theorem map_nu_wvec {n : Type} [Fintype n] [DecidableEq n] {ρ : MatrixRepresentation G n}
    {j : n} (xm : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ G) (k : ℕ)
    (K : Type u) [Field K] [Algebra F K] (r : Fin 2 → F) :
    (fun a => algebraMap F K (nu k (wvec ρ j xm F) r a)) =
      nu k (wvec ρ j xm K) (fun b => algebraMap F K (r b)) :=
  map_nu (algebraMap F K) k _ r

/-- **Uniform height bound from cell data.** -/
theorem CellData.uniformBound (hG : IsConnectedReductive G) {n : ℕ}
    {ρ : MatrixRepresentation G (Fin n)} {j : Fin n} (D : CellData ρ j i α) :
    HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1) := by
  classical
  obtain ⟨CH, hCH, hherm⟩ := PrimitiveAdelicHeight.exists_rationalHeight_le_sqrt_det F
  set Bi : InfinitePlace F → ℝ := fun w => (D.k + 1) * wbound D (InfiniteCompletion F w)
    with hBi_def
  set Bf : FinitePlace F → ℝ := fun v => wbound D (FiniteCompletion F v) with hBf_def
  have hBi1 : ∀ w, 1 ≤ Bi w := fun w => by
    have h1 := one_le_wbound D (InfiniteCompletion F w)
    have h2 : (1 : ℝ) ≤ D.k + 1 := by
      have := D.k.cast_nonneg (α := ℝ)
      linarith
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ _ := mul_le_mul h2 h1 zero_le_one (by linarith)
  have hBf1 : ∀ v, 1 ≤ Bf v := fun v => one_le_wbound D _
  have hBfev : ∀ᶠ v in Filter.cofinite, Bf v = 1 := by
    have h := eventually_norm_finiteProjection_le_one (F := F)
      (fun p : Fin (D.k + 1) × Fin n => diagonal F (wvec ρ j D.xm F p.1 p.2))
    filter_upwards [h] with v hv
    refine wbound_eq_one D _ fun l hl => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a => ?_
    exact hv (⟨l, Nat.lt_succ_of_le hl⟩, a)
  have hBfpos : 0 < ∏ᶠ v, Bf v :=
    lt_of_le_of_ne (finprod_nonneg fun v => zero_le_one.trans (hBf1 v))
      (Ne.symm (finprod_ne_zero fun v => (zero_lt_one.trans_le (hBf1 v)).ne'))
  refine ⟨(∏ w, Bi w ^ w.mult) * (∏ᶠ v, Bf v) * CH ^ D.k,
    mul_pos (mul_pos (Finset.prod_pos fun w _ => pow_pos (zero_lt_one.trans_le (hBi1 w)) _)
      hBfpos) (pow_pos hCH _), fun g => ?_⟩
  set g' : AdelicGroupPoints F G := (g : AdelicGroupPoints F G) with hg'
  choose hf muf hmuf hdetf hrelf hgoodf hboundf using fun v : FinitePlace F =>
    D.exists_finite_local hG (FiniteCompletion F v) (localPoint (finiteAlgHom v) g')
  choose hi mui hmui hdeti hreli hboundi using fun w : InfinitePlace F =>
    D.exists_infinite_local hG (InfiniteCompletion F w) (localPoint (infiniteAlgHom w) g')
  set x : Ideles F := AdelicGroupPoints.character F G D.eta.toMul g' with hx_def
  have hxn : (∏ w, ‖x.val.1 w‖ ^ w.mult) * ∏ᶠ v, ‖x.val.2 v‖ = 1 := by
    have h := (AdelicGroupPoints.mem_normOneSubgroup F G g').mp g.2 D.eta.toMul
    have h' := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) h
    simp only [Units.val_one, NNReal.coe_one] at h'
    rw [← IdeleAbsoluteValue.coe_full]
    exact h'
  have hrelf' : ∀ v, (‖muf v‖ ^ 2 * ‖(hf v).det‖ ^ D.k) ^ D.d = ‖x.val.2 v‖ ^ 2 := fun v =>
    (hrelf v).trans (by rw [etaUnits_localPoint]; rfl)
  have hreli' : ∀ w, (‖mui w‖ ^ 2 * ‖(hi w).det‖ ^ D.k) ^ D.d = ‖x.val.1 w‖ ^ 2 := fun w =>
    (hreli w).trans (by rw [etaUnits_localPoint]; rfl)
  have heta : ∀ᶠ v in Filter.cofinite, ‖x.val.2 v‖ = 1 :=
    Filter.eventually_cofinite.mpr
      (NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F x).2)
  have hone : ∀ᶠ v in Filter.cofinite, hf v = 1 ∧ muf v = 1 := by
    have hent := eventually_norm_finiteProjection_le_one (F := F)
      (fun p : Fin n × Fin n =>
        (adelicMatrix F G ρ g' : Matrix (Fin n) (Fin n) (Adeles F)) p.1 p.2)
    filter_upwards [hent, heta] with v hv1 hv2
    refine hgoodf v (fun a b => ?_) ?_
    · rw [affineMatrix_localPoint]
      exact hv1 (a, b)
    · rw [etaUnits_localPoint]
      exact hv2
  obtain ⟨A, hAi, hAf⟩ := exists_adelicGL_of_local hi hf hdeti hdetf (hone.mono fun v hv => hv.1)
  obtain ⟨r, hr, hH⟩ := hherm A
  obtain ⟨q, c, hc, hqc⟩ := D.exists_rational_orbit r hr
  refine ⟨q, ?_⟩
  rw [orbitHeight_mul_rational]
  have hej : (Pi.single j (1 : F) : Fin n → F) ≠ 0 := by
    intro h
    simpa using congrFun h j
  have hne := PrimitiveAdelicHeight.rational_mulVec_ne_zero F n (rationalMatrix F G ρ q) hej
  have hnu : nu D.k (wvec ρ j D.xm F) r ≠ 0 := by
    rw [hqc]
    exact smul_ne_zero hc hne
  have horb : orbitHeight F G ρ ((rationalMatrix F G ρ q).val *ᵥ Pi.single j 1) g' =
      PrimitiveAdelicHeight.rationalHeight F n (adelicMatrix F G ρ g')
        (nu D.k (wvec ρ j D.xm F) r) := by
    change PrimitiveAdelicHeight.rationalHeight F n (adelicMatrix F G ρ g')
      ((rationalMatrix F G ρ q).val *ᵥ Pi.single j 1) = _
    rw [hqc]
    exact (PrimitiveAdelicHeight.rationalHeight_smul F n _ (Units.mk0 c hc) _ hne).symm
  rw [horb]
  set Y := (adelicMatrix F G ρ g').val *ᵥ
    PrimitiveAdelicHeight.rational F n (nu D.k (wvec ρ j D.xm F) r) with hY
  set Z := A.val *ᵥ PrimitiveAdelicHeight.rational F 2 r with hZ
  have hYp : PrimitiveAdelicHeight.IsPrimitive F n Y := ⟨_, _, hnu, rfl⟩
  have hZp : PrimitiveAdelicHeight.IsPrimitive F 2 Z := ⟨A, r, hr, rfl⟩
  -- local identities
  have hYf : ∀ v, PrimitiveAdelicHeight.finiteNorm F n Y v ≤
      Bf v * ‖muf v‖ * PrimitiveAdelicHeight.finiteNorm F 2 Z v ^ D.k := fun v => by
    have e1 : PrimitiveAdelicHeight.finiteNorm F n Y v =
        ‖(ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) (localPoint (finiteAlgHom v) g') :
          Matrix (Fin n) (Fin n) _) *ᵥ nu D.k (wvec ρ j D.xm (FiniteCompletion F v))
            (fun b => algebraMap F _ (r b))‖ := by
      change ‖fun a => finiteAlgHom v (Y a)‖ = _
      rw [hY, map_mulVec_rational, map_nu_wvec, affineMatrix_localPoint]
    have e2 : PrimitiveAdelicHeight.finiteNorm F 2 Z v =
        ‖hf v *ᵥ (fun b => algebraMap F (FiniteCompletion F v) (r b))‖ := by
      change ‖fun a => finiteAlgHom v (Z a)‖ = _
      rw [hZ, map_mulVec_rational, ← hAf v]
      rfl
    rw [e1, e2]
    exact hboundf v _
  have hYi : ∀ w, PrimitiveAdelicHeight.infiniteNorm F n Y w ≤
      Bi w * ‖mui w‖ * PrimitiveAdelicHeight.infiniteNorm F 2 Z w ^ D.k := fun w => by
    have e1 : PrimitiveAdelicHeight.infiniteNorm F n Y w =
        ‖(ρ.affineMatrix (CommAlgCat.of F (InfiniteCompletion F w))
          (localPoint (infiniteAlgHom w) g') :
          Matrix (Fin n) (Fin n) _) *ᵥ nu D.k (wvec ρ j D.xm (InfiniteCompletion F w))
            (fun b => algebraMap F _ (r b))‖ := by
      change ‖fun a => infiniteAlgHom w (Y a)‖ = _
      rw [hY, map_mulVec_rational, map_nu_wvec, affineMatrix_localPoint]
    have e2 : PrimitiveAdelicHeight.infiniteNorm F 2 Z w =
        ‖hi w *ᵥ (fun b => algebraMap F (InfiniteCompletion F w) (r b))‖ := by
      change ‖fun a => infiniteAlgHom w (Z a)‖ = _
      rw [hZ, map_mulVec_rational, ← hAi w]
      rfl
    rw [e1, e2]
    exact hboundi w _
  -- the finite exceptional set
  have hev : ∀ᶠ v in Filter.cofinite, (hf v = 1 ∧ muf v = 1) ∧ Bf v = 1 ∧
      PrimitiveAdelicHeight.finiteNorm F n Y v = 1 ∧
      PrimitiveAdelicHeight.finiteNorm F 2 Z v = 1 ∧ ‖x.val.2 v‖ = 1 :=
    hone.and (hBfev.and ((hYp.eventually_finiteNorm_eq_one F n).and
      ((hZp.eventually_finiteNorm_eq_one F 2).and heta)))
  obtain ⟨S, hS⟩ : ∃ S : Finset (FinitePlace F), ∀ v ∉ S, (hf v = 1 ∧ muf v = 1) ∧ Bf v = 1 ∧
      PrimitiveAdelicHeight.finiteNorm F n Y v = 1 ∧
      PrimitiveAdelicHeight.finiteNorm F 2 Z v = 1 ∧ ‖x.val.2 v‖ = 1 :=
    ⟨(Filter.eventually_cofinite.mp hev).toFinset, fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset _).mpr h)⟩
  have hsub : ∀ f : FinitePlace F → ℝ, (∀ v ∉ S, f v = 1) → Function.mulSupport f ⊆ ↑S :=
    fun f hf1 v hv => by
      by_contra h
      exact hv (hf1 v h)
  have eY : ∏ᶠ v, PrimitiveAdelicHeight.finiteNorm F n Y v =
      ∏ v ∈ S, PrimitiveAdelicHeight.finiteNorm F n Y v :=
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun v hv => (hS v hv).2.2.1)
  have eZ : ∏ᶠ v, PrimitiveAdelicHeight.finiteNorm F 2 Z v =
      ∏ v ∈ S, PrimitiveAdelicHeight.finiteNorm F 2 Z v :=
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun v hv => (hS v hv).2.2.2.1)
  have eB : ∏ᶠ v, Bf v = ∏ v ∈ S, Bf v :=
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun v hv => (hS v hv).2.1)
  have eDet : ∏ᶠ v, ‖(hf v).det‖ = ∏ v ∈ S, ‖(hf v).det‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun v hv => by
      rw [(hS v hv).1.1, Matrix.det_one, norm_one])
  have eX : ∏ᶠ v, ‖x.val.2 v‖ = ∏ v ∈ S, ‖x.val.2 v‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun v hv => (hS v hv).2.2.2.2)
  -- the determinant of the glued matrix
  have hdetA : ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) =
      (∏ w, ‖(hi w).det‖ ^ w.mult) * ∏ v ∈ S, ‖(hf v).det‖ := by
    rw [IdeleAbsoluteValue.coe_full, ← eDet]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← hAi w]
      exact congrArg (fun z => ‖z‖ ^ w.mult) (RingHom.map_det (infiniteProjection F w) A.val)
    · refine finprod_congr fun v => ?_
      rw [← hAf v]
      exact congrArg (fun z => ‖z‖) (RingHom.map_det (finiteProjection F v) A.val)
  rw [hdetA] at hH
  -- the product formula
  set P := (∏ w, ‖mui w‖ ^ w.mult) * ∏ v ∈ S, ‖muf v‖ with hP
  set Δ := (∏ w, ‖(hi w).det‖ ^ w.mult) * ∏ v ∈ S, ‖(hf v).det‖ with hΔ
  have hP0 : 0 ≤ P := by positivity
  have hΔ0 : 0 ≤ Δ := by positivity
  have hPD : (P ^ 2 * Δ ^ D.k) ^ D.d = 1 := by
    have hx1 : (∏ w, ‖x.val.1 w‖ ^ w.mult) * ∏ v ∈ S, ‖x.val.2 v‖ = 1 := by
      rw [← eX]
      exact hxn
    calc (P ^ 2 * Δ ^ D.k) ^ D.d
        = (∏ w, ((‖mui w‖ ^ w.mult) ^ 2 * (‖(hi w).det‖ ^ w.mult) ^ D.k) ^ D.d) *
            ∏ v ∈ S, (‖muf v‖ ^ 2 * ‖(hf v).det‖ ^ D.k) ^ D.d := by
          simp only [hP, hΔ, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow]
          ring
      _ = (∏ w, (‖x.val.1 w‖ ^ w.mult) ^ 2) * ∏ v ∈ S, ‖x.val.2 v‖ ^ 2 := by
          congr 1
          · refine Finset.prod_congr rfl fun w _ => ?_
            calc ((‖mui w‖ ^ w.mult) ^ 2 * (‖(hi w).det‖ ^ w.mult) ^ D.k) ^ D.d
                = ((‖mui w‖ ^ 2 * ‖(hi w).det‖ ^ D.k) ^ D.d) ^ w.mult := by ring
              _ = (‖x.val.1 w‖ ^ 2) ^ w.mult := by rw [hreli' w]
              _ = (‖x.val.1 w‖ ^ w.mult) ^ 2 := by ring
          · exact Finset.prod_congr rfl fun v _ => hrelf' v
      _ = 1 := by rw [Finset.prod_pow, Finset.prod_pow, ← mul_pow, hx1, one_pow]
  have hPD1 : P ^ 2 * Δ ^ D.k = 1 :=
    (pow_eq_one_iff_of_nonneg (mul_nonneg (pow_nonneg hP0 _) (pow_nonneg hΔ0 _)) D.d_pos.ne').mp hPD
  have hPs : P * Real.sqrt Δ ^ D.k = 1 := by
    have h0 : 0 ≤ P * Real.sqrt Δ ^ D.k := mul_nonneg hP0 (pow_nonneg (Real.sqrt_nonneg _) _)
    refine (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp ?_
    rw [mul_pow, ← pow_mul, mul_comm D.k 2, pow_mul, Real.sq_sqrt hΔ0]
    exact hPD1
  -- the height estimate
  have hZh : PrimitiveAdelicHeight.height F 2 Z =
      (∏ w, PrimitiveAdelicHeight.infiniteNorm F 2 Z w ^ w.mult) *
        ∏ v ∈ S, PrimitiveAdelicHeight.finiteNorm F 2 Z v := by
    rw [PrimitiveAdelicHeight.height, eZ]
  have hH' : PrimitiveAdelicHeight.height F 2 Z ≤ CH * Real.sqrt Δ := hH
  have hZk : PrimitiveAdelicHeight.height F 2 Z ^ D.k ≤ (CH * Real.sqrt Δ) ^ D.k :=
    pow_le_pow_left₀ (hZp.height_pos F 2).le hH' _
  have hiY0 : ∀ w, 0 ≤ PrimitiveAdelicHeight.infiniteNorm F n Y w := fun w => norm_nonneg _
  have hfY0 : ∀ v, 0 ≤ PrimitiveAdelicHeight.finiteNorm F n Y v := fun v => norm_nonneg _
  have hiZ0 : ∀ w, 0 ≤ PrimitiveAdelicHeight.infiniteNorm F 2 Z w := fun w => norm_nonneg _
  have hfZ0 : ∀ v, 0 ≤ PrimitiveAdelicHeight.finiteNorm F 2 Z v := fun v => norm_nonneg _
  have hBi0 : ∀ w, 0 ≤ Bi w := fun w => zero_le_one.trans (hBi1 w)
  have hBf0 : ∀ v, 0 ≤ Bf v := fun v => zero_le_one.trans (hBf1 v)
  change PrimitiveAdelicHeight.height F n Y ≤ _
  calc PrimitiveAdelicHeight.height F n Y
      = (∏ w, PrimitiveAdelicHeight.infiniteNorm F n Y w ^ w.mult) *
          ∏ v ∈ S, PrimitiveAdelicHeight.finiteNorm F n Y v := by
        rw [PrimitiveAdelicHeight.height, eY]
    _ ≤ (∏ w, (Bi w * ‖mui w‖ * PrimitiveAdelicHeight.infiniteNorm F 2 Z w ^ D.k) ^ w.mult) *
          ∏ v ∈ S, (Bf v * ‖muf v‖ * PrimitiveAdelicHeight.finiteNorm F 2 Z v ^ D.k) := by
        refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ => pow_nonneg (hiY0 w) _)
          (fun w _ => pow_le_pow_left₀ (hiY0 w) (hYi w) _))
          (Finset.prod_le_prod₀ (fun v _ => hfY0 v) (fun v _ => hYf v))
          (Finset.prod_nonneg fun v _ => hfY0 v) ?_
        exact Finset.prod_nonneg fun w _ =>
          pow_nonneg (mul_nonneg (mul_nonneg (hBi0 w) (norm_nonneg _)) (pow_nonneg (hiZ0 w) _)) _
    _ = (∏ w, Bi w ^ w.mult) * (∏ v ∈ S, Bf v) * P *
          PrimitiveAdelicHeight.height F 2 Z ^ D.k := by
        rw [prod_mul_mul_pow_pow, prod_mul_mul_pow, hZh, hP]
        ring
    _ ≤ (∏ w, Bi w ^ w.mult) * (∏ v ∈ S, Bf v) * P * (CH * Real.sqrt Δ) ^ D.k := by
        refine mul_le_mul_of_nonneg_left hZk ?_
        have h1 : 0 ≤ ∏ v ∈ S, Bf v := Finset.prod_nonneg fun v _ => hBf0 v
        have h2 : 0 ≤ ∏ w, Bi w ^ w.mult := Finset.prod_nonneg fun w _ => pow_nonneg (hBi0 w) _
        exact mul_nonneg (mul_nonneg h2 h1) hP0
    _ = (∏ w, Bi w ^ w.mult) * (∏ᶠ v, Bf v) * CH ^ D.k * (P * Real.sqrt Δ ^ D.k) := by
        rw [eB]
        ring
    _ = (∏ w, Bi w ^ w.mult) * (∏ᶠ v, Bf v) * CH ^ D.k := by
        rw [hPs, mul_one]

end Main

end Langlands.Global.SplitRankOne

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme Langlands.Global.SplitRankOne

/-- **The split rank-one rational-orbit height bound.** -/
theorem splitRankOneParabolicRationalOrbitHeightBound :
    SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u} := by
  intro F _ _ G _ _ hG T i hi hmax ν hν α hα n ρ j hstab
  obtain ⟨D⟩ := nonempty_cellData hG i hi hmax ν hν α hα ρ j hstab
  exact D.uniformBound hG

end Langlands.Global.RepresentationGrowth
