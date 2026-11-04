import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Langlands.GroupScheme.CentralSurjectionImage.GroupAlgebraCoeff
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Gradings of bialgebras by generalized eigenspaces of a right translation

Let `B` be a commutative bialgebra over a field `k` and `e : B → K` a point with values in an
algebraically closed field `K`. Right translation by `e` is an algebra endomorphism of
`V = K ⊗[k] B`, locally finite since `V` is a coalgebra over `K`. Its generalized eigenspaces
multiply according to their eigenvalues and are stable under all left translations. If `e` has
a convolution inverse, the eigenvalues are units, and the counits of the eigencomponents define a
bialgebra map `B → K[Kˣ]`. A grouplike element `g` is sent to the monomial of `e(g)`.
-/

noncomputable section

universe u

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.CentralSurjectionImage.EigenGrading

open AffineLinearEmbedding

variable (k : Type u) [Field k] (B : Type u) [CommRing B] [Bialgebra k B]
  (K : Type u) [Field K] [Algebra k K]

/-- The scalar extension `K ⊗[k] B`, a bialgebra over `K`. -/
abbrev V := K ⊗[k] B

variable {k B K}

/-- The `K`-linear extension of a `K`-valued point. -/
def extend (e : B →ₐ[k] K) : V k B K →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) e (fun _ _ => Commute.all _ _)

@[simp] theorem extend_tmul (e : B →ₐ[k] K) (c : K) (b : B) :
    extend e (c ⊗ₜ b) = c * e b := by
  simp [extend]

/-- Right translation by `e` on the elements `1 ⊗ b`: `b ↦ ∑ e(b₂) ⊗ b₁`. -/
def rho (e : B →ₐ[k] K) : B →ₐ[k] V k B K :=
  (Algebra.TensorProduct.productMap Algebra.TensorProduct.includeRight
    (((Algebra.ofId K (V k B K)).restrictScalars k).comp e)).comp (Bialgebra.comulAlgHom k B)

/-- Right translation by `e`, as a `K`-algebra endomorphism of `K ⊗[k] B`. -/
def rtAlg (e : B →ₐ[k] K) : V k B K →ₐ[K] V k B K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (V k B K)) (rho e) (fun _ _ => Commute.all _ _)

/-- The comultiplication of `K ⊗[k] B` on `1 ⊗ b`. -/
def incl2 : B ⊗[k] B →ₗ[k] V k B K ⊗[K] V k B K :=
  TensorProduct.lift
    (((TensorProduct.mk K (V k B K) (V k B K)).restrictScalars₁₂ k k).compl₁₂
      (Algebra.TensorProduct.includeRight : B →ₐ[k] V k B K).toLinearMap
      (Algebra.TensorProduct.includeRight : B →ₐ[k] V k B K).toLinearMap)

@[simp] theorem incl2_tmul (b₁ b₂ : B) :
    incl2 (K := K) (b₁ ⊗ₜ[k] b₂) = ((1 : K) ⊗ₜ[k] b₁) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] b₂) :=
  rfl

theorem comul_one_tmul (b : B) :
    Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[k] b : V k B K) = incl2 (Coalgebra.comul (R := k) b) := by
  rw [TensorProduct.comul_tmul]
  have h1 : Coalgebra.comul (R := K) (1 : K) = (1 : K) ⊗ₜ[K] (1 : K) := by
    simp [Coalgebra.comul]
  rw [h1]
  generalize Coalgebra.comul (R := k) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

/-- Right translation by the linear extension of `e` is the algebra map `rtAlg e`. -/
theorem rightAct_extend (e : B →ₐ[k] K) :
    rightAct (extend e).toLinearMap = (rtAlg e).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c b
  rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
  congr 1
  rw [rightAct_apply, comul_one_tmul, AlgHom.toLinearMap_apply, rtAlg,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul, rho, AlgHom.comp_apply]
  change _ = Algebra.TensorProduct.productMap _ _ (Coalgebra.comul (R := k) b)
  generalize Coalgebra.comul (R := k) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [incl2_tmul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, extend_tmul, one_mul,
      TensorProduct.rid_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.includeRight_apply, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
      Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, TensorProduct.smul_tmul', smul_eq_mul, Algebra.algebraMap_self,
      RingHom.id_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- Right translation by `e`, as a `K`-linear endomorphism. -/
abbrev rt (e : B →ₐ[k] K) : Module.End K (V k B K) := (rtAlg e).toLinearMap

theorem rt_eq_rightAct (e : B →ₐ[k] K) : rt e = rightAct (extend e).toLinearMap :=
  (rightAct_extend e).symm

/-- Left translations commute with right translation by `e`. -/
theorem commute_rt_leftAct (e : B →ₐ[k] K) (h : Module.Dual K (V k B K)) :
    Commute (rt e) (leftAct h) := by
  apply LinearMap.ext
  intro v
  change rt e (leftAct h v) = leftAct h (rt e v)
  rw [rt_eq_rightAct, rightAct_leftAct]

theorem counit_leftAct (h : Module.Dual K (V k B K)) (v : V k B K) :
    Coalgebra.counit (R := K) (leftAct h v) = h v := by
  rw [apply_leftAct, rightAct_counit]

/-- A left convolution inverse makes right translation injective. -/
theorem rt_injective (e e' : B →ₐ[k] K)
    (he' : ∀ b, Algebra.TensorProduct.productMap e' e (Coalgebra.comul (R := k) b) =
      algebraMap k K (Coalgebra.counit (R := k) b)) :
    Function.Injective (rt e) := by
  have hcomp : (extend e').toLinearMap ∘ₗ rightAct (extend e).toLinearMap =
      Coalgebra.counit (R := K) (A := V k B K) := by
    rw [rightAct_extend]
    apply TensorProduct.AlgebraTensorModule.ext
    intro c b
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, rtAlg,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul, rho, AlgHom.comp_apply,
      TensorProduct.counit_tmul]
    change _ = Coalgebra.counit (R := k) b • (1 : K)
    rw [Algebra.smul_def, mul_one, ← he' b]
    change (extend e') (Algebra.TensorProduct.productMap _ _ (Coalgebra.comul (R := k) b)) = _
    generalize Coalgebra.comul (R := k) b = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        Algebra.TensorProduct.includeRight_apply, extend_tmul, one_mul, AlgHom.comp_apply,
        AlgHom.coe_restrictScalars', Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, map_one, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  intro a a' h
  have h' := congrArg (rightAct (extend e').toLinearMap) h
  rw [rt_eq_rightAct, rightAct_rightAct, rightAct_rightAct, hcomp, rightAct_counit,
    rightAct_counit] at h'
  exact h'

/-- Generalized eigenvectors of an algebra endomorphism multiply according to their
eigenvalues. -/
theorem mul_mem_maxGenEigenspace {A : Type u} [CommRing A] [Algebra K A] (f : A →ₐ[K] A)
    {μ ν : K} {x y : A} (hx : x ∈ Module.End.maxGenEigenspace f.toLinearMap μ)
    (hy : y ∈ Module.End.maxGenEigenspace f.toLinearMap ν) :
    x * y ∈ Module.End.maxGenEigenspace f.toLinearMap (μ * ν) := by
  set F : Module.End K A := f.toLinearMap
  rw [Module.End.mem_maxGenEigenspace] at hx hy ⊢
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b = n → ∀ x y : A, ((F - μ • 1) ^ a) x = 0 →
      ((F - ν • 1) ^ b) y = 0 → ((F - (μ * ν) • 1) ^ n) (x * y) = 0 := by
    intro n
    induction n with
    | zero =>
      intro a b hab x y hx _
      obtain rfl : a = 0 := by omega
      rw [pow_zero, Module.End.one_apply] at hx
      rw [hx, zero_mul, map_zero]
    | succ n ih =>
      intro a b hab x y hx hy
      have hsplit : (F - (μ * ν) • 1) (x * y) =
          (F - μ • 1) x * F y + μ • (x * (F - ν • 1) y) := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          AlgHom.toLinearMap_apply, map_mul, F]
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [pow_succ, Module.End.mul_apply, hsplit, map_add, map_smul]
      have h1 : ((F - (μ * ν) • 1) ^ n) ((F - μ • 1) x * F y) = 0 := by
        rcases a with _ | a
        · rw [pow_zero, Module.End.one_apply] at hx
          rw [hx, map_zero, zero_mul, map_zero]
        · refine ih a b (by omega) _ _ ?_ ?_
          · rw [← Module.End.mul_apply, ← pow_succ]
            exact hx
          · have hc : Commute F ((F - ν • 1) ^ b) :=
              (Commute.sub_right (Commute.refl F) (Commute.smul_right (Commute.one_right F) ν)).pow_right b
            rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hy, map_zero]
      have h2 : ((F - (μ * ν) • 1) ^ n) (x * (F - ν • 1) y) = 0 := by
        rcases b with _ | b
        · rw [pow_zero, Module.End.one_apply] at hy
          rw [hy, map_zero, mul_zero, map_zero]
        · refine ih a b (by omega) _ _ hx ?_
          rw [← Module.End.mul_apply, ← pow_succ]
          exact hy
      rw [h1, h2, smul_zero, add_zero]
  exact key (a + b) a b rfl x y ha hb

/-! ### The generalized eigenspace decomposition -/

section Decomposition

variable [IsAlgClosed K] [DecidableEq K]

/-- The generalized eigenspaces of right translation by `e`. -/
abbrev eig (e : B →ₐ[k] K) (μ : K) : Submodule K (V k B K) :=
  Module.End.maxGenEigenspace (rt e) μ

omit [DecidableEq K] in
/-- Right translation is locally finite, so its generalized eigenspaces span. -/
theorem iSup_eig (e : B →ₐ[k] K) : ⨆ μ, eig e μ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨U, hUfg, hU⟩ := exists_fg_rightAct (K := K) (B := V k B K) v
  let W : Submodule K (V k B K) :=
    Submodule.span K (Set.range fun f : Module.Dual K (V k B K) => rightAct f v)
  have hWle : W ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact hU f
  have : FiniteDimensional K U := Module.Finite.iff_fg.mpr hUfg
  have : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWle
  have hvW : v ∈ W := by
    have := Submodule.subset_span (R := K)
      (Set.mem_range_self (f := fun f : Module.Dual K (V k B K) => rightAct f v)
        (Coalgebra.counit (R := K)))
    simpa using this
  have hstable : ∀ w : V k B K, w ∈ W → rt e w ∈ W := by
    intro w hw
    rw [rt_eq_rightAct]
    have hle : W ≤ W.comap (rightAct (extend e).toLinearMap) := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact Submodule.subset_span
        ⟨(extend e).toLinearMap ∘ₗ rightAct f, (rightAct_rightAct _ f v).symm⟩
    exact hle hw
  have htop := Module.End.iSup_maxGenEigenspace_eq_top ((rt e).restrict hstable)
  have hmem : (⟨v, hvW⟩ : W) ∈ ⨆ μ, Module.End.maxGenEigenspace ((rt e).restrict hstable) μ := by
    rw [htop]
    trivial
  have hmap := Submodule.mem_map_of_mem (f := W.subtype) hmem
  rw [Submodule.map_iSup] at hmap
  have hle : (⨆ μ, (Module.End.maxGenEigenspace ((rt e).restrict hstable) μ).map W.subtype) ≤
      ⨆ μ, eig e μ := by
    refine iSup_mono fun μ => ?_
    rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
    exact Submodule.map_comap_le _ _
  exact hle hmap

theorem isInternal_eig (e : B →ₐ[k] K) : DirectSum.IsInternal (eig e) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Module.End.independent_maxGenEigenspace (rt e)) (iSup_eig e)

/-- The generalized eigenspace decomposition of `K ⊗[k] B` under right translation by `e`. -/
@[instance_reducible]
noncomputable def decomposition (e : B →ₐ[k] K) : DirectSum.Decomposition (eig e) :=
  (isInternal_eig e).chooseDecomposition

omit [IsAlgClosed K] [DecidableEq K] in
/-- The zero generalized eigenspace vanishes when `e` has a left convolution inverse. -/
theorem eig_zero (e e' : B →ₐ[k] K)
    (he' : ∀ b, Algebra.TensorProduct.productMap e' e (Coalgebra.comul (R := k) b) =
      algebraMap k K (Coalgebra.counit (R := k) b)) :
    eig e 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨n, hn⟩ := hv
  rw [zero_smul, sub_zero, Module.End.pow_apply] at hn
  have hinj : Function.Injective (rt e)^[n] := (rt_injective e e' he').iterate n
  exact (Submodule.mem_bot K).mpr (hinj (hn.trans (by rw [Function.iterate_fixed (map_zero _)])))

omit [IsAlgClosed K] [DecidableEq K] in
/-- Right translation fixes `1`. -/
theorem one_mem_eig (e : B →ₐ[k] K) : (1 : V k B K) ∈ eig e 1 := by
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp [rt]

/-- The counit of the `μ`-component, a functional on `K ⊗[k] B`. -/
def wt (e : B →ₐ[k] K) (μ : K) : Module.Dual K (V k B K) :=
  letI := decomposition e
  Coalgebra.counit (R := K) ∘ₗ (eig e μ).subtype ∘ₗ
    DirectSum.component K K (fun ν => eig e ν) μ ∘ₗ
      (DirectSum.decomposeLinearEquiv (eig e)).toLinearMap

theorem wt_of_mem (e : B →ₐ[k] K) {μ ω : K} {w : V k B K} (hw : w ∈ eig e ω) :
    wt e μ w = if μ = ω then Coalgebra.counit (R := K) w else 0 := by
  let := decomposition e
  simp only [wt, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, Submodule.coe_subtype]
  rw [DirectSum.decompose_of_mem (eig e) hw, ← DirectSum.lof_eq_of K, DirectSum.component.of]
  by_cases h : μ = ω
  · subst h
    simp
  · simp [h, Ne.symm h]

omit [IsAlgClosed K] [DecidableEq K] in
/-- Contracting a comultiplication with two functionals is a left translation followed by the
second functional. -/
theorem mul'_map_comul (φ ψ : Module.Dual K (V k B K)) (v : V k B K) :
    LinearMap.mul' K K (TensorProduct.map φ ψ (Coalgebra.comul (R := K) v)) = ψ (leftAct φ v) := by
  rw [leftAct_apply]
  generalize Coalgebra.comul (R := K) v = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]

/-- The component counits are orthogonal idempotents for convolution. -/
theorem conv_wt (e : B →ₐ[k] K) (μ ν : K) (v : V k B K) :
    LinearMap.mul' K K (TensorProduct.map (wt e μ) (wt e ν) (Coalgebra.comul (R := K) v)) =
      if μ = ν then wt e μ v else 0 := by
  let := decomposition e
  induction v using DirectSum.Decomposition.inductionOn (eig e) with
  | zero => simp
  | homogeneous m =>
    rw [mul'_map_comul]
    have hl : leftAct (wt e μ) (m : V k B K) ∈ eig e _ :=
      Module.End.mapsTo_maxGenEigenspace_of_comm (commute_rt_leftAct e (wt e μ)) _ m.2
    rw [wt_of_mem e hl, counit_leftAct, wt_of_mem e m.2]
    split_ifs <;> simp_all
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    split_ifs <;> simp

/-- The index of a nonzero eigenvalue in the additive unit group. -/
def idx (μ : K) : Additive Kˣ :=
  if h : μ = 0 then 0 else Additive.ofMul (Units.mk0 μ h)

/-- The eigencomponent counits, assembled into a linear map to the group algebra of `Kˣ`. -/
def gradeLin (e : B →ₐ[k] K) : V k B K →ₗ[K] AddMonoidAlgebra K (Additive Kˣ) :=
  letI := decomposition e
  DirectSum.toModule K K (AddMonoidAlgebra K (Additive Kˣ))
      (fun μ => AddMonoidAlgebra.lsingle (idx μ) ∘ₗ Coalgebra.counit (R := K) ∘ₗ (eig e μ).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv (eig e)).toLinearMap

theorem gradeLin_of_mem (e : B →ₐ[k] K) {ω : K} {w : V k B K} (hw : w ∈ eig e ω) :
    gradeLin e w = AddMonoidAlgebra.single (idx ω) (Coalgebra.counit (R := K) w) := by
  let := decomposition e
  simp only [gradeLin, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (eig e) hw, ← DirectSum.lof_eq_of K, DirectSum.toModule_lof]
  simp [AddMonoidAlgebra.lsingle_apply]

omit [IsAlgClosed K] in
theorem idx_of_ne {μ : K} (hμ : μ ≠ 0) : idx μ = Additive.ofMul (Units.mk0 μ hμ) := by
  simp [idx, hμ]

omit [IsAlgClosed K] in
theorem idx_mul {μ ν : K} (hμ : μ ≠ 0) (hν : ν ≠ 0) : idx (μ * ν) = idx μ + idx ν := by
  rw [idx_of_ne (mul_ne_zero hμ hν), idx_of_ne hμ, idx_of_ne hν, ← ofMul_mul]
  congr 1
  ext
  simp

omit [IsAlgClosed K] in
theorem idx_one : idx (1 : K) = 0 := by
  rw [idx_of_ne one_ne_zero]
  change Additive.ofMul (Units.mk0 (1 : K) one_ne_zero) = Additive.ofMul 1
  congr 1
  ext
  simp

section Inverse

variable (e e' : B →ₐ[k] K)
  (he' : ∀ b, Algebra.TensorProduct.productMap e' e (Coalgebra.comul (R := k) b) =
    algebraMap k K (Coalgebra.counit (R := k) b))
include he'

/-- The coefficient of the grading at a unit `u` is the counit of the `u`-component. -/
theorem coeff_gradeLin (u : Kˣ) (v : V k B K) :
    (gradeLin e v).coeff (Additive.ofMul u) = wt e u v := by
  let := decomposition e
  induction v using DirectSum.Decomposition.inductionOn (eig e) with
  | zero => simp
  | @homogeneous ω m =>
    obtain ⟨w, hw⟩ := m
    rw [gradeLin_of_mem e hw, wt_of_mem e hw]
    by_cases hω0 : ω = 0
    · subst hω0
      rw [eig_zero e e' he'] at hw
      rw [(Submodule.mem_bot K).mp hw]
      simp
    · rw [idx_of_ne hω0, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h : (u : K) = ω
      · have hu : Units.mk0 ω hω0 = u := Units.ext (by simp [h])
        simp [hu, h]
      · have hu : Units.mk0 ω hω0 ≠ u := fun h' => h (by rw [← h']; simp)
        simp [hu, h]
  | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, map_add]

omit he' in
theorem gradeLin_one : gradeLin e 1 = 1 := by
  rw [gradeLin_of_mem e (one_mem_eig e), idx_one, AddMonoidAlgebra.one_def]
  congr 1
  exact (Bialgebra.counitAlgHom K (V k B K)).map_one

theorem gradeLin_mul (v w : V k B K) : gradeLin e (v * w) = gradeLin e v * gradeLin e w := by
  let := decomposition e
  induction v using DirectSum.Decomposition.inductionOn (eig e) with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, add_mul]
  | @homogeneous ω m =>
    obtain ⟨v, hv⟩ := m
    induction w using DirectSum.Decomposition.inductionOn (eig e) with
    | zero => simp
    | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
    | @homogeneous ω' m' =>
      obtain ⟨w, hw⟩ := m'
      have hvw : v * w ∈ eig e (ω * ω') := mul_mem_maxGenEigenspace (rtAlg e) hv hw
      change gradeLin e (v * w) = gradeLin e v * gradeLin e w
      rw [gradeLin_of_mem e hvw, gradeLin_of_mem e hv, gradeLin_of_mem e hw,
        AddMonoidAlgebra.single_mul_single, Bialgebra.counit_mul]
      by_cases hω : ω = 0
      · subst hω
        rw [eig_zero e e' he'] at hv
        rw [(Submodule.mem_bot K).mp hv]
        simp
      by_cases hω' : ω' = 0
      · subst hω'
        rw [eig_zero e e' he'] at hw
        rw [(Submodule.mem_bot K).mp hw]
        simp
      rw [idx_mul hω hω']

/-- The grading, as a `K`-algebra map `K ⊗[k] B → K[Kˣ]`. -/
def gradeAlg : V k B K →ₐ[K] AddMonoidAlgebra K (Additive Kˣ) :=
  AlgHom.ofLinearMap (gradeLin e) (gradeLin_one e) (gradeLin_mul e e' he')

end Inverse

omit [IsAlgClosed K] [DecidableEq K] in
/-- Contraction of a `k`-tensor of elements `1 ⊗ b` with two `K`-functionals. -/
theorem mul'_map_incl2 (f g : Module.Dual K (V k B K)) (t : B ⊗[k] B) :
    LinearMap.mul' k K (TensorProduct.map
        ((f.restrictScalars k) ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[k] V k B K).toLinearMap)
        ((g.restrictScalars k) ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[k] V k B K).toLinearMap)
        t) =
      LinearMap.mul' K K (TensorProduct.map f g (incl2 t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]

omit [IsAlgClosed K] [DecidableEq K] in
/-- A grouplike element `g` spans an eigenline of right translation, with eigenvalue `e(g)`. -/
theorem rt_one_tmul_grouplike (e : B →ₐ[k] K) {g : B}
    (hg : Coalgebra.comul (R := k) g = g ⊗ₜ g) :
    rt e ((1 : K) ⊗ₜ[k] g) = e g • ((1 : K) ⊗ₜ[k] g) := by
  rw [rt, AlgHom.toLinearMap_apply, rtAlg, Algebra.TensorProduct.lift_tmul, map_one, one_mul, rho, AlgHom.comp_apply]
  change Algebra.TensorProduct.productMap _ _ (Coalgebra.comul (R := k) g) = _
  rw [hg, Algebra.TensorProduct.productMap_apply_tmul]
  simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.comp_apply,
    AlgHom.coe_restrictScalars', Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, TensorProduct.smul_tmul', smul_eq_mul]

/-- **Grading by eigenvalues.** For a `K`-point `e` of a commutative `k`-bialgebra `B` with a
left convolution inverse, with `K` algebraically closed, there is a bialgebra map
`ψ : B → K[Kˣ]` sending every grouplike element `g` to the monomial of `e(g)`. -/
theorem exists_grading (e e' : B →ₐ[k] K)
    (he' : ∀ b, Algebra.TensorProduct.productMap e' e (Coalgebra.comul (R := k) b) =
      algebraMap k K (Coalgebra.counit (R := k) b)) :
    ∃ ψ : B →ₐ[k] AddMonoidAlgebra K (Additive Kˣ),
      (∀ b, AddMonoidAlgebra.mapDomainAlgHom k K (diagonal (Additive Kˣ)) (ψ b) =
        Algebra.TensorProduct.productMap
          ((AddMonoidAlgebra.mapDomainAlgHom k K (AddMonoidHom.inl _ _)).comp ψ)
          ((AddMonoidAlgebra.mapDomainAlgHom k K (AddMonoidHom.inr _ _)).comp ψ)
          (Coalgebra.comul (R := k) b)) ∧
      ∀ g : B, Coalgebra.comul (R := k) g = g ⊗ₜ g → Coalgebra.counit (R := k) g = 1 →
        ∃ h : e g ≠ 0, ψ g = AddMonoidAlgebra.single (Additive.ofMul (Units.mk0 (e g) h)) 1 := by
  let ψ : B →ₐ[k] AddMonoidAlgebra K (Additive Kˣ) :=
    ((gradeAlg e e' he').restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hψ : ∀ b (u : Kˣ), (ψ b).coeff (Additive.ofMul u) = wt e u ((1 : K) ⊗ₜ[k] b) := by
    intro b u
    exact coeff_gradeLin e e' he' u _
  refine ⟨ψ, fun b => ?_, fun g hg hgc => ?_⟩
  · ext ⟨a₁, a₂⟩
    obtain ⟨u₁, rfl⟩ : ∃ u : Kˣ, Additive.ofMul u = a₁ := ⟨Additive.toMul a₁, rfl⟩
    obtain ⟨u₂, rfl⟩ : ∃ u : Kˣ, Additive.ofMul u = a₂ := ⟨Additive.toMul a₂, rfl⟩
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply, coeff_mapDomain_diag, coeff_productMap_inl_inr']
    have hcoeff : ∀ u : Kˣ, coeffL k (Additive.ofMul u) ∘ₗ ψ.toLinearMap =
        (wt e u).restrictScalars k ∘ₗ
          (Algebra.TensorProduct.includeRight : B →ₐ[k] V k B K).toLinearMap := by
      intro u
      ext b
      exact hψ b u
    rw [hcoeff, hcoeff, mul'_map_incl2, ← comul_one_tmul, conv_wt, hψ]
    by_cases h : u₁ = u₂
    · subst h
      simp
    · have h' : (u₁ : K) ≠ u₂ := fun h'' => h (Units.ext h'')
      simp [h, h']
  · have hne : e g ≠ 0 := by
      intro h0
      have h1 := he' g
      rw [hg, Algebra.TensorProduct.productMap_apply_tmul, h0, mul_zero, hgc, map_one] at h1
      exact zero_ne_one h1
    refine ⟨hne, ?_⟩
    have hmem : (1 : K) ⊗ₜ[k] g ∈ eig e (e g) := by
      rw [Module.End.mem_maxGenEigenspace]
      refine ⟨1, ?_⟩
      simp [rt_one_tmul_grouplike e hg]
    change gradeLin e ((1 : K) ⊗ₜ[k] g) = _
    rw [gradeLin_of_mem e hmem, idx_of_ne hne, TensorProduct.counit_tmul, hgc]
    simp

end Decomposition

end Langlands.GroupScheme.CentralSurjectionImage.EigenGrading
