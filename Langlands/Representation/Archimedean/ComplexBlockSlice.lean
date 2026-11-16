import Langlands.Representation.Archimedean.ComplexBlockDual

/-!
# Slices along the tied block: density and finite decomposition

Let `u` be a `U(a+k+1)`-finite function of the principal series of `χ⁻¹` on `GL_{a+k+1}(ℂ)`.
Its slices `g₂ ↦ u(diag(g₁, g₂))` lie in the principal series of the characters
`χT = ComplexBlockDual.blockDualChar a χ` of `GL_{k+1}(ℂ)`. This file proves two facts about
them.

* **Finite decomposition** (`ComplexBlockSlice.exists_blockDiag_decomposition`): there are finitely
  many `U(a+k+1)`-finite `p_i` of the principal series of `χ⁻¹` and `U(k+1)`-finite `φ_i` of the
  principal series of `χT` with `u(diag(g₁, g₂)) = ∑_i p_i(diag(g₁, 1)) φ_i(g₂)` for all `g₁, g₂`.
  Each `p_i` is a linear combination of right translates of `u` by elements `diag(1, κ)`,
  `κ ∈ U(k+1)`.
* **Density** (`ComplexBlockSlice.exists_mem_blockDiag_eq`): if the principal series of `χT` is
  irreducible, `U` is a `(𝔤, K)`-stable space of `U(a+k+1)`-finite functions of the principal
  series of `χ⁻¹`, `u ∈ U` and `φ` is a `U(k+1)`-finite function of the principal series of `χT`,
  then some `u' ∈ U` satisfies `u'(diag(g₁, g₂)) = u(diag(g₁, 1)) φ(g₂)` for all `g₁, g₂`.

The density statement is the first part of the proof of
`ComplexBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`, stated on its own and extended from
unitary `g₁` to all of `GL_a(ℂ)`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexBlockSlice

open ComplexBlockParabolic ComplexBlockChart ComplexBlockLimit ComplexBlockJacquet ComplexBlockDual
  ComplexPartialJacquet ComplexJacquetLimit ComplexGramFormula ComplexPrincipalSeriesExtension
  ComplexDuality Langlands.GeneralLinear

/-! ## Linear algebra: coordinate functionals as combinations of evaluations -/

/-- Let `W` be a finite-dimensional space of functions on `Y` whose elements are determined by
their values on `K ⊆ Y`. Every linear functional on `W` is a finite linear combination of
evaluations at points of `K`. -/
theorem exists_finsupp_eval {Y : Type*} (W : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W]
    (K : Set Y) (hK : ∀ w ∈ W, (∀ y ∈ K, w y = 0) → w = 0) (f : Module.Dual ℂ W) :
    ∃ c : Y →₀ ℂ, (∀ y ∈ c.support, y ∈ K) ∧
      ∀ w : W, f w = ∑ y ∈ c.support, c y * (w : Y → ℂ) y := by
  set ev : Y → Module.Dual ℂ W := fun y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype
    with hev
  have hS : Submodule.span ℂ (ev '' K) = ⊤ := by
    have h1 : (Submodule.span ℂ (ev '' K)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      have : (w : Y → ℂ) = 0 := hK w w.2 fun y hy =>
        hw (ev y) (Submodule.subset_span ⟨y, hy, rfl⟩)
      exact (Submodule.mem_bot ℂ).mpr (Subtype.ext this)
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := Submodule.span ℂ (ev '' K))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hf : f ∈ Submodule.span ℂ (ev '' K) := hS ▸ Submodule.mem_top
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hf
  refine ⟨c, fun y hy => hc hy, fun w => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul]
  rfl

/-! ## Restriction to `GL_a(ℂ)` on the full principal series -/

section Restrict

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- `g₁ ↦ u(diag(g₁, 1))` lies in the principal series of `(blockShiftChar k χ)⁻¹` on `GL_a(ℂ)`
for every `u` of the principal series of `χ⁻¹` (no finiteness needed). -/
theorem restrictBlock_mem_principalSeries (hχ : IsPhasePower χ e)
    {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ)) :
    restrictBlock (k := k) u ∈ principalSeries ℂ a (dualChar (blockShiftChar k χ)) := by
  refine ⟨contMDiff_restrictBlock hu.1, fun z v g => ?_⟩
  rw [restrictBlock_apply, restrictBlock_apply]
  have hsplit : blockDiagGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℂ) *
      (v : Langlands.GeneralLinear a ℂ) * g) (1 : Langlands.GeneralLinear (k + 1) ℂ) =
      (Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) :
        Langlands.GeneralLinear (a + (k + 1)) ℂ) *
      ((⟨blockDiagGL (v : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear (k + 1) ℂ),
        blockDiagGL_mem_upperUnipotent v⟩ : upperUnipotent (a + (k + 1)) ℂ) :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) * blockDiagGL g 1 := by
    rw [← blockDiagGL_diagonalUnits]
    change _ = blockDiagGL (Iwasawa.diagonalUnits z) 1 *
      blockDiagGL (v : Langlands.GeneralLinear a ℂ) 1 * blockDiagGL g 1
    rw [← blockDiagGL_mul, ← blockDiagGL_mul, one_mul, one_mul]
  rw [hsplit, hu.2, principalSeriesCharacter_addCases_dual hχ]

/-- Two functions of the principal series of `χ⁻¹` that agree on `diag(κ₁, 1)` for all unitary
`κ₁` agree on `diag(g₁, 1)` for all `g₁ ∈ GL_a(ℂ)`. -/
theorem blockDiag_eq_of_eqOn_unitary (hχ : IsPhasePower χ e)
    {v w : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hv : v ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hw : w ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (h : ∀ κ₁ ∈ unitaryCompact ℂ a, v (blockDiagGL κ₁ (1 : Langlands.GeneralLinear (k + 1) ℂ)) =
      w (blockDiagGL κ₁ (1 : Langlands.GeneralLinear (k + 1) ℂ)))
    (g₁ : Langlands.GeneralLinear a ℂ) :
    v (blockDiagGL g₁ (1 : Langlands.GeneralLinear (k + 1) ℂ)) =
      w (blockDiagGL g₁ (1 : Langlands.GeneralLinear (k + 1) ℂ)) := by
  have hm := restrictBlock_mem_principalSeries (k := k) hχ
    ((principalSeries ℂ (a + (k + 1)) (dualChar χ)).sub_mem hv hw)
  have h0 := eq_zero_of_mem_principalSeries_of_eqOn hm fun κ hκ => by
    rw [map_sub, Pi.sub_apply, restrictBlock_apply, restrictBlock_apply, h κ hκ, sub_self]
  have := congrFun h0 g₁
  rw [map_sub, Pi.sub_apply, restrictBlock_apply, restrictBlock_apply, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

end Restrict

/-! ## Finite decomposition along the tied block -/

section Decomposition

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} {χT : ℕ → ℂˣ → ℂ}

/-- **Finite decomposition of the slices.** Let `u` be a `U(a+k+1)`-finite function of the
principal series of `χ⁻¹`. There are `p_0, …, p_{d-1}`, each a `U(a+k+1)`-finite function of the
principal series of `χ⁻¹` lying in the span of the right translates of `u` by `U(a+k+1)`, and
`U(k+1)`-finite functions `φ_0, …, φ_{d-1}` of the principal series of `χT`, such that
`u(diag(g₁, g₂)) = ∑_i p_i(diag(g₁, 1)) φ_i(g₂)` for all `g₁ ∈ GL_a(ℂ)` and `g₂ ∈ GL_{k+1}(ℂ)`. -/
theorem exists_blockDiag_decomposition (hχ : IsPhasePower χ e)
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ, χT l z = blockDualChar a χ l z)
    {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1)))) :
    ∃ (d : ℕ) (p : Fin d → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
      (φ : Fin d → Langlands.GeneralLinear (k + 1) ℂ → ℂ),
      (∀ i, p i ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
        (unitaryCompact ℂ (a + (k + 1)))) ∧
      (∀ i, p i ∈ Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
          (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)) ∧
      (∀ i, φ i ∈ kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))) ∧
      ∀ (g₁ : Langlands.GeneralLinear a ℂ) (g₂ : Langlands.GeneralLinear (k + 1) ℂ),
        u (blockDiagGL g₁ g₂) = ∑ i, p i (blockDiagGL g₁ 1) * φ i g₂ := by
  -- the finite-dimensional span of the translates of `u`
  set V : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) :=
    Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u) with hVdef
  have hVfin : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hu.2
  have hVle : V ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    exact rightTranslation_mem_kFiniteFunctions_principalSeries _ _ hu κ.2
  -- the slices at `1` of `V`
  set W : Submodule ℂ (Langlands.GeneralLinear (k + 1) ℂ → ℂ) := V.map (sliceFun 1) with hWdef
  have hWfin : FiniteDimensional ℂ W := inferInstance
  have hWmem : ∀ w ∈ W,
      w ∈ kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact sliceFun_mem hχ hT (hVle hv) 1
  have hK : ∀ w ∈ W, (∀ y ∈ (unitaryCompact ℂ (k + 1) : Set (Langlands.GeneralLinear (k + 1) ℂ)),
      w y = 0) → w = 0 := fun w hw h0 =>
    eq_zero_of_mem_principalSeries_of_eqOn (hWmem w hw).1 h0
  have hslice : ∀ κ₁ : Langlands.GeneralLinear a ℂ, κ₁ ∈ unitaryCompact ℂ a →
      sliceFun κ₁ u ∈ W := by
    intro κ₁ hκ₁
    rw [sliceFun_eq_sliceFun_one]
    exact ⟨_, Submodule.subset_span ⟨⟨blockDiagGL κ₁ 1,
      blockDiagGL_mem_unitaryCompact hκ₁ (unitaryCompact ℂ (k + 1)).one_mem⟩, rfl⟩, rfl⟩
  -- a basis of `W` and its coordinate functionals as combinations of evaluations
  set b := Module.finBasis ℂ W with hbdef
  choose c hcK hc using fun i => exists_finsupp_eval W _ hK (b.coord i)
  set p : Fin (Module.finrank ℂ W) → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ := fun i =>
    ∑ y ∈ (c i).support, c i y • Whittaker.rightTranslation ℂ
      (Langlands.GeneralLinear (a + (k + 1)) ℂ) (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) y) u
    with hpdef
  have hpV : ∀ i, p i ∈ V := fun i =>
    Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨blockDiagGL 1 y, blockDiagGL_mem_unitaryCompact (unitaryCompact ℂ a).one_mem
        (hcK i y hy)⟩, rfl⟩)
  -- the identity for unitary `κ₁`
  have hunit : ∀ κ₁ ∈ unitaryCompact ℂ a, ∀ g₂ : Langlands.GeneralLinear (k + 1) ℂ,
      u (blockDiagGL κ₁ g₂) = ∑ i, p i (blockDiagGL κ₁ 1) * (b i : Langlands.GeneralLinear
        (k + 1) ℂ → ℂ) g₂ := by
    intro κ₁ hκ₁ g₂
    set s : W := ⟨sliceFun κ₁ u, hslice κ₁ hκ₁⟩ with hsdef
    have hrepr := congrArg (fun w : W => (w : Langlands.GeneralLinear (k + 1) ℂ → ℂ) g₂)
      (b.sum_repr s)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hsdef, sliceFun_apply] at hrepr
    rw [← hrepr]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Module.Basis.coord_apply, hc i s]
    simp only [hpdef, Finset.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hsdef, sliceFun_apply]
    congr 1
    change u (blockDiagGL κ₁ y) = u (blockDiagGL κ₁ 1 * blockDiagGL 1 y)
    rw [← blockDiagGL_mul, mul_one, one_mul]
  refine ⟨Module.finrank ℂ W, p, fun i => (b i : Langlands.GeneralLinear (k + 1) ℂ → ℂ),
    fun i => hVle (hpV i), hpV, fun i => hWmem _ (b i).2, fun g₁ g₂ => ?_⟩
  -- extension from unitary `κ₁` to all of `GL_a(ℂ)`
  have hv : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
      (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g₂) u ∈
        principalSeries ℂ (a + (k + 1)) (dualChar χ) :=
    rightTranslation_mem_principalSeries _ hu.1 _
  have hw : (∑ i, (b i : Langlands.GeneralLinear (k + 1) ℂ → ℂ) g₂ • p i) ∈
      principalSeries ℂ (a + (k + 1)) (dualChar χ) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hVle (hpV i)).1
  have key := blockDiag_eq_of_eqOn_unitary hχ hv hw (fun κ₁ hκ₁ => by
    change u (blockDiagGL κ₁ 1 * blockDiagGL 1 g₂) = _
    rw [← blockDiagGL_mul, mul_one, one_mul, hunit κ₁ hκ₁ g₂, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]) g₁
  change u (blockDiagGL g₁ 1 * blockDiagGL 1 g₂) = _ at key
  rw [← blockDiagGL_mul, mul_one, one_mul, Finset.sum_apply] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]

end Decomposition

/-! ## Density on the tied block -/

section Density

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} {χT : ℕ → ℂˣ → ℂ}

/-- **Density on the tied block.** Assume the principal series of `χT = blockDualChar a χ` (on
`l < k+1`) of `GL_{k+1}(ℂ)` is irreducible. Let `U` be a space of `U(a+k+1)`-finite functions of
the principal series of `χ⁻¹`, stable under right translation by `U(a+k+1)` and under right
derivatives. For every `u ∈ U` and every `U(k+1)`-finite `φ` of the principal series of `χT` there
is `u' ∈ U` with `u'(diag(g₁, g₂)) = u(diag(g₁, 1)) φ(g₂)` for all `g₁ ∈ GL_a(ℂ)` and
`g₂ ∈ GL_{k+1}(ℂ)`. -/
theorem exists_mem_blockDiag_eq (hχ : IsPhasePower χ e)
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ, χT l z = blockDualChar a χ l z)
    (hirr : IsIrreducibleGKModule (principalSeriesRep ℂ (k + 1) χT)
      (principalSeriesLie ℂ (k + 1) χT))
    {U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1))))
    (hUK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u ∈ U)
    (hUD : ∀ (X : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (a + (k + 1))) X u ∈ U)
    {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ} (hu : u ∈ U)
    {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ}
    (hφ : φ ∈ kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))) :
    ∃ u' ∈ U, ∀ (g₁ : Langlands.GeneralLinear a ℂ) (g₂ : Langlands.GeneralLinear (k + 1) ℂ),
      u' (blockDiagGL g₁ g₂) = u (blockDiagGL g₁ 1) * φ g₂ := by
  set u0 : U := ⟨u, hu⟩ with hu0
  -- a finite-dimensional space containing all slices of `u` at unitary `κ₁`
  set W : Submodule ℂ (Langlands.GeneralLinear (k + 1) ℂ → ℂ) :=
    (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)).map (sliceFun 1) with hWdef
  have hWfin : FiniteDimensional ℂ W := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ
        (a + (k + 1)) => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
          (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)) :=
      (mem_kFiniteVectors_iff _ _ _).mp (hU hu).2
    infer_instance
  set S : Submodule ℂ (kFiniteFunctions (principalSeries ℂ (k + 1) χT)
    (unitaryCompact ℂ (k + 1))) :=
    W.comap (kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))).subtype
    with hSdef
  have hSfin : FiniteDimensional ℂ S := by
    refine Module.Finite.of_injective (LinearMap.codRestrict W
      ((kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))).subtype ∘ₗ
        S.subtype) fun x => x.2) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W =>
      (z : Langlands.GeneralLinear (k + 1) ℂ → ℂ)) hxy))
  have hslice : ∀ κ₁ ∈ unitaryCompact ℂ a, sliceV hχ hT hU κ₁ u0 ∈ S := by
    intro κ₁ hκ₁
    change sliceFun κ₁ u ∈ W
    rw [sliceFun_eq_sliceFun_one]
    refine ⟨_, Submodule.subset_span ⟨⟨blockDiagGL κ₁ 1,
      blockDiagGL_mem_unitaryCompact hκ₁ (unitaryCompact ℂ (k + 1)).one_mem⟩, rfl⟩, rfl⟩
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).mpr hSfin
  -- the rank-one target map `v ↦ v(1) φ`
  set φ' : kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)) :=
    ⟨φ, hφ⟩ with hφ'
  set f : Module.End ℂ (kFiniteFunctions (principalSeries ℂ (k + 1) χT)
    (unitaryCompact ℂ (k + 1))) :=
    (kFiniteEval (principalSeries ℂ (k + 1) χT) 1).smulRight φ' with hfdef
  obtain ⟨A, hA⟩ := GKModuleDensity.exists_freeAlgebra_eq (hyp_principalSeries hirr) s f
  have hAS : ∀ v ∈ S, FreeAlgebra.lift ℂ (GKModuleDensity.gens (principalSeriesRep ℂ (k + 1) χT)
      (principalSeriesLie ℂ (k + 1) χT)) A v = f v := by
    intro v hv
    rw [← hs] at hv
    exact LinearMap.eqOn_span (fun w hw => hA w hw) hv
  obtain ⟨u', hu'⟩ := exists_sliceV_eq hχ hT hU hUK hUD A u0
  -- the identity for unitary `κ₁`
  have hunit : ∀ κ₁ ∈ unitaryCompact ℂ a, ∀ g₂ : Langlands.GeneralLinear (k + 1) ℂ,
      (u' : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (blockDiagGL κ₁ g₂) =
        u (blockDiagGL κ₁ 1) * φ g₂ := by
    intro κ₁ hκ₁ g₂
    have h1 := congrArg (fun v : kFiniteFunctions (principalSeries ℂ (k + 1) χT)
      (unitaryCompact ℂ (k + 1)) => (v : Langlands.GeneralLinear (k + 1) ℂ → ℂ) g₂)
      ((hu' κ₁).trans (hAS _ (hslice κ₁ hκ₁)))
    simp only [sliceV_coe, sliceFun_apply, hfdef, LinearMap.smulRight_apply, kFiniteEval_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ'] at h1
    exact h1
  refine ⟨u', u'.2, fun g₁ g₂ => ?_⟩
  -- extension from unitary `κ₁` to all of `GL_a(ℂ)`
  have hv : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
      (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g₂)
        (u' : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) ∈
        principalSeries ℂ (a + (k + 1)) (dualChar χ) :=
    rightTranslation_mem_principalSeries _ (hU u'.2).1 _
  have hw : φ g₂ • u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ) :=
    Submodule.smul_mem _ _ (hU hu).1
  have key := blockDiag_eq_of_eqOn_unitary hχ hv hw (fun κ₁ hκ₁ => by
    change (u' : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
      (blockDiagGL κ₁ 1 * blockDiagGL 1 g₂) = _
    rw [← blockDiagGL_mul, mul_one, one_mul, hunit κ₁ hκ₁ g₂, Pi.smul_apply, smul_eq_mul,
      mul_comm]) g₁
  change (u' : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (blockDiagGL g₁ 1 * blockDiagGL 1 g₂) = _ at key
  rw [← blockDiagGL_mul, mul_one, one_mul, Pi.smul_apply, smul_eq_mul] at key
  rw [key, mul_comm]

end Density

end ComplexBlockSlice

end Langlands.Archimedean
