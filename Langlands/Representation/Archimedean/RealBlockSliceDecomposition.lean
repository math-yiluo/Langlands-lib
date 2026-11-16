import Langlands.Representation.Archimedean.RealBlockDual

/-!
# Slices of principal-series functions along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`

For an `O(a+k+1)`-finite function `y` of the principal series of `χ⁻¹` on `GL_{a+k+1}(ℝ)`, the
slices `g₂ ↦ y(diag(h, g₂))` (`h ∈ GL_a(ℝ)`) all lie in one finite-dimensional space
`sliceSpace y` of `O(k+1)`-finite functions of the principal series of the tied block
(`sliceFun_mem_sliceSpace`). Interpolating in that space at points of `O(k+1)` gives a finite
separation of variables

`y(diag(h, g₂)) = ∑ᵢ ỹᵢ(diag(h, 1)) bᵢ(g₂)`

with `ỹᵢ = R(diag(1, pᵢ)) y` again `O(a+k+1)`-finite in the principal series of `χ⁻¹`
(`exists_blockDiag_decomposition`). If the principal series of the tied block is irreducible,
the density theorem produces, inside any `(𝔤, K)`-stable space containing `x`, a function `x'`
with `x'(diag(h, g₂)) = x(diag(h, 1)) φ(g₂)` for a prescribed `φ` (`exists_mem_blockDiag_eq`;
this is the density step of `RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`, for all
`h ∈ GL_a(ℝ)` instead of `h ∈ O(a)`).
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealBlockSliceDecomposition

open RealBlockParabolic RealBlockChart RealBlockLimit RealBlockJacquet RealBlockDual PartialJacquet
  JacquetLimit GramFormula PrincipalSeriesExtension RealPrincipalSeriesDuality
  Langlands.GeneralLinear

/-! ## Interpolation at points of a separating set -/

/-- A finite-dimensional space `S` of functions on `X`, whose elements vanishing on `P ⊆ X` are
zero, has an interpolation family: points `p i ∈ P` and functions `u i ∈ S` with
`s = ∑ s(p i) • u i` for every `s ∈ S`. -/
theorem exists_interpolation_of_separating {X : Type*} (P : Set X) (S : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ S] (hsep : ∀ s ∈ S, (∀ x ∈ P, s x = 0) → s = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → X) (u : ι → X → ℂ), (∀ i, p i ∈ P) ∧
      (∀ i, u i ∈ S) ∧ ∀ s ∈ S, s = ∑ i, s (p i) • u i := by
  classical
  let b := Module.finBasis ℂ S
  have hsep' : ∀ s ∈ S, (∀ x : P, (LinearMap.proj (x : X) : (X → ℂ) →ₗ[ℂ] ℂ) s = 0) →
      s = 0 :=
    fun s hs h => hsep s hs fun x hx => h ⟨x, hx⟩
  have hcoord : ∀ j, ∃ (m : ℕ) (p : Fin m → P) (c : Fin m → ℂ), ∀ s (hs : s ∈ S),
      b.coord j ⟨s, hs⟩ = ∑ i, c i * s (p i) := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (b.coord j)
    obtain ⟨m, p, c, h⟩ := exists_sum_of_separating
      (fun x : P => (LinearMap.proj (x : X) : (X → ℂ) →ₗ[ℂ] ℂ)) S hsep' ℓ
    refine ⟨m, p, c, fun s hs => ?_⟩
    rw [← hℓ, LinearMap.comp_apply, Submodule.subtype_apply]
    exact h s hs
  choose m p c hc using hcoord
  refine ⟨Σ j, Fin (m j), inferInstance, fun q => (p q.1 q.2 : X),
    fun q => c q.1 q.2 • (b q.1 : X → ℂ), fun q => (p q.1 q.2).2,
    fun q => S.smul_mem _ (b q.1).2, fun s hs => ?_⟩
  calc s = ((⟨s, hs⟩ : S) : X → ℂ) := rfl
    _ = ∑ j, b.repr ⟨s, hs⟩ j • (b j : X → ℂ) := by
        conv_lhs => rw [← b.sum_repr ⟨s, hs⟩]
        rw [Submodule.coe_sum]
        rfl
    _ = ∑ j, ∑ i, s (p j i) • (c j i • (b j : X → ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← b.coord_apply, hc j s hs, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
    _ = _ := (Fintype.sum_sigma (fun q : Σ j, Fin (m j) =>
          s (p q.1 q.2) • (c q.1 q.2 • (b q.1 : X → ℂ)))).symm

/-! ## The slice space -/

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- The span of the right `O(a+k+1)`-translates of `y`. -/
def transSpan (y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) :
    Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun κ : unitaryCompact ℝ (a + (k + 1)) =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ)
      (κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) y)

/-- The space `{g₂ ↦ v(diag(1, g₂)) | v ∈ transSpan y}` containing all slices of `y`. -/
def sliceSpace (y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) :
    Submodule ℂ (Langlands.GeneralLinear (k + 1) ℝ → ℂ) :=
  (transSpan y).map (sliceFun (1 : Langlands.GeneralLinear a ℝ))

theorem finiteDimensional_transSpan {ψ : ℕ → ℝˣ → ℂ}
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) ψ)
      (unitaryCompact ℝ (a + (k + 1)))) :
    FiniteDimensional ℂ (transSpan y) :=
  (mem_kFiniteVectors_iff _ _ _).mp hy.2

theorem finiteDimensional_sliceSpace {ψ : ℕ → ℝˣ → ℂ}
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) ψ)
      (unitaryCompact ℝ (a + (k + 1)))) :
    FiniteDimensional ℂ (sliceSpace (a := a) (k := k) y) := by
  have := finiteDimensional_transSpan hy
  unfold sliceSpace
  infer_instance

theorem transSpan_le {ψ : ℕ → ℝˣ → ℂ} {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) ψ)
      (unitaryCompact ℝ (a + (k + 1)))) :
    transSpan y ≤ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) ψ)
      (unitaryCompact ℝ (a + (k + 1))) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨κ, rfl⟩
  exact rightTranslation_mem_kFiniteFunctions_principalSeries (hf := hy) (hk := κ.2)

theorem sliceSpace_le (hχ : IsSignedPower χ e) {χT : ℕ → ℝˣ → ℂ}
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℝˣ, χT l z = blockDualChar a χ l z)
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℝ (a + (k + 1)))) :
    sliceSpace (a := a) (k := k) y ≤
      kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1)) := by
  rintro _ ⟨v, hv, rfl⟩
  exact sliceFun_mem hχ hT (transSpan_le hy hv) 1

/-- **All slices lie in the slice space.** For `h = z u κ` (Iwasawa), the slice at `h` is a
multiple of the slice at `κ`, which is the slice at `1` of `R(diag(κ, 1)) y`. -/
theorem sliceFun_mem_sliceSpace {ψ : ℕ → ℝˣ → ℂ}
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ principalSeries ℝ (a + (k + 1)) ψ) (h : Langlands.GeneralLinear a ℝ) :
    sliceFun h y ∈ sliceSpace (a := a) (k := k) y := by
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact h
  have hsl : sliceFun ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℝ) *
      (u : Langlands.GeneralLinear a ℝ) * κ) y =
      principalSeriesCharacter ℝ (a + (k + 1)) ψ (Fin.addCases z (fun _ => 1)) •
        sliceFun κ y := by
    funext g₂
    rw [sliceFun_apply, Pi.smul_apply, sliceFun_apply, smul_eq_mul]
    have hsplit : blockDiagGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℝ) *
        (u : Langlands.GeneralLinear a ℝ) * κ) g₂ =
        (Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) :
          Langlands.GeneralLinear (a + (k + 1)) ℝ) *
        ((⟨blockDiagGL (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear (k + 1) ℝ),
          blockDiagGL_mem_upperUnipotent u⟩ : upperUnipotent (a + (k + 1)) ℝ) :
            Langlands.GeneralLinear (a + (k + 1)) ℝ) * blockDiagGL κ g₂ := by
      rw [← blockDiagGL_diagonalUnits]
      change _ = blockDiagGL (Iwasawa.diagonalUnits z) 1 *
        blockDiagGL (u : Langlands.GeneralLinear a ℝ) 1 * blockDiagGL κ g₂
      rw [← blockDiagGL_mul, ← blockDiagGL_mul, one_mul, one_mul]
    rw [hsplit, hy.2]
  rw [hsl, sliceFun_eq_sliceFun_one]
  exact Submodule.smul_mem _ _ ⟨_, Submodule.subset_span ⟨⟨blockDiagGL κ 1,
    blockDiagGL_mem_unitaryCompact hκ (unitaryCompact ℝ (k + 1)).one_mem⟩, rfl⟩, rfl⟩

/-! ## Separation of variables -/

/-- **Finite separation of variables.** An `O(a+k+1)`-finite function `y` of the principal
series of `χ⁻¹` satisfies `y(diag(h, g₂)) = ∑ᵢ ỹᵢ(diag(h, 1)) bᵢ(g₂)` with finitely many
`O(a+k+1)`-finite `ỹᵢ` of the principal series of `χ⁻¹` and `O(k+1)`-finite `bᵢ` of the principal
series of the tied block. -/
theorem exists_blockDiag_decomposition (hχ : IsSignedPower χ e) {χT : ℕ → ℝˣ → ℂ}
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℝˣ, χT l z = blockDualChar a χ l z)
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℝ (a + (k + 1)))) :
    ∃ (ι : Type) (_ : Fintype ι) (yt : ι → Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
      (b : ι → Langlands.GeneralLinear (k + 1) ℝ → ℂ),
      (∀ i, yt i ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) (dualChar χ))
        (unitaryCompact ℝ (a + (k + 1)))) ∧
      (∀ i, b i ∈ kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1))) ∧
      ∀ (h : Langlands.GeneralLinear a ℝ) (g₂ : Langlands.GeneralLinear (k + 1) ℝ),
        y (blockDiagGL h g₂) = ∑ i, restrictBlock (k := k) (yt i) h * b i g₂ := by
  have := finiteDimensional_sliceSpace (a := a) (k := k) hy
  have hsep : ∀ s ∈ sliceSpace (a := a) (k := k) y,
      (∀ x ∈ (unitaryCompact ℝ (k + 1) : Set (Langlands.GeneralLinear (k + 1) ℝ)), s x = 0) →
        s = 0 :=
    fun s hs h0 => eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact
      (sliceSpace_le hχ hT hy hs).1 h0
  obtain ⟨ι, _, p, u, hp, hu, hs⟩ := exists_interpolation_of_separating
    (unitaryCompact ℝ (k + 1) : Set (Langlands.GeneralLinear (k + 1) ℝ)) _ hsep
  refine ⟨ι, inferInstance, fun i => Whittaker.rightTranslation ℂ
    (Langlands.GeneralLinear (a + (k + 1)) ℝ)
      (blockDiagGL (1 : Langlands.GeneralLinear a ℝ) (p i)) y,
    u, fun i => rightTranslation_mem_kFiniteFunctions_principalSeries (hf := hy)
      (hk := blockDiagGL_mem_unitaryCompact (unitaryCompact ℝ a).one_mem (hp i)),
    fun i => sliceSpace_le hχ hT hy (hu i), fun h g₂ => ?_⟩
  have h1 := congrFun (hs _ (sliceFun_mem_sliceSpace hy.1 h)) g₂
  rw [Finset.sum_apply] at h1
  simp only [sliceFun_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change y (blockDiagGL h (p i)) = y (blockDiagGL h 1 * blockDiagGL 1 (p i))
  rw [← blockDiagGL_mul, mul_one, one_mul]

/-! ## Density on the tied block -/

/-- **Density along the tied block.** Let `X` be a `(𝔤, K)`-stable space of `O(a+k+1)`-finite
functions of the principal series of `χ⁻¹`, and assume the principal series of the tied block is
irreducible. For `x ∈ X` and every `O(k+1)`-finite `φ` of the principal series of the tied block,
some `x' ∈ X` satisfies `x'(diag(h, g₂)) = x(diag(h, 1)) φ(g₂)` for all `h`, `g₂`. -/
theorem exists_mem_blockDiag_eq (hχ : IsSignedPower χ e) {χT : ℕ → ℝˣ → ℂ}
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℝˣ, χT l z = blockDualChar a χ l z)
    (hirr : IsIrreducibleGKModule (principalSeriesRep ℝ (k + 1) χT)
      (principalSeriesLie ℝ (k + 1) χT))
    {X : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)}
    (hX : X ≤ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℝ (a + (k + 1))))
    (hXK : ∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ∀ x ∈ X,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ) κ x ∈ X)
    (hXD : ∀ (Y : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℝ), ∀ x ∈ X,
      rightDerivative (matrixModel ℝ (a + (k + 1))) Y x ∈ X)
    {x : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ} (hx : x ∈ X)
    (φ : kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1))) :
    ∃ x' ∈ X, ∀ (h : Langlands.GeneralLinear a ℝ) (g₂ : Langlands.GeneralLinear (k + 1) ℝ),
      x' (blockDiagGL h g₂) =
        x (blockDiagGL h 1) * (φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ) g₂ := by
  set x0 : X := ⟨x, hx⟩ with hx0
  set W : Submodule ℂ (Langlands.GeneralLinear (k + 1) ℝ → ℂ) := sliceSpace (a := a) (k := k) x
    with hWdef
  have hWfin : FiniteDimensional ℂ W := finiteDimensional_sliceSpace (hX hx)
  set S : Submodule ℂ (kFiniteFunctions (principalSeries ℝ (k + 1) χT)
    (unitaryCompact ℝ (k + 1))) :=
    W.comap (kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1))).subtype
    with hSdef
  have hSfin : FiniteDimensional ℂ S := by
    refine Module.Finite.of_injective (LinearMap.codRestrict W
      ((kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1))).subtype ∘ₗ
        S.subtype) fun x => x.2) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W =>
      (z : Langlands.GeneralLinear (k + 1) ℝ → ℂ)) hxy))
  have hslice : ∀ h : Langlands.GeneralLinear a ℝ, sliceV hχ hT hX h x0 ∈ S := by
    intro h
    change sliceFun h x ∈ W
    exact sliceFun_mem_sliceSpace (hX hx).1 h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).mpr hSfin
  set f : Module.End ℂ
      (kFiniteFunctions (principalSeries ℝ (k + 1) χT) (unitaryCompact ℝ (k + 1))) :=
    (kFiniteEval (principalSeries ℝ (k + 1) χT) 1).smulRight φ with hfdef
  obtain ⟨A, hA⟩ := GKModuleDensity.exists_freeAlgebra_eq (hyp_principalSeries hirr) s f
  have hAS : ∀ v ∈ S, FreeAlgebra.lift ℂ (GKModuleDensity.gens (principalSeriesRep ℝ (k + 1) χT)
      (principalSeriesLie ℝ (k + 1) χT)) A v = f v := by
    intro v hv
    rw [← hs] at hv
    exact LinearMap.eqOn_span (fun w hw => hA w hw) hv
  obtain ⟨x', hx'⟩ := exists_sliceV_eq hχ hT hX hXK hXD A x0
  refine ⟨x', x'.2, fun h g₂ => ?_⟩
  have h1 := congrArg (fun v : kFiniteFunctions (principalSeries ℝ (k + 1) χT)
    (unitaryCompact ℝ (k + 1)) => (v : Langlands.GeneralLinear (k + 1) ℝ → ℂ) g₂)
    ((hx' h).trans (hAS _ (hslice h)))
  simp only [sliceV_coe, sliceFun_apply, hfdef, LinearMap.smulRight_apply, kFiniteEval_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
  exact h1

end RealBlockSliceDecomposition

end Langlands.Archimedean
