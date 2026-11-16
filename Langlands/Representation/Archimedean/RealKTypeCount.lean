import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.RealRankOneStepFiltration

/-!
# Counting `O(n)`-types: injective `O(n)`-maps between function spaces are bijective

Let `V` and `W` be subspaces of principal series of `GL_n(ℝ)`. This file proves that if there
is an injective linear map from the `O(n)`-finite functions of `W` to those of `V` commuting
with right translation by `O(n)`, then every injective such map from those of `V` to those of
`W` is surjective (`RealKTypeCount.surjective_of_injective`).

The proof filters functions on `O(n)` by degree: `RealKTypeCount.degreeLE n N` is the space of
polynomials of degree at most `N` in the matrix entries. It is finite-dimensional and invariant
under left and right translation, and every polynomial function on `O(n)` lies in one of them.
The layer `RealKTypeCount.layer V (degreeLE n N)` of the `O(n)`-finite functions of `V`
restricting into `degreeLE n N` is finite-dimensional, because a principal series function is
determined by its restriction to `O(n)`. An equivariant map preserves layers: `(T f)(κ)` is the
value at `1` of `T` of the right translate of `f` by `κ`, and on the finite-dimensional layer
this functional is a finite combination of point evaluations, so `T f` restricts to a finite
combination of left translates of the restriction of `f`. Every `O(n)`-finite function lies in
some layer (`OrthogonalFinitePolynomial`). Comparing dimensions of layers then gives the
result.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace RealKTypeCount

variable {n : ℕ}

/-! ## Restriction to `O(n)` -/

/-- The restriction of a function on `GL_n(ℝ)` to `O(n)`. -/
def restrictLinear (n : ℕ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  LinearMap.funLeft ℂ ℂ Unitary.toUnits

@[simp]
theorem restrictLinear_apply (f : Langlands.GeneralLinear n ℝ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : restrictLinear n f κ = f (Unitary.toUnits κ) :=
  rfl

/-! ## A filtration of the functions on `O(n)` -/

/-- The span of the constant `1` and the matrix entries, as functions on `O(n)`. -/
def linearSpan (n : ℕ) : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  1 ⊔ Submodule.span ℂ
    (Set.range fun ij : Fin n × Fin n => (OrthogonalFinitePolynomial.entry n ij : _ → ℂ))

/-- The functions on `O(n)` that are polynomials of degree at most `N` in the matrix entries:
the `N`-th power of `linearSpan n`. -/
def degreeLE (n N : ℕ) : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  linearSpan n ^ N

theorem one_le_linearSpan : (1 : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ)) ≤
    linearSpan n :=
  le_sup_left

theorem entry_mem_linearSpan (ij : Fin n × Fin n) :
    (OrthogonalFinitePolynomial.entry n ij : Matrix.unitaryGroup (Fin n) ℝ → ℂ) ∈
      linearSpan n :=
  le_sup_right (a := (1 : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ)))
    (Submodule.subset_span ⟨ij, rfl⟩)

theorem fg_linearSpan : (linearSpan n).FG := by
  refine Submodule.FG.sup ⟨{1}, by simp [Submodule.one_eq_span]⟩ ?_
  exact Submodule.fg_span (Set.finite_range _)

instance finiteDimensional_degreeLE (N : ℕ) : FiniteDimensional ℂ (degreeLE n N) :=
  Module.Finite.iff_fg.mpr (fg_linearSpan.pow N)

theorem degreeLE_mono {N M : ℕ} (h : N ≤ M) : degreeLE n N ≤ degreeLE n M :=
  pow_le_pow_right' one_le_linearSpan h

/-- Every polynomial function on `O(n)` lies in some `degreeLE n N`. -/
theorem exists_mem_degreeLE {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : φ ∈ OrthogonalFinitePolynomial.polynomialFunctions n) : ∃ N, φ ∈ degreeLE n N := by
  let S : Subalgebra ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
    { carrier := {ψ | ∃ N, ψ ∈ degreeLE n N}
      mul_mem' := by
        rintro a b ⟨N, ha⟩ ⟨M, hb⟩
        refine ⟨N + M, ?_⟩
        rw [degreeLE, pow_add]
        exact Submodule.mul_mem_mul ha hb
      add_mem' := by
        rintro a b ⟨N, ha⟩ ⟨M, hb⟩
        exact ⟨max N M, add_mem (degreeLE_mono (le_max_left N M) ha)
          (degreeLE_mono (le_max_right N M) hb)⟩
      algebraMap_mem' := by
        intro c
        refine ⟨0, ?_⟩
        rw [degreeLE, pow_zero, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ c (Submodule.one_le.mp le_rfl) }
  have hle : OrthogonalFinitePolynomial.polynomialFunctions n ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨ij, rfl⟩
    exact ⟨1, by rw [degreeLE, pow_one]; exact entry_mem_linearSpan ij⟩
  exact hle hφ

/-! ### Translation invariance -/

/-- Right translation by `k` on functions on `O(n)`, as an algebra homomorphism. -/
def rightAlgHom (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (Matrix.unitaryGroup (Fin n) ℝ → ℂ) →ₐ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  AlgHom.pi fun x => Pi.evalAlgHom ℂ (fun _ : Matrix.unitaryGroup (Fin n) ℝ => ℂ) (x * k)

theorem rightAlgHom_apply (k : Matrix.unitaryGroup (Fin n) ℝ)
    (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) : rightAlgHom k φ = fun x => φ (x * k) :=
  rfl

/-- Left translation by `k` on functions on `O(n)`, as an algebra homomorphism. -/
def leftAlgHom (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (Matrix.unitaryGroup (Fin n) ℝ → ℂ) →ₐ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  AlgHom.pi fun x => Pi.evalAlgHom ℂ (fun _ : Matrix.unitaryGroup (Fin n) ℝ => ℂ) (k * x)

theorem leftAlgHom_apply (k : Matrix.unitaryGroup (Fin n) ℝ)
    (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) : leftAlgHom k φ = fun x => φ (k * x) :=
  rfl

theorem map_rightAlgHom_linearSpan_le (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (linearSpan n).map (rightAlgHom k).toLinearMap ≤ linearSpan n := by
  rw [linearSpan, Submodule.map_sup, Submodule.map_span]
  refine sup_le ?_ ?_
  · rw [Submodule.map_one]
    exact le_sup_left
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
    have h : (rightAlgHom k).toLinearMap
        (OrthogonalFinitePolynomial.entry n ij : Matrix.unitaryGroup (Fin n) ℝ → ℂ) =
        ∑ l : Fin n, (((k : Matrix (Fin n) (Fin n) ℝ) l ij.2 : ℝ) : ℂ) •
          (OrthogonalFinitePolynomial.entry n (ij.1, l) : Matrix.unitaryGroup (Fin n) ℝ → ℂ) := by
      funext x
      simp only [AlgHom.toLinearMap_apply, rightAlgHom_apply,
        OrthogonalFinitePolynomial.entry_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Submonoid.coe_mul, Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [SetLike.mem_coe, h]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (entry_mem_linearSpan _)

theorem map_leftAlgHom_linearSpan_le (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (linearSpan n).map (leftAlgHom k).toLinearMap ≤ linearSpan n := by
  rw [linearSpan, Submodule.map_sup, Submodule.map_span]
  refine sup_le ?_ ?_
  · rw [Submodule.map_one]
    exact le_sup_left
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
    have h : (leftAlgHom k).toLinearMap
        (OrthogonalFinitePolynomial.entry n ij : Matrix.unitaryGroup (Fin n) ℝ → ℂ) =
        ∑ l : Fin n, (((k : Matrix (Fin n) (Fin n) ℝ) ij.1 l : ℝ) : ℂ) •
          (OrthogonalFinitePolynomial.entry n (l, ij.2) : Matrix.unitaryGroup (Fin n) ℝ → ℂ) := by
      funext x
      simp only [AlgHom.toLinearMap_apply, leftAlgHom_apply,
        OrthogonalFinitePolynomial.entry_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Submonoid.coe_mul, Matrix.mul_apply]
      push_cast
      rfl
    rw [SetLike.mem_coe, h]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (entry_mem_linearSpan _)

theorem right_mem_degreeLE {N : ℕ} {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : φ ∈ degreeLE n N) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (fun x => φ (x * k)) ∈ degreeLE n N := by
  have h : (degreeLE n N).map (rightAlgHom k).toLinearMap ≤ degreeLE n N := by
    rw [degreeLE, Submodule.map_pow]
    exact pow_le_pow_left' (map_rightAlgHom_linearSpan_le k) N
  exact h ⟨φ, hφ, rightAlgHom_apply k φ⟩

theorem left_mem_degreeLE {N : ℕ} {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : φ ∈ degreeLE n N) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (fun x => φ (k * x)) ∈ degreeLE n N := by
  have h : (degreeLE n N).map (leftAlgHom k).toLinearMap ≤ degreeLE n N := by
    rw [degreeLE, Submodule.map_pow]
    exact pow_le_pow_left' (map_leftAlgHom_linearSpan_le k) N
  exact h ⟨φ, hφ, leftAlgHom_apply k φ⟩

end RealKTypeCount

/-! ## Maps commuting with right translation by `O(n)` -/

/-- A linear map `T` from the `O(n)`-finite functions of `V` to those of `W` commutes with
right translation by `O(n)`: for every `k ∈ O(n)` and every `f`, the right translates by `k` of
`f` and of `T f` are again in the respective spaces, and `T` carries the first to the second. -/
def IsRealKEquivariant {n : ℕ} (V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (T : kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] kFiniteFunctions W (unitaryCompact ℝ n)) :
    Prop :=
  ∀ (k : unitaryCompact ℝ n) (f : kFiniteFunctions V (unitaryCompact ℝ n)),
    ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions V (unitaryCompact ℝ n),
      ∃ hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (T f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            kFiniteFunctions W (unitaryCompact ℝ n),
        T ⟨_, hf⟩ = ⟨_, hg⟩

/-- An intertwiner modulo `⊥` commutes with right translation by `O(n)`. -/
theorem IsRealIntertwinerModulo.isRealKEquivariant {n : ℕ} {ds es : List RealBlock}
    {q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (hq : IsRealIntertwinerModulo n ds es ⊥ q) :
    IsRealKEquivariant (realStandardModule n ds) (realStandardModule n es) q := by
  intro k f
  obtain ⟨hf, hg, h⟩ := hq.1 k f
  exact ⟨hf, hg, sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h)⟩

namespace RealKTypeCount

variable {n : ℕ}

/-! ## Layers of the `O(n)`-finite functions -/

/-- The `O(n)`-finite functions of `V` whose restriction to `O(n)` lies in `U`. -/
def layer (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (U : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ)) :
    Submodule ℂ (kFiniteFunctions V (unitaryCompact ℝ n)) :=
  U.comap (restrictLinear n ∘ₗ (kFiniteFunctions V (unitaryCompact ℝ n)).subtype)

theorem mem_layer_iff (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (U : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ))
    (f : kFiniteFunctions V (unitaryCompact ℝ n)) :
    f ∈ layer V U ↔ restrictLinear n (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ U :=
  Iff.rfl

theorem toUnits_mk {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ : Matrix.unitaryGroup (Fin n) ℝ) = k :=
  Units.ext rfl

/-- Restriction to `O(n)` is injective on the `O(n)`-finite functions of a subspace of a
principal series. -/
theorem restrict_injective {χ : ℕ → ℝˣ → ℂ} {V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hV : V ≤ principalSeries ℝ n χ) :
    Function.Injective
      (restrictLinear n ∘ₗ (kFiniteFunctions V (unitaryCompact ℝ n)).subtype) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => Subtype.ext ?_
  refine eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hV f.2.1) fun k hk => ?_
  have h := congrFun hf ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, restrictLinear_apply,
    toUnits_mk hk] at h
  exact h

/-- Over a subspace of a principal series, the layer of a finite-dimensional space of functions
on `O(n)` is finite-dimensional. -/
theorem finiteDimensional_layer {χ : ℕ → ℝˣ → ℂ}
    {V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} (hV : V ≤ principalSeries ℝ n χ)
    (U : Submodule ℂ (Matrix.unitaryGroup (Fin n) ℝ → ℂ)) [FiniteDimensional ℂ U] :
    FiniteDimensional ℂ (layer V U) := by
  let r : layer V U →ₗ[ℂ] U :=
    (restrictLinear n ∘ₗ (kFiniteFunctions V (unitaryCompact ℝ n)).subtype).restrict
      fun x hx => hx
  refine Module.Finite.of_injective r fun x y hxy => Subtype.ext (restrict_injective hV ?_)
  exact congrArg Subtype.val hxy

/-- A map commuting with right translation by `O(n)`, out of the `O(n)`-finite functions of a
subspace of a principal series, preserves the degree layers. -/
theorem mem_layer_degreeLE_of_isRealKEquivariant {χ : ℕ → ℝˣ → ℂ}
    {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} (hV : V ≤ principalSeries ℝ n χ)
    {T : kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] kFiniteFunctions W (unitaryCompact ℝ n)}
    (hT : IsRealKEquivariant V W T) {N : ℕ} {f : kFiniteFunctions V (unitaryCompact ℝ n)}
    (hf : f ∈ layer V (degreeLE n N)) : T f ∈ layer W (degreeLE n N) := by
  let e : Matrix.unitaryGroup (Fin n) ℝ →
      kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] ℂ := fun κ =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℝ => ℂ)
      (Unitary.toUnits κ)).comp (kFiniteFunctions V (unitaryCompact ℝ n)).subtype
  let ℓ : kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℝ => ℂ) 1).comp
      ((kFiniteFunctions W (unitaryCompact ℝ n)).subtype.comp T)
  have := finiteDimensional_layer hV (degreeLE n N)
  have hsep : ∀ s ∈ layer V (degreeLE n N), (∀ κ, e κ s = 0) → s = 0 := by
    intro s _ hs
    refine restrict_injective hV ?_
    rw [map_zero]
    funext κ
    exact hs κ
  obtain ⟨m, p, c, hsum⟩ := exists_sum_of_separating e (layer V (degreeLE n N)) hsep ℓ
  have key : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ,
      (T f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ) =
        ∑ i, c i * (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (p i * κ)) := by
    intro κ
    obtain ⟨hf', hg', hT'⟩ := hT ⟨Unitary.toUnits κ, κ.2⟩ f
    have hmem : (⟨_, hf'⟩ : kFiniteFunctions V (unitaryCompact ℝ n)) ∈
        layer V (degreeLE n N) := by
      rw [mem_layer_iff]
      have h := right_mem_degreeLE hf κ
      convert h using 1
      funext x
      simp only [restrictLinear_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      show (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits x * Unitary.toUnits κ) = _
      rw [← map_mul]
    have h1 := hsum _ hmem
    have h2 : ℓ ⟨_, hf'⟩ = (T f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ) := by
      show ((T ⟨_, hf'⟩ : kFiniteFunctions W (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) 1 = _
      rw [hT']
      show (T f : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits κ) = _
      rw [one_mul]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i * (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (p i) * Unitary.toUnits κ) = _
    rw [← map_mul]
  rw [mem_layer_iff]
  have hres : restrictLinear n (T f : Langlands.GeneralLinear n ℝ → ℂ) =
      ∑ i, c i • fun x => restrictLinear n (f : Langlands.GeneralLinear n ℝ → ℂ) (p i * x) := by
    funext κ
    rw [restrictLinear_apply, key, Finset.sum_apply]
    rfl
  rw [hres]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (left_mem_degreeLE hf (p i))

/-- Every `O(n)`-finite function of a subspace of a principal series lies in some degree
layer. -/
theorem exists_mem_layer_degreeLE {χ : ℕ → ℝˣ → ℂ}
    {V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} (hV : V ≤ principalSeries ℝ n χ)
    (f : kFiniteFunctions V (unitaryCompact ℝ n)) : ∃ N, f ∈ layer V (degreeLE n N) := by
  have hc : Continuous (f : Langlands.GeneralLinear n ℝ → ℂ) := (hV f.2.1).1.continuous
  have hfK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ))) := f.2.2
  have hle : OrthogonalFinitePolynomial.translateSpan
      (restrictLinear n (f : Langlands.GeneralLinear n ℝ → ℂ)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ))).map
        (restrictLinear n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    funext x
    show (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits x * Unitary.toUnits k) =
      (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (x * k))
    rw [map_mul]
  have : FiniteDimensional ℂ (OrthogonalFinitePolynomial.translateSpan
      (restrictLinear n (f : Langlands.GeneralLinear n ℝ → ℂ))) :=
    Submodule.finiteDimensional_of_le hle
  exact exists_mem_degreeLE (φ := restrictLinear n (f : Langlands.GeneralLinear n ℝ → ℂ))
    (OrthogonalFinitePolynomial.mem_polynomialFunctions_of_finiteDimensional
      (hc.comp continuous_unitary_toUnits))

/-- **Counting `O(n)`-types.** Let `V` and `W` be subspaces of principal series of `GL_n(ℝ)`.
If there is an injective linear map from the `O(n)`-finite functions of `W` to those of `V`
commuting with right translation by `O(n)`, then every injective such map in the opposite
direction is surjective. -/
theorem surjective_of_injective {χ χ' : ℕ → ℝˣ → ℂ}
    {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} (hV : V ≤ principalSeries ℝ n χ)
    (hW : W ≤ principalSeries ℝ n χ')
    {T : kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] kFiniteFunctions W (unitaryCompact ℝ n)}
    (hT : IsRealKEquivariant V W T) (hTi : Function.Injective T)
    {A : kFiniteFunctions W (unitaryCompact ℝ n) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)}
    (hA : IsRealKEquivariant W V A) (hAi : Function.Injective A) : Function.Surjective T := by
  intro g
  obtain ⟨N, hg⟩ := exists_mem_layer_degreeLE hW g
  have := finiteDimensional_layer hV (degreeLE n N)
  have := finiteDimensional_layer hW (degreeLE n N)
  let T' : layer V (degreeLE n N) →ₗ[ℂ] layer W (degreeLE n N) :=
    T.restrict fun f hf => mem_layer_degreeLE_of_isRealKEquivariant hV hT hf
  let A' : layer W (degreeLE n N) →ₗ[ℂ] layer V (degreeLE n N) :=
    A.restrict fun f hf => mem_layer_degreeLE_of_isRealKEquivariant hW hA hf
  have hT' : Function.Injective T' := fun x y hxy =>
    Subtype.ext (hTi (congrArg Subtype.val hxy))
  have hA' : Function.Injective A' := fun x y hxy =>
    Subtype.ext (hAi (congrArg Subtype.val hxy))
  have hrank : Module.finrank ℂ (layer V (degreeLE n N)) =
      Module.finrank ℂ (layer W (degreeLE n N)) :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hT')
      (LinearMap.finrank_le_finrank_of_injective hA')
  have hs : Function.Surjective T' := by
    rw [← LinearMap.range_eq_top]
    exact @Submodule.eq_top_of_finrank_eq ℂ (layer W (degreeLE n N)) _ _ _ this T'.range
      (by rw [LinearMap.finrank_range_of_inj hT', hrank])
  obtain ⟨⟨f, hf⟩, hfg⟩ := hs ⟨g, hg⟩
  exact ⟨f, congrArg Subtype.val hfg⟩

end RealKTypeCount

end Langlands.Archimedean
