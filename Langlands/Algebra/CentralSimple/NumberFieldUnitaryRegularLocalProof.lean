import Langlands.FieldTheory.ClosureTransport
import Langlands.Algebra.CentralSimple.NumberFieldUnitaryRegularLocalStatement
import Langlands.Algebra.CentralSimple.UnitaryRegularNonsplit
import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting
import Langlands.Algebra.LocalUnitaryDivisionCommutativeProof
import Langlands.Global.FiniteCompletionLocalField

/-! # Proof: regular local unitary elements of prescribed relative reduced norm -/

noncomputable section

universe u

open scoped TensorProduct
open Polynomial NumberField

namespace Langlands.CentralSimple

open Langlands.GroupScheme Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
  UnitaryPoints

/-- For a quadratic extension `E/F` and a field `K` over `F`, either `E` embeds in `K` over `F`
or `E ⊗[F] K` is a field. -/
theorem nonempty_algHom_or_isField_tensor {F E : Type u} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (K : Type u) [Field K] [Algebra F K] :
    Nonempty (E →ₐ[F] K) ∨ IsField (E ⊗[F] K) := by
  classical
  have : FiniteDimensional F E := .of_finrank_pos (by rw [h2]; decide)
  have hT : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, h2]
  have : Nontrivial (K ⊗[F] E) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [hT]; decide)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] E)
  let : Field (K ⊗[F] E ⧸ m) := Ideal.Quotient.field m
  let π : K ⊗[F] E →ₐ[K] K ⊗[F] E ⧸ m := Ideal.Quotient.mkₐ K m
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective K m
  have : FiniteDimensional K (K ⊗[F] E ⧸ m) := Module.Finite.of_surjective π.toLinearMap hπ
  have hle : Module.finrank K (K ⊗[F] E ⧸ m) ≤ 2 :=
    hT ▸ LinearMap.finrank_le_finrank_of_surjective (f := π.toLinearMap) hπ
  have hpos : 0 < Module.finrank K (K ⊗[F] E ⧸ m) := Module.finrank_pos
  interval_cases h : Module.finrank K (K ⊗[F] E ⧸ m)
  · left
    have hinj : Function.Injective (Algebra.ofId K (K ⊗[F] E ⧸ m)) :=
      (Algebra.ofId K (K ⊗[F] E ⧸ m)).toRingHom.injective
    have hsurj : Function.Surjective (Algebra.ofId K (K ⊗[F] E ⧸ m)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_self, h])
        (f := (Algebra.ofId K (K ⊗[F] E ⧸ m)).toLinearMap)).mp hinj
    let e : K ≃ₐ[K] K ⊗[F] E ⧸ m := AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩
    exact ⟨((e.symm : K ⊗[F] E ⧸ m →ₐ[K] K).restrictScalars F).comp
      ((π.restrictScalars F).comp Algebra.TensorProduct.includeRight)⟩
  · right
    have hinj : Function.Injective π :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hT, h])
        (f := π.toLinearMap)).mpr hπ
    let e : K ⊗[F] E ≃ₐ[K] K ⊗[F] E ⧸ m := AlgEquiv.ofBijective π ⟨hinj, hπ⟩
    have hKE : IsField (K ⊗[F] E) := MulEquiv.isField (Field.toIsField _) e.toMulEquiv
    exact MulEquiv.isField hKE (Algebra.TensorProduct.comm F E K).toMulEquiv

/-- Every quadratic extension of the completion of a number field at an infinite place is
isomorphic to `ℂ`, hence algebraically closed. -/
theorem isAlgClosed_of_finrank_eq_two {F : Type u} [Field F] [NumberField F]
    (w : InfinitePlace F) (L : Type u) [Field L] [Algebra w.Completion L]
    (h2 : Module.finrank w.Completion L = 2) : IsAlgClosed L := by
  have : FiniteDimensional w.Completion L := .of_finrank_pos (by rw [h2]; decide)
  let j := InfinitePlace.Completion.extensionEmbedding w
  let : Algebra w.Completion ℂ := j.toAlgebra
  let g : L →ₐ[w.Completion] ℂ := IsAlgClosed.lift
  have hgj (k : w.Completion) : g (algebraMap w.Completion L k) = j k := g.commutes k
  have hreal (r : ℝ) : ∃ k : w.Completion, j k = r := by
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨k, hk⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw r
      exact ⟨k, by rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hk]⟩
    · exact InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw r
  have hginj : Function.Injective g := g.toRingHom.injective
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : L, ℓ ∉ Set.range (algebraMap w.Completion L) := by
    by_contra! h
    have := LinearMap.finrank_le_finrank_of_surjective
      (f := Algebra.linearMap w.Completion L) (fun ℓ => h ℓ)
    rw [Module.finrank_self, h2] at this
    omega
  have him : (g ℓ).im ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := hreal (g ℓ).re
    apply hℓ
    refine ⟨k, hginj ?_⟩
    rw [hgj, hk]
    exact Complex.ext rfl (by simp [h])
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, ha⟩ := hreal (g ℓ).re
    obtain ⟨b, hb⟩ := hreal (g ℓ).im
    obtain ⟨c, hc⟩ := hreal y.re
    obtain ⟨d, hd⟩ := hreal y.im
    have hI : (g ℓ - ((g ℓ).re : ℂ)) / ((g ℓ).im : ℂ) = Complex.I := by
      rw [div_eq_iff (by exact_mod_cast him)]
      apply Complex.ext <;> simp
    have hb0 : algebraMap w.Completion L b ≠ 0 := by
      intro h0
      apply him
      have h1 : ((g ℓ).im : ℂ) = 0 := by rw [← hb, ← hgj, h0, map_zero]
      exact_mod_cast h1
    refine ⟨algebraMap w.Completion L c +
      algebraMap w.Completion L d * ((ℓ - algebraMap w.Completion L a) /
        algebraMap w.Completion L b), ?_⟩
    rw [map_add, map_mul, map_div₀, map_sub, hgj, hgj, hgj, hgj, hc, hd, ha, hb, hI]
    exact Complex.re_add_im y
  exact Langlands.FieldTheory.isAlgClosed_of_ringEquiv _ (RingEquiv.ofBijective g ⟨hginj, hsurj⟩).symm

/-- Central simple algebras with unitary involutions over quadratic extensions of the
completion at an infinite place are split. -/
theorem unitaryInvolutionSplitting_infinitePlace {F : Type u} [Field F] [NumberField F]
    (w : InfinitePlace F) : UnitaryInvolutionSplitting w.Completion := by
  intro L _ _ _ _ σ _ A _ _ _ _ _ τ _
  have : IsAlgClosed L :=
    isAlgClosed_of_finrank_eq_two w L (Algebra.IsQuadraticExtension.finrank_eq_two _ L)
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed L A
  exact ⟨n, ⟨e⟩⟩

/-- **Regular local unitary elements of prescribed relative reduced norm.** At every place
`v` of a number field `F`, a unitary point of `F_v ⊗[F] B` with relative reduced norm `z ⊗ 1`
can be replaced by a unitary `x` which is regular, with a conjugate-reciprocal polynomial `f`
of degree `n` over `F_v ⊗[F] E` satisfying `f(x) = 0` and `f'(x)` invertible. -/
theorem numberFieldUnitaryRegularLocal : NumberFieldUnitaryRegularLocalStatement.{u} := by
  intro F E B _ _ _ _ _ _ _ _ _ _ _ _ _ τ hτ n hn z v hx
  obtain ⟨x₀, hx₀, hz⟩ := hx
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  rcases v with w | v
  · let : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := by
          refine ⟨2, ?_⟩
          have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (2 : w.Completion)
          rw [← h]
          norm_num only [map_ofNat, Complex.norm_ofNat] }
    have : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
    rcases nonempty_algHom_or_isField_tensor (E := E) h2 w.Completion with hφ | hfield
    · obtain ⟨φ⟩ := hφ
      let : Algebra E w.Completion := φ.toRingHom.toAlgebra
      have : IsScalarTower F E w.Completion :=
        IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
      exact exists_regular_unitary_of_split τ hτ w.Completion n hn z x₀ hx₀ hz
    · exact exists_regular_unitary_of_isField τ hτ w.Completion
        (unitaryInvolutionSplitting_infinitePlace w) hfield n hn z x₀ hx₀ hz
  · let : NontriviallyNormedField (Global.FiniteCompletion F v) :=
      Valued.toNontriviallyNormedField (Global.FiniteCompletion F v) (WithZero (Multiplicative ℤ))
    have : CharZero (Global.FiniteCompletion F v) :=
      charZero_of_injective_algebraMap (algebraMap F (Global.FiniteCompletion F v)).injective
    rcases nonempty_algHom_or_isField_tensor (E := E) h2 (Global.FiniteCompletion F v)
      with hφ | hfield
    · obtain ⟨φ⟩ := hφ
      let : Algebra E (Global.FiniteCompletion F v) := φ.toRingHom.toAlgebra
      have : IsScalarTower F E (Global.FiniteCompletion F v) :=
        IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
      exact exists_regular_unitary_of_split τ hτ (Global.FiniteCompletion F v) n hn z x₀ hx₀ hz
    · let : ValuativeRel (Global.FiniteCompletion F v) := Global.FiniteCompletion.valuativeRel v
      have : IsNonarchimedeanLocalField (Global.FiniteCompletion F v) :=
        Global.FiniteCompletion.isNonarchimedeanLocalField v
      exact exists_regular_unitary_of_isField τ hτ (Global.FiniteCompletion F v)
        (Algebra.CentralSimple.unitaryDivisionSplitting _
          (localUnitaryDivisionCommutative (Global.FiniteCompletion F v)))
        hfield n hn z x₀ hx₀ hz

end Langlands.CentralSimple
