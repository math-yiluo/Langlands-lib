import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseField
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.PrimitiveElement

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing Polynomial

open scoped IntermediateField

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}}

section EtaleLift

/-- A finite separable extension `L` of the residue field `k` of a local artinian ring `R` lifts
to a local artinian, formally étale, finite type `R`-algebra `E` with residue field `L`:
`E = R[X]/(ĝ)` for a monic lift `ĝ` of the minimal polynomial of a primitive element. -/
theorem exists_etale_lift [IsLocalRing R] [IsArtinianRing R] {k L : Type u} [Field k]
    [Algebra R k] (hk : Function.Surjective (algebraMap R k)) [Field L] [Algebra k L]
    [Algebra R L] [IsScalarTower R k L] [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), IsLocalRing E ∧ IsArtinianRing E ∧
      Algebra.FormallyEtale R E ∧ Algebra.FiniteType R E ∧
        ∃ πE : E →ₐ[R] L, Function.Surjective πE := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hθi : IsIntegral k θ := IsIntegral.of_finite k θ
  let g := minpoly k θ
  have hgm : g.Monic := minpoly.monic hθi
  have hgs : g.Separable := Algebra.IsSeparable.isSeparable k θ
  obtain ⟨ĝ, hĝmap, -, hĝm⟩ := lifts_and_natDegree_eq_and_monic
    (f := algebraMap R k) (map_surjective _ hk g) hgm
  let E := AdjoinRoot ĝ
  have : Module.Finite R E := hĝm.finite_adjoinRoot
  have : IsArtinianRing E := IsArtinianRing.of_finite R E
  have hev : aeval θ ĝ = 0 := by
    rw [← Polynomial.aeval_map_algebraMap k, hĝmap]
    exact minpoly.aeval k θ
  let πE : E →ₐ[R] L := AdjoinRoot.liftAlgHom ĝ (Algebra.ofId R L) θ hev
  have hπE : ∀ q : R[X], πE (AdjoinRoot.mk ĝ q) = aeval θ (q.map (algebraMap R k)) := by
    intro q
    refine (AdjoinRoot.liftAlgHom_mk ĝ (Algebra.ofId R L) θ hev q).trans ?_
    rw [Polynomial.aeval_map_algebraMap]
    rfl
  have hπEs : Function.Surjective πE := by
    intro x
    have hx : x ∈ (k⟮θ⟯).toSubalgebra := by rw [hθ]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθi.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := map_surjective (algebraMap R k) hk p
    exact ⟨AdjoinRoot.mk ĝ q, hπE q⟩
  -- the kernel of `πE` is nil
  have hmnil : IsNilpotent ((maximalIdeal R).map (algebraMap R E)) := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  have hkerk : ∀ r : R, algebraMap R k r = 0 → r ∈ maximalIdeal R := fun r hr ↦ by
    by_contra h
    have hu : IsUnit r := by
      by_contra h'
      exact h ((mem_maximalIdeal r).mpr h')
    exact (hu.map (algebraMap R k)).ne_zero hr
  have hnil : ∀ x : E, πE x = 0 → IsNilpotent x := by
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [hπE] at hx
    obtain ⟨h, hh⟩ := minpoly.dvd k θ hx
    obtain ⟨h', rfl⟩ := map_surjective (algebraMap R k) hk h
    have hf : AdjoinRoot.mk ĝ f = AdjoinRoot.mk ĝ (f - ĝ * h') := by
      rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
    have hcoeff : ∀ i, (f - ĝ * h').coeff i ∈ maximalIdeal R := by
      intro i
      apply hkerk
      have : (f - ĝ * h').map (algebraMap R k) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hĝmap, hh, sub_self]
      have h0 := congrArg (fun p ↦ p.coeff i) this
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h0
      exact h0
    rw [hf]
    obtain ⟨n, hn⟩ := hmnil
    refine ⟨n, ?_⟩
    have hmem : AdjoinRoot.mk ĝ (f - ĝ * h') ∈ (maximalIdeal R).map (algebraMap R E) := by
      rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
      refine Ideal.sum_mem _ fun i _ ↦ ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff i))
    have := Ideal.pow_mem_pow hmem n
    rw [hn] at this
    simpa using this
  have : IsLocalRing E := isLocalRing_of_ker_nil πE.toRingHom hπEs hnil
  -- formal étaleness: `E` is the standard étale algebra of `(ĝ, ĝ')`
  let P : StandardEtalePair R := ⟨ĝ, hĝm, derivative ĝ, 1, 0, 1, by ring⟩
  have hunit : IsUnit (AdjoinRoot.mk ĝ (derivative ĝ)) := by
    by_contra hu
    have hm : AdjoinRoot.mk ĝ (derivative ĝ) ∈ maximalIdeal E := (mem_maximalIdeal _).mpr hu
    have h0 : πE (AdjoinRoot.mk ĝ (derivative ĝ)) = 0 := map_maximalIdeal_eq_zero πE.toRingHom hm
    rw [hπE, ← Polynomial.derivative_map, hĝmap] at h0
    exact hgs.aeval_derivative_ne_zero (minpoly.aeval k θ) h0
  let e₁ : E ≃ₐ[E] Localization.Away (AdjoinRoot.mk ĝ (derivative ĝ)) :=
    IsLocalization.atUnit E _ _ hunit
  let e : P.Ring ≃ₐ[R] E := P.equivAwayAdjoinRoot.trans (e₁.symm.restrictScalars R)
  have : Algebra.FormallyEtale R E := Algebra.FormallyEtale.of_equiv e
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, πE, hπEs⟩

end EtaleLift


section ChartRing

variable {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

/-- Existence of infinitesimal lifts for the minimal lift `ξ`: the formally smooth `E` lifts
`u₀` to `ψ : E → A`; the element `v` lies over `η` on the image `E / ker ψ ⊆ A`, so
`descend_general` and minimality of `J` give `J ≤ ker ψ`. -/
lemma chart_lift (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h2 : FilteredColimits F) (h5 : NilpotentInjective F) {L E : Type u} [Field L]
    [Algebra R L] [CommRing E] [Algebra R E] [IsLocalRing E] [IsArtinianRing E]
    [Algebra.FormallyEtale R E] (πE : E →ₐ[R] L) (hπE : Function.Surjective πE)
    (η : F.obj (op (ovR R L))) (J : Ideal E) (ξ : F.obj (op (ovR R (E ⧸ J))))
    (hξ : IsOver (Ideal.Quotient.mkₐ R J) πE η ξ)
    (hJmin : ∀ I : Ideal E, (∃ w : F.obj (op (ovR R (E ⧸ I))),
      IsOver (Ideal.Quotient.mkₐ R I) πE η w) → J ≤ I)
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing A] [IsArtinianRing A] (I : Ideal A)
    (hI : IsNilpotent I) (u₀ : E ⧸ J →ₐ[R] A ⧸ I) (v : F.obj (op (ovR R A)))
    (hv : res u₀ ξ = res (Ideal.Quotient.mkₐ R I) v) :
    ∃ u : E ⧸ J →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp u = u₀ ∧ res u ξ = v := by
  have hkerπ : RingHom.ker πE = maximalIdeal E :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπE)
  have hInil : ∀ a ∈ I, IsNilpotent a := fun a ha ↦ by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow ha n⟩
  let ψ₀ : E →ₐ[R] A ⧸ I := u₀.comp (Ideal.Quotient.mkₐ R J)
  let ψ : E →ₐ[R] A := Algebra.FormallySmooth.lift I hI ψ₀
  have hψ : (Ideal.Quotient.mkₐ R I).comp ψ = ψ₀ := Algebra.FormallySmooth.comp_lift I hI ψ₀
  let K := RingHom.ker ψ
  have hKle : K ≤ maximalIdeal E := fun x hx ↦ by
    by_contra h
    have hu : IsUnit x := by
      by_contra h'
      exact h ((mem_maximalIdeal x).mpr h')
    exact (hu.map ψ).ne_zero hx
  have hKnil : IsNilpotent K := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal E).mp inferInstance
    exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hKle n).trans (by rw [hn]; rfl))⟩
  let C := E ⧸ K
  have : IsLocalRing C := Charts.isLocalRing_quotient hKnil
  let : Algebra C A := (Ideal.Quotient.lift K ψ.toRingHom (fun a ha ↦ ha)).toAlgebra
  have : IsScalarTower R C A := IsScalarTower.of_algebraMap_eq fun r ↦
    (ψ.commutes r).symm
  have hinjC : Function.Injective (algebraMap C A) :=
    (Ideal.injective_lift_iff (I := K) (f := ψ.toRingHom) (fun a ha ↦ ha)).mpr rfl
  obtain ⟨πC, hπC⟩ := exists_factor (Ideal.Quotient.mkₐ R K) Ideal.Quotient.mk_surjective πE
    (fun a ha ↦ by
      rw [← RingHom.mem_ker, hkerπ]
      exact hKle ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  have hπCs : Function.Surjective πC := fun z ↦ by
    obtain ⟨x, rfl⟩ := hπE z
    exact ⟨Ideal.Quotient.mk K x, congrArg (fun f ↦ f x) hπC⟩
  -- `v` lies over `η` along `C ⊆ A`
  have hvC : IsOver (IsScalarTower.toAlgHom R C A) πC η v := by
    intro K' _ _ φ φ₀ hφ
    obtain ⟨φ', hφ'⟩ := exists_factor (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective φ
      (fun a ha ↦ ((hInil a ((Ideal.Quotient.eq_zero_iff_mem).mp ha)).map φ).eq_zero)
    rw [← hφ', ← res_res, ← hv, res_res]
    refine hξ K' _ φ₀ ?_
    ext x
    have h1 := congrArg (fun f ↦ f (Ideal.Quotient.mk K x)) hφ
    have h2 := congrArg (fun f ↦ f x) hπC
    have h3 := congrArg (fun f ↦ f x) hψ
    change φ₀ (πE x) = φ' (u₀ (Ideal.Quotient.mk J x))
    rw [← h2]
    change φ₀ (πC (Ideal.Quotient.mk K x)) = _
    refine h1.trans ?_
    change φ (ψ x) = _
    rw [← hφ']
    change φ' (Ideal.Quotient.mk I (ψ x)) = _
    exact congrArg φ' h3
  obtain ⟨w, hw⟩ := descend_general h4 hZ hF h2 h5 hinjC πC hπCs η v hvC
  have hK : J ≤ K := hJmin K ⟨w, by
    have := isOver_of_surjective (Ideal.Quotient.mkₐ R K) Ideal.Quotient.mk_surjective πC hw
    rwa [hπC] at this⟩
  let u : E ⧸ J →ₐ[R] A := Ideal.Quotient.liftₐ J ψ (fun a ha ↦ hK ha)
  have hu : (Ideal.Quotient.mkₐ R I).comp u = u₀ := by
    apply Ideal.Quotient.algHom_ext
    ext x
    exact congrArg (fun f ↦ f x) hψ
  refine ⟨u, hu, nilInj h5 A I hI ?_⟩
  rw [res_res, hu, hv]

/-- The ring-level chart. For a minimal `η ∈ F(Spec L)`, `L / k` finite separable, and a local
artinian formally étale `R`-algebra `E` with residue map `πE : E → L`, let `J` be the smallest
ideal of `E` such that `η` lifts to `E / J` (it exists by `inter_closed`). Then the lift
`ξ ∈ F(Spec (E/J))` is infinitesimally étale (existence by `descend_general` applied to the
image of the étale lift `E → A`, uniqueness by formal unramifiedness) and is a monomorphism on
points with values in fields (`mono_field`). -/
theorem exists_chart_ring (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F) (h5 : NilpotentInjective F)
    {k L E : Type u} [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (hnil : ∀ r : R, algebraMap R k r = 0 → IsNilpotent r) [Field L] [Algebra k L]
    [Algebra R L] [IsScalarTower R k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [CommRing E] [Algebra R E] [IsLocalRing E] [IsArtinianRing E] [Algebra.FormallyEtale R E]
    (πE : E →ₐ[R] L) (hπE : Function.Surjective πE) (η : F.obj (op (ovR R L)))
    (hmin : IsMinimal η) :
    ∃ (J : Ideal E) (ξ : F.obj (op (ovR R (E ⧸ J)))), J ≤ RingHom.ker πE ∧
      IsOver (Ideal.Quotient.mkₐ R J) πE η ξ ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A] [IsArtinianRing A]
        (I : Ideal A), IsNilpotent I → ∀ (u₀ : E ⧸ J →ₐ[R] A ⧸ I) (v : F.obj (op (ovR R A))),
          res u₀ ξ = res (Ideal.Quotient.mkₐ R I) v →
            ∃! u : E ⧸ J →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp u = u₀ ∧ res u ξ = v) ∧
      (∀ (K : Type u) [Field K] [Algebra R K] (φ₁ φ₂ : E ⧸ J →ₐ[R] K),
        res φ₁ ξ = res φ₂ ξ → φ₁ = φ₂) := by
  classical
  have hkerπ : RingHom.ker πE = maximalIdeal E :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπE)
  let 𝒥 : Set (Ideal E) := {I | ∃ w : F.obj (op (ovR R (E ⧸ I))),
    IsOver (Ideal.Quotient.mkₐ R I) πE η w}
  have hker : RingHom.ker πE ∈ 𝒥 := by
    let e := Ideal.quotientKerAlgEquivOfSurjective hπE
    refine ⟨res e.symm.toAlgHom η, ?_⟩
    have : e.toAlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker πE)) = πE := by
      ext x
      rfl
    have h := isOver_of_surjective (η := η) (Ideal.Quotient.mkₐ R (RingHom.ker πE))
      Ideal.Quotient.mk_surjective e.toAlgHom (w := res e.symm.toAlgHom η) (by
        rw [res_res]
        convert res_id η using 2
        exact AlgHom.ext fun x ↦ e.apply_symm_apply x)
    rwa [this] at h
  obtain ⟨J, hJ, hJmin'⟩ := (wellFounded_lt (α := Ideal E)).has_min 𝒥 ⟨_, hker⟩
  have hJmin : ∀ I ∈ 𝒥, J ≤ I := by
    intro I hI
    have hJI : J ⊓ I ∈ 𝒥 := inter_closed h4 hZ h5 πE hπE η J I hJ hI
    by_contra hne
    exact hJmin' _ hJI (lt_of_le_of_ne inf_le_left (fun h ↦ hne (h ▸ inf_le_right)))
  obtain ⟨ξ, hξ⟩ := hJ
  have hJker : J ≤ RingHom.ker πE := hJmin _ hker
  refine ⟨J, ξ, hJker, hξ, ?_, ?_⟩
  · intro A _ _ _ _ I hI u₀ v hv
    obtain ⟨u, hu, huv⟩ := chart_lift h4 hZ hF h2 h5 πE hπE η J ξ hξ hJmin I hI u₀ v hv
    refine ⟨u, ⟨hu, huv⟩, fun u' ⟨hu', _⟩ ↦ ?_⟩
    exact Algebra.FormallyUnramified.ext I hI fun x ↦ by
      have h1 := congrArg (fun f ↦ f x) hu
      have h2 := congrArg (fun f ↦ f x) hu'
      exact h2.trans h1.symm
  · intro K _ _ φ₁ φ₂ hφ
    obtain ⟨πJ, hπJ⟩ := exists_factor (Ideal.Quotient.mkₐ R J) Ideal.Quotient.mk_surjective πE
      (fun a ha ↦ by
        rw [← RingHom.mem_ker]
        exact hJker ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
    have hπJs : Function.Surjective πJ := fun z ↦ by
      obtain ⟨x, rfl⟩ := hπE z
      exact ⟨Ideal.Quotient.mk J x, congrArg (fun f ↦ f x) hπJ⟩
    have hres : res πJ ξ = η := by
      have := hξ L πJ (AlgHom.id R L) (by rw [AlgHom.id_comp, hπJ])
      rwa [res_id] at this
    have : IsLocalRing (E ⧸ J) := Charts.isLocalRing_quotient (by
      obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal E).mp inferInstance
      exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono (hJker.trans hkerπ.le) n).trans
        (by rw [hn]; rfl))⟩)
    have hkerJ : RingHom.ker πJ = maximalIdeal (E ⧸ J) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπJs)
    obtain ⟨φ₁', h₁⟩ := exists_factor πJ hπJs φ₁ (fun a ha ↦ map_maximalIdeal_eq_zero
      φ₁.toRingHom (by rw [← hkerJ]; exact ha))
    obtain ⟨φ₂', h₂⟩ := exists_factor πJ hπJs φ₂ (fun a ha ↦ map_maximalIdeal_eq_zero
      φ₂.toRingHom (by rw [← hkerJ]; exact ha))
    have h' : res φ₁' η = res φ₂' η := by
      rw [← hres, res_res, res_res, h₁, h₂, hφ]
    have := mono_field hZ hF h5 hk hnil hmin φ₁' φ₂' h'
    rw [← h₁, ← h₂, this]

end ChartRing

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
