import Langlands.Automorphic.Unramified.WeakInductionOrbitRestriction
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.OperatorDeterminantTwistClasses
import Mathlib.FieldTheory.KummerExtension

/-! # Weak induction from weak base change to the full Galois orbit and a norm self-twist

For a cyclic extension `E/F`, a lower cuspidal class `c` fixed by the determinant twist by
a Hecke character `η` with exactly the norm kernel, and an upper cuspidal class `d` whose
full Galois orbit is a weak base change of `c`, the class `c` is weakly induced from `d`.

At almost every base place `v` the local value `ζ = η_v(ϖ_v)` has order the common
residue degree `f` above `v`. The self-twist makes the lower spectrum stable under
multiplication by `ζ`, so it is a union of full orbits of `f` roots. The weak base change
identifies its `f`-th powers with `f` copies of the upper spectra at the places above `v`;
cancelling the `f` copies gives the induced Euler polynomial.
-/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Unramified Global Global.AdelicFunctoriality CuspidalOperatorRealization
open Polynomial Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

namespace CyclicOrbitWeakInduction

section Algebra

variable {ζ : ℂˣ} {f : ℕ}

/-- The orbit `α, ζ α, …, ζ ^ (f - 1) α` of a nonzero number under multiplication by `ζ`. -/
def rootOrbit (ζ : ℂˣ) (f : ℕ) (α : ℂˣ) : Multiset ℂˣ :=
  (Multiset.range f).map fun i => ζ ^ i * α

/-- For a primitive `f`-th root of unity `ζ`, the orbit of `α` consists of the
`f`-th roots of `α ^ f`. -/
theorem mem_rootOrbit (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f) {α x : ℂˣ} :
    x ∈ rootOrbit ζ f α ↔ x ^ f = α ^ f := by
  constructor
  · intro hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mul_pow, ← pow_mul, mul_comm i f, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  · intro hx
    have : NeZero f := ⟨hf.ne'⟩
    have h1 : x * α⁻¹ ∈ rootsOfUnity f ℂ := by
      rw [mem_rootsOfUnity, mul_pow, hx, inv_pow, mul_inv_cancel]
    obtain ⟨i, hi, hζi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    exact Multiset.mem_map.mpr ⟨i, Multiset.mem_range.mpr hi, by rw [hζi, inv_mul_cancel_right]⟩

theorem nodup_rootOrbit (hζ : IsPrimitiveRoot ζ f) (α : ℂˣ) : (rootOrbit ζ f α).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range f)
  intro i hi j hj h
  exact hζ.pow_inj (Multiset.mem_range.mp hi) (Multiset.mem_range.mp hj) (mul_right_cancel h)

@[simp] theorem card_rootOrbit (ζ : ℂˣ) (f : ℕ) (α : ℂˣ) :
    Multiset.card (rootOrbit ζ f α) = f := by
  simp [rootOrbit]

/-- A multiset stable under multiplication by `ζ` contains the whole orbit of each
of its elements. -/
theorem rootOrbit_le (hζ : IsPrimitiveRoot ζ f) {A : Multiset ℂˣ}
    (hinv : A.map (fun z => ζ * z) = A) {α : ℂˣ} (hα : α ∈ A) : rootOrbit ζ f α ≤ A := by
  have hstep : ∀ z ∈ A, ζ * z ∈ A := fun z hz => by
    rw [← hinv]
    exact Multiset.mem_map_of_mem _ hz
  have hpow : ∀ i : ℕ, ζ ^ i * α ∈ A := by
    intro i
    induction i with
    | zero => simpa using hα
    | succ i ih =>
      rw [pow_succ', mul_assoc]
      exact hstep _ ih
  refine (Multiset.le_iff_subset (nodup_rootOrbit hζ α)).mpr fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
  exact hpow i

theorem map_mul_rootOrbit (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f) (α : ℂˣ) :
    (rootOrbit ζ f α).map (fun z => ζ * z) = rootOrbit ζ f α := by
  refine (Multiset.Nodup.ext ((nodup_rootOrbit hζ α).map (mul_right_injective ζ))
    (nodup_rootOrbit hζ α)).mpr fun x => ?_
  rw [mem_rootOrbit hζ hf, Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_rootOrbit hζ hf] at hy
    rw [mul_pow, hζ.pow_eq_one, one_mul, hy]
  · intro hx
    refine ⟨ζ⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [mem_rootOrbit hζ hf, mul_pow, inv_pow, hζ.pow_eq_one, inv_one, one_mul, hx]

theorem map_pow_rootOrbit (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f) (α : ℂˣ) :
    (rootOrbit ζ f α).map (fun z => z ^ f) = Multiset.replicate f (α ^ f) := by
  rw [Multiset.eq_replicate]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hb
  exact (mem_rootOrbit hζ hf).mp hx

/-- The Euler factors of an orbit multiply to `1 - α ^ f X ^ f`. -/
theorem prod_rootOrbit (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f) (α : ℂˣ) :
    ((rootOrbit ζ f α).map fun z : ℂˣ => 1 - C (z : ℂ) * X).prod =
      1 - C (((α ^ f : ℂˣ)) : ℂ) * X ^ f := by
  have hζC : IsPrimitiveRoot (C (ζ : ℂ)) f :=
    (IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective Polynomial.C_injective
  have key := congrArg (Polynomial.eval (1 : ℂ[X]))
    (X_pow_sub_C_eq_prod hζC hf (α := C (α : ℂ) * X) (a := C ((α : ℂ) ^ f) * X ^ f)
      (by rw [mul_pow, ← C_pow]))
  simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C, eval_prod] at key
  rw [Units.val_pow_eq_pow_val, key, rootOrbit, Multiset.map_map]
  change ((Finset.range f).val.map _).prod = _
  rw [Finset.prod_map_val]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Units.val_mul, Units.val_pow_eq_pow_val, C_mul, C_pow, mul_assoc]

/-- A multiset stable under a primitive `f`-th root of unity whose `f`-th powers
are `f` copies of `B` is a union of full orbits indexed by a lift of `B`. -/
theorem exists_rootOrbit_decomposition (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f)
    (A B : Multiset ℂˣ) (hinv : A.map (fun z => ζ * z) = A)
    (hpow : A.map (fun z => z ^ f) = f • B) :
    ∃ L : Multiset ℂˣ, A = L.bind (rootOrbit ζ f) ∧ L.map (fun z => z ^ f) = B := by
  suffices h : ∀ (N : ℕ) (A B : Multiset ℂˣ), Multiset.card A = N →
      A.map (fun z => ζ * z) = A → A.map (fun z => z ^ f) = f • B →
      ∃ L : Multiset ℂˣ, A = L.bind (rootOrbit ζ f) ∧ L.map (fun z => z ^ f) = B from
    h _ A B rfl hinv hpow
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A B hA hinv hpow
  rcases Multiset.empty_or_exists_mem A with rfl | ⟨α, hα⟩
  · refine ⟨0, by simp, ?_⟩
    have hcard : Multiset.card (f • B) = 0 := by rw [← hpow]; simp
    rw [Multiset.card_nsmul, mul_eq_zero] at hcard
    rcases hcard with h | h
    · omega
    · simpa using (Multiset.card_eq_zero.mp h).symm
  · obtain ⟨A₁, rfl⟩ := Multiset.le_iff_exists_add.mp (rootOrbit_le hζ hinv hα)
    have hinv₁ : A₁.map (fun z => ζ * z) = A₁ := by
      rw [Multiset.map_add, map_mul_rootOrbit hζ hf] at hinv
      exact add_left_cancel hinv
    rw [Multiset.map_add, map_pow_rootOrbit hζ hf] at hpow
    have hmem : α ^ f ∈ B := by
      have h : α ^ f ∈ f • B := by
        rw [← hpow]
        exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_replicate.mpr ⟨hf.ne', rfl⟩))
      exact Multiset.mem_of_mem_nsmul h
    obtain ⟨B₁, rfl⟩ : ∃ B₁, B = α ^ f ::ₘ B₁ :=
      ⟨B.erase (α ^ f), (Multiset.cons_erase hmem).symm⟩
    rw [Multiset.nsmul_cons, Multiset.nsmul_singleton] at hpow
    have hpow₁ := add_left_cancel hpow
    have hcard : Multiset.card A₁ < N := by
      rw [← hA, Multiset.card_add, card_rootOrbit]
      omega
    obtain ⟨L₁, rfl, hL₁⟩ := ih _ hcard A₁ B₁ rfl hinv₁ hpow₁
    exact ⟨α ::ₘ L₁, by rw [Multiset.cons_bind], by rw [Multiset.map_cons, hL₁]⟩

/-- The Euler polynomial of a `ζ`-stable spectrum whose `f`-th powers are `f`
copies of `B`. -/
theorem eulerPolynomial_eq_of_rootOrbit (hζ : IsPrimitiveRoot ζ f) (hf : 0 < f) {n : ℕ}
    (a : Eigenvalues n) (B : Multiset ℂˣ)
    (hinv : (a : Multiset ℂˣ).map (fun z => ζ * z) = a)
    (hpow : (a : Multiset ℂˣ).map (fun z => z ^ f) = f • B) :
    a.eulerPolynomial = (B.map fun β : ℂˣ => 1 - C (β : ℂ) * X ^ f).prod := by
  obtain ⟨L, hA, hL⟩ := exists_rootOrbit_decomposition hζ hf _ B hinv hpow
  rw [Eigenvalues.eulerPolynomial, hA, Multiset.map_bind, Multiset.prod_bind, ← hL,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun α _ => prod_rootOrbit hζ hf α

/-- The induced Euler polynomial of a family of spectra with a common residue degree. -/
theorem prod_eulerPolynomial_comp {J : Type*} [Fintype J] {m : ℕ} (b : J → Eigenvalues m)
    (f : ℕ) :
    ∏ j, (b j).eulerPolynomial.comp (X ^ f) =
      ((∑ j, (b j : Multiset ℂˣ)).map fun β : ℂˣ => 1 - C (β : ℂ) * X ^ f).prod := by
  rw [show (∑ j, (b j : Multiset ℂˣ)).map (fun β : ℂˣ => 1 - C (β : ℂ) * X ^ f) =
      ∑ j, (b j : Multiset ℂˣ).map (fun β : ℂˣ => 1 - C (β : ℂ) * X ^ f) from
    map_sum (Multiset.mapAddMonoidHom fun β : ℂˣ => 1 - C (β : ℂ) * X ^ f) _ _,
    Multiset.prod_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Eigenvalues.eulerPolynomial, Polynomial.multiset_prod_comp, Multiset.map_map]
  simp [sub_comp, mul_comp]

end Algebra

section Places

open scoped Classical

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

omit [NumberField F] [IsGalois F E] in
private theorem placeOrbit_mul_aux {v : Global.FinitePlace F} (w : FinitePlacesAbove E v)
    (σ τ : E ≃ₐ[F] E) : placeOrbit w (σ * τ) = placeOrbit (placeOrbit w σ) τ := by
  apply Subtype.ext
  change finitePlaceEquiv (τ.toRingEquiv.trans σ.toRingEquiv) w.1 =
    finitePlaceEquiv τ.toRingEquiv (finitePlaceEquiv σ.toRingEquiv w.1)
  rw [finitePlaceEquiv_trans]
  rfl

omit [NumberField F] [IsGalois F E] in
private theorem placeOrbit_one_aux {v : Global.FinitePlace F} (w : FinitePlacesAbove E v) :
    placeOrbit w (1 : E ≃ₐ[F] E) = w := by
  apply Subtype.ext
  change finitePlaceEquiv (RingEquiv.refl E) w.1 = w.1
  rw [finitePlaceEquiv_refl]
  rfl

private theorem placeOrbit_surjective_aux {v : Global.FinitePlace F}
    (w : FinitePlacesAbove E v) : Function.Surjective (placeOrbit w) := by
  intro q
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 E) (E ≃ₐ[F] E)
    q.1.asIdeal w.1.asIdeal
    ((Ideal.LiesOver.over (P := q.1.asIdeal) (p := v.asIdeal)).symm.trans
      (Ideal.LiesOver.over (P := w.1.asIdeal) (p := v.asIdeal)))
  refine ⟨σ, Subtype.ext (HeightOneSpectrum.ext ?_)⟩
  change (finitePlaceEquiv σ.toRingEquiv w.1).asIdeal = q.1.asIdeal
  rw [finitePlaceEquiv_asIdeal, hσ]
  ext x
  rw [Ideal.mem_comap]
  exact Ideal.smul_mem_pointwise_smul_iff

/-- If every place above `v` is unramified of residue degree `f`, every fibre of the
orbit map of a place above `v` has `f` elements. -/
private theorem card_placeOrbit_fibre {v : Global.FinitePlace F} (w q : FinitePlacesAbove E v)
    (f : ℕ) (he : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hf : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.inertiaDeg (𝓞 F) = f) :
    (Finset.univ.filter fun σ => placeOrbit w σ = q).card = f := by
  classical
  have hcard (x y : FinitePlacesAbove E v) :
      (Finset.univ.filter fun σ => placeOrbit w σ = x).card =
        (Finset.univ.filter fun σ => placeOrbit w σ = y).card := by
    obtain ⟨g, hg⟩ := placeOrbit_surjective_aux x y
    refine Finset.card_nbij' (fun σ => σ * g) (fun σ => σ * g⁻¹) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [placeOrbit_mul_aux, hσ]
      exact hg
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [placeOrbit_mul_aux, hσ, ← hg, ← placeOrbit_mul_aux, mul_inv_cancel]
      exact placeOrbit_one_aux x
    · intro σ _
      simp
    · intro σ _
      simp
  have hsum := Finset.card_eq_sum_card_fiberwise (f := placeOrbit w)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hdegree := finitePlacesAbove_sum_ramification_inertia (L := E) v
  simp only [he, hf, one_mul, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hdegree
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card (α := E ≃ₐ[F] E),
    IsGalois.card_aut_eq_finrank F E, fun x => hcard x q, Finset.sum_const, smul_eq_mul] at hsum
  let : Nonempty (FinitePlacesAbove E v) := ⟨w⟩
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos (hsum.symm.trans hdegree.symm)

/-- Summing a function of places over the full Galois orbit of one place counts each
place above `v` exactly `f` times. -/
theorem sum_placeOrbit {v : Global.FinitePlace F} (w : FinitePlacesAbove E v) (f : ℕ)
    (he : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hf : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.inertiaDeg (𝓞 F) = f)
    (a : FinitePlacesAbove E v → Multiset ℂˣ) :
    (∑ σ : E ≃ₐ[F] E, a (placeOrbit w σ)) = f • ∑ q, a q := by
  classical
  rw [Finset.smul_sum]
  calc
    (∑ σ : E ≃ₐ[F] E, a (placeOrbit w σ)) =
        ∑ q : FinitePlacesAbove E v,
          ∑ σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a (placeOrbit w σ) :=
      (Finset.sum_fiberwise_of_maps_to (g := placeOrbit w)
        (fun _ _ => Finset.mem_univ _) (fun σ => a (placeOrbit w σ))).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [show (∑ σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a (placeOrbit w σ)) =
        ∑ _σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a q from
          Finset.sum_congr rfl fun σ hσ => congrArg a (Finset.mem_filter.mp hσ).2,
        Finset.sum_const, card_placeOrbit_fibre w q f he hf]

end Places

end CyclicOrbitWeakInduction

open CyclicOrbitWeakInduction

/-- Arthur–Clozel III.6, the calculation after (6.5)–(6.6), in arbitrary cyclic degree:
weak base change to the full Galois orbit together with the norm-kernel self-twist
gives weak induction. -/
theorem cyclicOrbitBaseChangeWeakInduction :
    CyclicOrbitBaseChangeWeakInductionStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ _ _ η hη r m c d htw hBC
  classical
  obtain ⟨hR, s, tO, hs, htO, hst⟩ := hBC
  -- An actual presentation of the lower class.
  obtain ⟨s₀, hs₀, hs₀s⟩ := hs.exists_ofCuspidal
  have hs₀' : IsoClass.HasSpectralSystem.{uF, uV} c s₀ := hs₀
  obtain ⟨S, P, hS, rfl⟩ := hs₀'
  subst hS
  -- An actual presentation of the upper class, read off from the orbit attachment.
  obtain ⟨T, Q, hT⟩ : ∃ (T : CuspidalOperatorRealization E m)
      (_ : CuspidalSpectralPresentation.{uE, uW} T), T.isoClass = d := by
    obtain ⟨k, σ, hσ, t, ht, -⟩ := htO
    have hmem : PositiveRankCuspidalClass.ofFixedRank d ∈ Finset.univ.val.map σ := by
      rw [hσ]
      exact Multiset.mem_map.mpr ⟨1, Finset.mem_univ_val _,
        PositiveRankCuspidalClass.galoisConj_one (F := F) _⟩
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
    have aux : ∀ (c' : PositiveRankCuspidalClass E)
        (t' : SpectralSystem (Global.FinitePlace E) c'.rank),
        c' = PositiveRankCuspidalClass.ofFixedRank d →
        PositiveRankCuspidalClass.HasSpectralSystem.{uE, uW} c' t' →
        ∃ (T : CuspidalOperatorRealization E m)
          (_ : CuspidalSpectralPresentation.{uE, uW} T), T.isoClass = d := by
      rintro c' t' rfl ⟨T, Q, hT, -⟩
      exact ⟨T, Q, hT⟩
    exact aux (σ j) (t j) hj (ht j)
  subst hT
  -- The genuine Galois attachment of the full orbit, built from `Q`.
  let ce := PositiveRankCuspidalClass.ofFixedRank T.isoClass
  let O := IsobaricData.galoisOrbit F ce
  let k := Fintype.card (E ≃ₐ[F] E)
  let e : Fin k ≃ (E ≃ₐ[F] E) := (Fintype.equivFin _).symm
  let σ (i : Fin k) := ce.galoisConj (e i)
  let b (i : Fin k) := (Q.arithmeticComap (e i).toRingEquiv.symm).spectralSystem
  let tSum := SpectralSystem.finiteSum b
  have hEnum : Finset.univ.val.map σ = O := by
    change Finset.univ.val.map ((fun g => ce.galoisConj g) ∘ e) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    rfl
  have hRt : (∑ _ : Fin k, (m + 1)) = O.rank := by
    simp [O, IsobaricData.rank_galoisOrbit, ce, k]
  let tO' : SpectralSystem (Global.FinitePlace E) O.rank := hRt ▸ tSum
  have htO' : O.HasSpectralSystem.{uE, uW} tO' := by
    refine ⟨k, σ, hEnum, b, fun i => ⟨_, Q.arithmeticComap (e i).toRingEquiv.symm, rfl, rfl⟩, ?_⟩
    exact Filter.Eventually.of_forall fun q hq hq' =>
      (SpectralSystem.eulerPolynomial_eqRec hRt tSum q hq' hq).symm
  have hsame : tO.SameEulerPolynomials tO' := htO.sameEulerPolynomials htO'
  -- The rank equation.
  have hrank : r + 1 = (m + 1) * Module.finrank F E := by
    have h := hR
    rw [IsobaricData.rank_galoisOrbit_of_isGalois, IsobaricData.rank_ofCuspidal] at h
    change Module.finrank F E * (m + 1) = r + 1 at h
    rw [mul_comm]
    exact h.symm
  -- The self-twist: the scaled spectral system is attached to the same class.
  have hfin : η.HasFiniteOrder := hη.hasFiniteOrder
  have hfix : IsoClass.determinantTwist S.isoClass η hfin = S.isoClass :=
    ((IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ η hfin).mp htw).symm
  have hscaled := IsoClass.HasSpectralSystem.determinantTwist
    (c := S.isoClass) ⟨S, P, rfl, rfl⟩ η hfin
  rw [hfix] at hscaled
  refine ⟨P.spectralSystem, Q.spectralSystem, ⟨S, P, rfl, rfl⟩, ⟨T, Q, rfl, rfl⟩, hrank, ?_⟩
  filter_upwards [hst, hs₀s,
    (P.exceptional ∪ η.finiteDeterminantTail (r + 1) hfin).eventually_cofinite_notMem,
    hsame.eventually_above (F := F),
    SpectralSystem.eventually_avoidsAbove (F := F) Q.exceptional,
    HeckeCharacter.cyclicNormKernelUnramifiedOrder.{uF, uE} F E η hη]
    with v hv1 hv2 hv3 hv4 hv5 hv6
  obtain ⟨hvs, hvt, he, heig⟩ := hv1
  have hvP : v ∉ P.spectralSystem.exceptional := fun h => hv3 (Finset.mem_union_left _ h)
  have hvQ : ∀ q : FinitePlacesAbove E v, q.1 ∉ Q.spectralSystem.exceptional := hv5
  refine ⟨hvP, hvQ, he, ?_⟩
  set ζ := η.finiteUniformizerValue v
  set f := orderOf ζ
  have hf_eq : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.inertiaDeg (𝓞 F) = f :=
    fun w => (hv6.2 w).2.symm
  obtain ⟨w₀⟩ : Nonempty (FinitePlacesAbove E v) := inferInstance
  have hf : 0 < f := by
    rw [← hf_eq w₀]
    exact w₀.1.asIdeal.inertiaDeg_pos (𝓞 F)
  have hζ : IsPrimitiveRoot ζ f := IsPrimitiveRoot.orderOf ζ
  -- Invariance of the lower spectrum under multiplication by `ζ`.
  have hinv : ((P.spectralSystem.eigenvalues v hvP : Eigenvalues (r + 1)) : Multiset ℂˣ).map
      (fun z => ζ * z) = P.spectralSystem.eigenvalues v hvP := by
    have h1 := IsoClass.HasSpectralSystem.eigenvalues_eq ⟨S, P, rfl, rfl⟩ hscaled v hvP hv3
    conv_rhs => rw [h1]
    rfl
  -- The `f`-th powers of the lower spectrum are `f` copies of the upper spectra.
  have hpow : ((P.spectralSystem.eigenvalues v hvP : Eigenvalues (r + 1)) : Multiset ℂˣ).map
      (fun z => z ^ f) =
        f • ∑ q : FinitePlacesAbove E v,
          ((Q.spectralSystem.eigenvalues q.1 (hvQ q) : Eigenvalues (m + 1)) : Multiset ℂˣ) := by
    have hsP : s.eigenvalues v hvs = P.spectralSystem.eigenvalues v hvP :=
      Eigenvalues.eulerPolynomial_injective (hv2 hvP hvs).symm
    have hw₀ : w₀.1 ∉ tO.exceptional := by
      simpa only [SpectralSystem.exceptional_eqRec] using hvt w₀
    have hw₀' : w₀.1 ∉ tO'.exceptional := (hv4 w₀).1
    have hB : w₀.1 ∉ tSum.exceptional := by
      simpa only [tO', SpectralSystem.exceptional_eqRec] using hw₀'
    have hOO : tO.eigenvalues w₀.1 hw₀ = tO'.eigenvalues w₀.1 hw₀' :=
      Eigenvalues.eulerPolynomial_injective ((hv4 w₀).2 hw₀ hw₀')
    have h1 : (((hR ▸ tO).eigenvalues w₀.1 (hvt w₀) : Eigenvalues _) : Multiset ℂˣ) =
        (((s.eigenvalues v hvs).power (w₀.1.asIdeal.inertiaDeg (𝓞 F)) : Eigenvalues _) :
          Multiset ℂˣ) :=
      congrArg _ (heig w₀)
    rw [SpectralSystem.coe_eigenvalues_eqRec hR tO _ _ hw₀, hOO,
      SpectralSystem.coe_eigenvalues_eqRec hRt tSum _ _ hB, hsP, hf_eq w₀] at h1
    rw [← sum_placeOrbit w₀ f he hf_eq
      (fun q => ((Q.spectralSystem.eigenvalues q.1 (hvQ q) : Eigenvalues (m + 1)) :
        Multiset ℂˣ))]
    refine h1.symm.trans ?_
    have hB' : w₀.1 ∉ SpectralSystem.familyExceptional b := hB
    change (∑ i : Fin k, ((b i).eigenvalues w₀.1
      (SpectralSystem.not_mem_exceptional b _ hB' i) : Multiset ℂˣ)) = _
    exact e.sum_comp fun g =>
      ((Q.spectralSystem.eigenvalues (placeOrbit w₀ g).1 (hvQ (placeOrbit w₀ g)) :
        Eigenvalues (m + 1)) : Multiset ℂˣ)
  change (P.spectralSystem.eigenvalues v hvP).eulerPolynomial = _
  rw [eulerPolynomial_eq_of_rootOrbit hζ hf _ _ hinv hpow]
  change _ = ∏ w : FinitePlacesAbove E v,
    (Q.spectralSystem.eulerPolynomial w.1 (hvQ w)).comp (X ^ w.1.asIdeal.inertiaDeg (𝓞 F))
  simp only [hf_eq]
  exact (prod_eulerPolynomial_comp
    (fun q : FinitePlacesAbove E v => Q.spectralSystem.eigenvalues q.1 (hvQ q)) f).symm

end Langlands.Automorphic.Unramified
