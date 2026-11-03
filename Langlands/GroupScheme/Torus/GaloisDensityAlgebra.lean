import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finsupp.Ext
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Algebraic input for the density of rational points of tori

Laurent polynomial algebras `R[t_i^{± 1} : i ∈ I]` are modelled by
`AddMonoidAlgebra R (I →₀ ℤ)`. For a finite Galois extension `K / k` of an infinite field we
show that a nonzero Laurent polynomial over `K` does not vanish at all "norm-shaped" points
`i ↦ ∏_σ σ (y_σ(t))`. This is the algebraic core of the density of rational points of a torus
split by `K`.
-/

noncomputable section

open AddMonoidAlgebra

namespace Langlands.GroupScheme.TorusDensity

/-! ### Evaluation of Laurent polynomials -/

section Eval

variable {I : Type*} {A : Type*} [CommRing A]

/-- Evaluation of Laurent monomials at a family of units. -/
def evalMonoid (t : I → Aˣ) : Multiplicative (I →₀ ℤ) →* Aˣ where
  toFun m := m.toAdd.prod fun i n => t i ^ n
  map_one' := Finsupp.prod_zero_index
  map_mul' _ _ :=
    Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem evalMonoid_apply (t : I → Aˣ) (m : Multiplicative (I →₀ ℤ)) :
    evalMonoid t m = m.toAdd.prod fun i n => t i ^ n := rfl

theorem evalMonoid_single (t : I → Aˣ) (i : I) (n : ℤ) :
    evalMonoid t (.ofAdd (Finsupp.single i n)) = t i ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

theorem evalMonoid_one (m : Multiplicative (I →₀ ℤ)) : evalMonoid (1 : I → Aˣ) m = 1 := by
  simp [evalMonoid_apply]

theorem evalMonoid_const_one (m : Multiplicative (I →₀ ℤ)) :
    evalMonoid (fun _ : I => (1 : Aˣ)) m = 1 :=
  evalMonoid_one m

theorem evalMonoid_mul (t t' : I → Aˣ) (m : Multiplicative (I →₀ ℤ)) :
    evalMonoid (t * t') m = evalMonoid t m * evalMonoid t' m := by
  simp only [evalMonoid_apply, Pi.mul_apply, mul_zpow]
  exact Finsupp.prod_mul

theorem evalMonoid_map {B : Type*} [CommRing B] (f : A →+* B) (t : I → Aˣ)
    (m : Multiplicative (I →₀ ℤ)) :
    Units.map f.toMonoidHom (evalMonoid t m) =
      evalMonoid (fun i => Units.map f.toMonoidHom (t i)) m := by
  simp only [evalMonoid_apply, map_finsuppProd, map_zpow]

theorem evalMonoid_mapDomain {J : Type*} (f : I → J) (t : J → Aˣ) (m : I →₀ ℤ) :
    evalMonoid t (.ofAdd (Finsupp.mapDomain f m)) = evalMonoid (fun i => t (f i)) (.ofAdd m) :=
  Finsupp.prod_mapDomain_index (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

/-- Over a finite index type, evaluation of a monomial is a finite product. -/
theorem evalMonoid_eq_prod [Fintype I] (t : I → Aˣ) (m : I →₀ ℤ) :
    evalMonoid t (.ofAdd m) = ∏ i, t i ^ m i :=
  Finsupp.prod_fintype _ _ fun _ => zpow_zero _

variable (R : Type*) [CommRing R]

/-- The monomial units `t^m` of the Laurent polynomial algebra. -/
def monomialUnit : Multiplicative (I →₀ ℤ) →* (AddMonoidAlgebra R (I →₀ ℤ))ˣ :=
  (of R (I →₀ ℤ)).toHomUnits

/-- The coordinate unit `t_i`. -/
def coord (i : I) : (AddMonoidAlgebra R (I →₀ ℤ))ˣ :=
  monomialUnit R (.ofAdd (Finsupp.single i 1))

theorem coe_monomialUnit (m : Multiplicative (I →₀ ℤ)) :
    (monomialUnit R m : AddMonoidAlgebra R (I →₀ ℤ)) = single m.toAdd 1 := rfl

theorem coe_coord (i : I) :
    (coord R i : AddMonoidAlgebra R (I →₀ ℤ)) = single (Finsupp.single i 1) 1 := rfl

/-- Two monoid homomorphisms out of the monomials agree once they agree on the
coordinates. -/
theorem monoidHom_ext {M : Type*} [Monoid M] {f g : Multiplicative (I →₀ ℤ) →* M}
    (h : ∀ i, f (.ofAdd (Finsupp.single i 1)) = g (.ofAdd (Finsupp.single i 1))) : f = g :=
  Finsupp.mulHom_ext' fun i => MonoidHom.ext_mint (h i)

/-- Evaluating the monomials at the coordinates gives back the monomials. -/
theorem evalMonoid_coord : evalMonoid (coord R (I := I)) = monomialUnit R :=
  monoidHom_ext fun i => by rw [evalMonoid_single, zpow_one]; rfl

variable [Algebra R A]

/-- The `R`-algebra map from Laurent polynomials sending `t_i` to the unit `t i`. -/
def lev (t : I → Aˣ) : AddMonoidAlgebra R (I →₀ ℤ) →ₐ[R] A :=
  AddMonoidAlgebra.lift R A (I →₀ ℤ) ((Units.coeHom A).comp (evalMonoid t))

theorem lev_single (t : I → Aˣ) (m : I →₀ ℤ) (r : R) :
    lev R t (single m r) = r • (evalMonoid t (.ofAdd m) : A) := by
  simp [lev]

theorem lev_coeff_sum (t : I → Aˣ) (F : AddMonoidAlgebra R (I →₀ ℤ)) :
    lev R t F = F.coeff.sum fun m r => r • (evalMonoid t (.ofAdd m) : A) := by
  rw [lev, AddMonoidAlgebra.lift_apply]
  rfl

theorem lev_coord (t : I → Aˣ) (i : I) : lev R t (coord R i) = t i := by
  rw [coe_coord, lev_single, evalMonoid_single, zpow_one, one_smul]

/-- `R`-algebra maps out of the Laurent algebra are determined by the images of the
coordinate units. -/
theorem algHom_ext_coord {f g : AddMonoidAlgebra R (I →₀ ℤ) →ₐ[R] A}
    (h : ∀ i : I, f (coord R i : AddMonoidAlgebra R (I →₀ ℤ)) =
      g (coord R i : AddMonoidAlgebra R (I →₀ ℤ))) : f = g := by
  apply (AddMonoidAlgebra.lift R A (I →₀ ℤ)).symm.injective
  exact monoidHom_ext fun i => by simpa [coe_coord] using h i

end Eval

/-! ### Galois characters -/

section Galois

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- A `k`-automorphism of `K` acting on units. -/
def gal (σ : K ≃ₐ[k] K) : Kˣ →* Kˣ := Units.map (σ : K →+* K).toMonoidHom

@[simp] theorem coe_gal (σ : K ≃ₐ[k] K) (s : Kˣ) : (gal σ s : K) = σ s := rfl

variable [FiniteDimensional k K]

/-- A product of integral powers of Galois conjugates which is trivial on all units has all
exponents zero. This is where the infinitude of `k` is used. -/
theorem exponents_eq_zero [Infinite k] [Algebra.IsSeparable k K]
    (d : (K ≃ₐ[k] K) → ℤ) (h : ∀ s : Kˣ, ∏ σ, gal σ s ^ d σ = 1) : d = 0 := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable k K
  set α : K := pb.gen
  have hinj : Function.Injective fun σ : K ≃ₐ[k] K => σ α := fun σ τ hστ =>
    AlgEquiv.coe_toAlgHom_injective (pb.algHom_ext hστ)
  let e : (K ≃ₐ[k] K) → ℕ := fun σ => (d σ).toNat
  let f : (K ≃ₐ[k] K) → ℕ := fun σ => (-d σ).toNat
  have hd : ∀ σ, d σ = (e σ : ℤ) - (f σ : ℤ) := fun σ => (Int.toNat_sub_toNat_neg (d σ)).symm
  let P : ((K ≃ₐ[k] K) → ℕ) → Polynomial K := fun n =>
    ∏ σ, (Polynomial.X - Polynomial.C (σ α)) ^ n σ
  have hP : ∀ n x, (P n).eval x = ∏ σ, (x - σ α) ^ n σ := fun n x => by
    simp [P, Polynomial.eval_prod]
  -- The two polynomials agree on the infinite set `k \ {α}`.
  have hPef : P e = P f := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : (Set.range (algebraMap k K) \ {α}).Infinite :=
      (Set.infinite_range_of_injective (algebraMap k K).injective).sdiff (Set.finite_singleton α)
    refine hinf.mono ?_
    rintro _ ⟨⟨c, rfl⟩, hc⟩
    have hs : algebraMap k K c - α ≠ 0 := sub_ne_zero.mpr hc
    have h1 := h (Units.mk0 _ hs)
    simp only [hd, zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      mul_inv_eq_one] at h1
    have h2 := congrArg (fun x : Kˣ => (x : K)) h1
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val, coe_gal, Units.val_mk0, map_sub,
      AlgEquiv.commutes] at h2
    simpa [hP] using h2
  -- Evaluating at a conjugate of `α` compares exponents.
  have key : ∀ (a b : (K ≃ₐ[k] K) → ℕ), P a = P b → ∀ σ₀, b σ₀ = 0 → a σ₀ = 0 := by
    intro a b hab σ₀ hb
    by_contra ha
    have h0 : (P a).eval (σ₀ α) = 0 := by
      rw [hP]
      exact Finset.prod_eq_zero (Finset.mem_univ σ₀) (by simp [zero_pow ha])
    have h1 : (P b).eval (σ₀ α) ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro σ _
      by_cases hσ : σ = σ₀
      · subst hσ; simp [hb]
      · exact pow_ne_zero _ (sub_ne_zero.mpr fun h' => hσ (hinj h'.symm))
    exact h1 (hab ▸ h0)
  funext σ
  have hef : e σ = 0 ∨ f σ = 0 := by
    rcases le_or_gt 0 (d σ) with h0 | h0
    · right; simp [f, h0]
    · left; simp [e, h0.le]
  rcases hef with h0 | h0
  · rw [hd, h0, key f e hPef.symm σ h0]; rfl
  · rw [hd, h0, key e f hPef σ h0]; rfl

variable {I : Type*}

/-- Conjugating a family of units by all Galois automorphisms. -/
def conjFamily (t : I → Kˣ) : (K ≃ₐ[k] K) × I → Kˣ := fun p => gal p.1 (t p.2)

/-- The character `t ↦ ∏_{σ, i} σ (t i) ^ m (σ, i)` of the torus of families of units. -/
def galChar (m : (K ≃ₐ[k] K) × I →₀ ℤ) : (I → Kˣ) →* Kˣ where
  toFun t := evalMonoid (conjFamily t) (.ofAdd m)
  map_one' := by
    have : conjFamily (k := k) (1 : I → Kˣ) = 1 := funext fun p => map_one (gal p.1)
    rw [this, evalMonoid_one]
  map_mul' t t' := by
    have : conjFamily (k := k) (t * t') = conjFamily t * conjFamily t' :=
      funext fun p => map_mul (gal p.1) _ _
    rw [this, evalMonoid_mul]

theorem galChar_mulSingle [Fintype I] [DecidableEq I] (m : (K ≃ₐ[k] K) × I →₀ ℤ) (i₀ : I)
    (s : Kˣ) : galChar m (Pi.mulSingle i₀ s) = ∏ σ, gal σ s ^ m (σ, i₀) := by
  change evalMonoid (conjFamily _) (.ofAdd m) = _
  rw [evalMonoid_eq_prod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [Fintype.prod_eq_single i₀]
  · simp [conjFamily]
  · intro i hi
    simp [conjFamily, Pi.mulSingle_eq_of_ne hi]

/-- Distinct exponents give distinct Galois characters. -/
theorem galChar_injective [Infinite k] [Algebra.IsSeparable k K] [Finite I] :
    Function.Injective (galChar (k := k) (K := K) (I := I)) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  intro m m' hmm'
  ext ⟨σ₀, i₀⟩
  have hd := exponents_eq_zero (k := k) (K := K) (fun σ => m (σ, i₀) - m' (σ, i₀)) fun s => by
    have h := congrArg (fun χ : (I → Kˣ) →* Kˣ => χ (Pi.mulSingle i₀ s)) hmm'
    simp only [galChar_mulSingle] at h
    simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [h, mul_inv_cancel]
  have := congrFun hd σ₀
  simpa [sub_eq_zero] using this

/-- **Density of Galois points.** A nonzero Laurent polynomial in the variables `t_{(σ, i)}`
does not vanish at all points `t_{(σ, i)} = σ (s_i)` with `s : I → Kˣ`. -/
theorem exists_lev_conjFamily_ne_zero [Infinite k] [Algebra.IsSeparable k K] [Finite I]
    {H : AddMonoidAlgebra K ((K ≃ₐ[k] K) × I →₀ ℤ)} (hH : H ≠ 0) :
    ∃ t : I → Kˣ, lev K (conjFamily t) H ≠ 0 := by
  by_contra hall
  push Not at hall
  let χ : ((K ≃ₐ[k] K) × I →₀ ℤ) → (I → Kˣ) →* K := fun m =>
    (Units.coeHom K).comp (galChar m)
  have hχ : Function.Injective χ := fun m m' h =>
    galChar_injective (k := k) (K := K) (I := I) <| MonoidHom.ext fun t =>
      Units.ext (DFunLike.congr_fun h t)
  have hli := (linearIndependent_monoidHom (I → Kˣ) K).comp χ hχ
  apply hH
  have h0 : Finsupp.linearCombination K (fun m => ((χ m : (I → Kˣ) →* K) : (I → Kˣ) → K))
      H.coeff = 0 := by
    funext t
    have ht := hall t
    rw [lev_coeff_sum, Finsupp.sum] at ht
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      Pi.zero_apply]
    exact ht
  have := linearIndependent_iff.mp hli H.coeff h0
  exact coeff_injective (by simpa using this)

/-! ### Norm-shaped points -/

/-- Apply `σ` to the coefficients and rename `t_i` to `t_{(σ, i)}`. -/
def twist (σ : K ≃ₐ[k] K) :
    AddMonoidAlgebra K (I →₀ ℤ) →+* AddMonoidAlgebra K ((K ≃ₐ[k] K) × I →₀ ℤ) :=
  (mapDomainRingHom K (Finsupp.mapDomain.addMonoidHom fun i : I => (σ, i))).comp
    (mapRingHom (I →₀ ℤ) (σ : K →+* K))

omit [FiniteDimensional k K] in
theorem twist_single (σ : K ≃ₐ[k] K) (m : I →₀ ℤ) (r : K) :
    twist σ (single m r) = single (Finsupp.mapDomain (fun i : I => (σ, i)) m) (σ r) := by
  simp [twist]

omit [FiniteDimensional k K] in
theorem lev_twist_single {B : Type*} [CommRing B] [Algebra K B]
    (s : (K ≃ₐ[k] K) × I → Bˣ) (σ : K ≃ₐ[k] K) (m : I →₀ ℤ) (r : K) :
    lev K s (twist σ (single m r)) =
      algebraMap K B (σ r) * (evalMonoid (fun i => s (σ, i)) (.ofAdd m) : B) := by
  rw [twist_single, lev_single, evalMonoid_mapDomain, Algebra.smul_def]

omit [FiniteDimensional k K] in
/-- Evaluating a twisted polynomial at conjugated units conjugates the evaluation. -/
theorem lev_conjFamily_twist (t : I → Kˣ) (σ : K ≃ₐ[k] K) (x : AddMonoidAlgebra K (I →₀ ℤ)) :
    lev K (conjFamily t) (twist σ x) = σ (lev K t x) := by
  have h : (lev K (conjFamily t)).toRingHom.comp (twist σ) =
      (σ : K →+* K).comp (lev K t).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      show lev K (conjFamily t) (twist σ (single 0 r)) = σ (lev K t (single 0 r))
      rw [lev_twist_single, lev_single]
      simp
    · intro m
      show lev K (conjFamily t) (twist σ (single m 1)) = σ (lev K t (single m 1))
      rw [lev_twist_single, lev_single]
      simp only [map_one, one_mul, one_smul]
      exact congrArg Units.val (evalMonoid_map (σ : K →+* K) t (.ofAdd m)).symm
  exact RingHom.congr_fun h x

/-- The norm-shaped family `i ↦ ∏_σ σ (y_{σ, i}(t))`. -/
def normFamily (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ) (t : I → Kˣ) :
    I → Kˣ :=
  fun i => ∏ σ, gal σ (Units.map (lev K t : AddMonoidAlgebra K (I →₀ ℤ) →* K) (u σ i))

/-- The universal norm-shaped substitution `t_i ↦ ∏_σ twist_σ (y_{σ, i})`. -/
def normSubst (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ) :
    AddMonoidAlgebra K (I →₀ ℤ) →ₐ[K] AddMonoidAlgebra K ((K ≃ₐ[k] K) × I →₀ ℤ) :=
  lev K fun i => ∏ σ, Units.map (twist σ).toMonoidHom (u σ i)

theorem normSubst_coord (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ) (i : I) :
    normSubst u (coord K i) = ∏ σ, twist σ (u σ i : AddMonoidAlgebra K (I →₀ ℤ)) := by
  rw [normSubst, lev_coord, Units.coe_prod]
  rfl

theorem lev_conjFamily_comp_normSubst
    (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ) (t : I → Kˣ) :
    (lev K (conjFamily t)).comp (normSubst u) = lev K (normFamily u t) := by
  apply algHom_ext_coord K
  intro i
  rw [AlgHom.comp_apply, normSubst_coord, lev_coord, normFamily, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  exact lev_conjFamily_twist t σ _

variable [DecidableEq (K ≃ₐ[k] K)]

/-- The collapse `t_{(1, i)} ↦ t_i`, `t_{(σ, i)} ↦ 1` for `σ ≠ 1`. -/
def collapse :
    AddMonoidAlgebra K ((K ≃ₐ[k] K) × I →₀ ℤ) →ₐ[K] AddMonoidAlgebra K (I →₀ ℤ) :=
  lev K fun p => if p.1 = 1 then coord K p.2 else 1

omit [FiniteDimensional k K] in
theorem collapse_twist_one (x : AddMonoidAlgebra K (I →₀ ℤ)) :
    collapse (twist (1 : K ≃ₐ[k] K) x) = x := by
  have h : (collapse (k := k) (K := K) (I := I)).toRingHom.comp (twist 1) =
      RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      show collapse (twist 1 (single 0 r)) = single 0 r
      rw [collapse, lev_twist_single]
      simp [AddMonoidAlgebra.coe_algebraMap]
    · intro m
      show collapse (twist 1 (single m 1)) = single m 1
      rw [collapse, lev_twist_single]
      simp only [map_one, one_mul, ite_true]
      rw [evalMonoid_coord]
      rfl
  exact RingHom.congr_fun h x

omit [FiniteDimensional k K] in
theorem collapse_twist_of_ne_one {σ : K ≃ₐ[k] K} (hσ : σ ≠ 1)
    (x : AddMonoidAlgebra K (I →₀ ℤ)) :
    collapse (twist σ x) = algebraMap K _ (σ (lev K (1 : I → Kˣ) x)) := by
  have h : (collapse (k := k) (K := K) (I := I)).toRingHom.comp (twist σ) =
      (algebraMap K _).comp ((σ : K →+* K).comp (lev K (1 : I → Kˣ)).toRingHom) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      show collapse (twist σ (single 0 r)) =
        algebraMap K _ (σ (lev K (1 : I → Kˣ) (single 0 r)))
      rw [collapse, lev_twist_single, lev_single]
      simp
    · intro m
      show collapse (twist σ (single m 1)) =
        algebraMap K _ (σ (lev K (1 : I → Kˣ) (single m 1)))
      rw [collapse, lev_twist_single, lev_single]
      simp only [hσ, ite_false, evalMonoid_const_one, evalMonoid_one]
      simp
  exact RingHom.congr_fun h x

/-- The rescaling `t_i ↦ c_i t_i`. -/
def rescale (c : I → Kˣ) : AddMonoidAlgebra K (I →₀ ℤ) →ₐ[K] AddMonoidAlgebra K (I →₀ ℤ) :=
  lev K fun i =>
    coord K i * Units.map (algebraMap K (AddMonoidAlgebra K (I →₀ ℤ))).toMonoidHom (c i)

theorem rescale_coord (c : I → Kˣ) (i : I) :
    rescale c (coord K i) = (coord K i : AddMonoidAlgebra K (I →₀ ℤ)) * algebraMap K _ (c i) := by
  rw [rescale, lev_coord, Units.val_mul]
  rfl

theorem rescale_injective (c : I → Kˣ) : Function.Injective (rescale c) := by
  have h : (rescale c⁻¹).comp (rescale c) = AlgHom.id K _ := by
    apply algHom_ext_coord K
    intro i
    rw [AlgHom.comp_apply, rescale_coord, map_mul, rescale_coord, AlgHom.commutes,
      AlgHom.id_apply, mul_assoc, ← map_mul, Pi.inv_apply, Units.inv_mul, map_one, mul_one]
  intro x y hxy
  have := congrArg (rescale c⁻¹) hxy
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, h, AlgHom.id_apply, AlgHom.id_apply] at this

theorem normSubst_injective (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ)
    (hu : ∀ i, u 1 i = coord K i) : Function.Injective (normSubst u) := by
  let c : I → Kˣ := fun i => ∏ σ ∈ Finset.univ.erase 1,
    gal σ (Units.map (lev K (1 : I → Kˣ) : AddMonoidAlgebra K (I →₀ ℤ) →* K) (u σ i))
  have h : collapse.comp (normSubst u) = rescale c := by
    apply algHom_ext_coord K
    intro i
    rw [AlgHom.comp_apply, normSubst_coord, map_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ 1), hu, collapse_twist_one, rescale_coord]
    congr 1
    simp only [c, Units.coe_prod, map_prod, coe_gal, Units.coe_map, MonoidHom.coe_coe]
    refine Finset.prod_congr rfl fun σ hσ => ?_
    exact collapse_twist_of_ne_one (Finset.ne_of_mem_erase hσ) _
  intro x y hxy
  apply rescale_injective c
  rw [← h, AlgHom.comp_apply, AlgHom.comp_apply, hxy]

/-- **Norm-shaped points are dense.** Let `u σ i` be units of the Laurent algebra with
`u 1 i = t_i`. A nonzero Laurent polynomial does not vanish at all norm-shaped points. -/
theorem exists_lev_normFamily_ne_zero [Infinite k] [Algebra.IsSeparable k K] [Finite I]
    (u : (K ≃ₐ[k] K) → I → (AddMonoidAlgebra K (I →₀ ℤ))ˣ) (hu : ∀ i, u 1 i = coord K i)
    {F : AddMonoidAlgebra K (I →₀ ℤ)} (hF : F ≠ 0) :
    ∃ t : I → Kˣ, lev K (normFamily u t) F ≠ 0 := by
  have hΦ : normSubst u F ≠ 0 := fun h0 =>
    hF (normSubst_injective u hu (h0.trans (map_zero _).symm))
  obtain ⟨t, ht⟩ := exists_lev_conjFamily_ne_zero (k := k) hΦ
  refine ⟨t, ?_⟩
  rw [← lev_conjFamily_comp_normSubst u t]
  exact ht

end Galois

end Langlands.GroupScheme.TorusDensity
