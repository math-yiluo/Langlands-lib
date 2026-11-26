import Langlands.Shimura.Unitary.HarrisCMCompositeSplitCenterStatement
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Global.Arithmetic.HarrisSplitPlaceNeConjPlaceProof

/-!
# Proof: the oriented split center of Harris's CM composite

Let `E` be a CM field with intermediate fields `E₀` and `K₀`, where `E₀` is totally
real, `K₀` is imaginary quadratic and `E₀ ⊔ K₀ = ⊤`; then the extension `E/E₀` is
quadratic. At a place `v` above a rational prime split in `K₀`, the place
`w` of `E₀` below `v` has exactly the two distinct places `v` and its CM
conjugate above it, each of local degree one. Evaluation at `v` and at the
conjugate place, in that order, identifies `(E₀)_w ⊗[E₀] E` with
`(E₀)_w × (E₀)_w`. Complex conjugation, transported to the completions, exchanges
the two coordinates.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Shimura.FiniteUnitary

open NumberField IsDedekindDomain _root_.Algebra Langlands.Global
  Langlands.Global.AdelicFunctoriality
open Langlands.GaloisRepresentation (residueCharacteristic)
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

section LocalDegree

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (p : HeightOneSpectrum (𝓞 K))

/-- In a quadratic extension, two distinct places above `p` exhaust the places above
`p`, and both have local degree one. -/
theorem placesAbove_eq_or_eq_of_finrank_eq_two (h2 : Module.finrank K L = 2)
    (a b : FinitePlacesAbove L p) (hab : a ≠ b) :
    (∀ q : FinitePlacesAbove L p, q = a ∨ q = b) ∧
      Module.finrank (p.adicCompletion K) (a.1.adicCompletion L) = 1 ∧
      Module.finrank (p.adicCompletion K) (b.1.adicCompletion L) = 1 := by
  classical
  let f : FinitePlacesAbove L p → ℕ := fun q =>
    Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)
  have hle : ∑ q, f q ≤ 2 := h2 ▸ finiteLocalDegree_sum_le p
  have hpos (q : FinitePlacesAbove L p) : 0 < f q := Module.finrank_pos
  have hpair : f a + f b ≤ 2 := by
    calc f a + f b = ∑ q ∈ {a, b}, f q := (Finset.sum_pair hab).symm
      _ ≤ ∑ q, f q := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 := hle
  have ha := hpos a
  have hb := hpos b
  refine ⟨fun q => ?_, by change f a = 1; omega, by change f b = 1; omega⟩
  by_contra hq
  push Not at hq
  have hq' := hpos q
  have htriple : f q + (f a + f b) ≤ 2 := by
    calc f q + (f a + f b) = ∑ x ∈ insert q {a, b}, f x := by
          rw [Finset.sum_insert (by simp [hq.1, hq.2]), Finset.sum_pair hab]
      _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 := hle
  omega

end LocalDegree

section CMField

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- Complex conjugation fixes every totally real subfield. -/
theorem complexConj_eq_self_of_isTotallyReal (E₀ : IntermediateField ℚ E) [IsTotallyReal E₀]
    {x : E} (hx : x ∈ E₀) : IsCMField.complexConj E x = x := by
  have : IsTotallyReal E₀.toSubfield := ‹IsTotallyReal E₀›
  exact (IsCMField.complexConj_eq_self_iff E x).mpr
    (IsTotallyReal.le_maximalRealSubfield E₀.toSubfield hx)

/-- A totally real subfield of a CM field together with a quadratic field generates
a quadratic extension of it. -/
theorem isQuadraticExtension_of_sup_eq_top (E₀ K₀ : IntermediateField ℚ E) [IsTotallyReal E₀]
    (hsup : E₀ ⊔ K₀ = ⊤) (hK₀ : Module.finrank ℚ K₀ = 2) : IsQuadraticExtension E₀ E := by
  refine ⟨?_⟩
  have htower := Module.finrank_mul_finrank ℚ E₀ E
  have hsupl := IntermediateField.finrank_sup_le E₀ K₀
  rw [hsup, IntermediateField.finrank_top', hK₀, ← htower] at hsupl
  have hE₀pos : 0 < Module.finrank ℚ E₀ := Module.finrank_pos
  have hle : Module.finrank E₀ E ≤ 2 := Nat.le_of_mul_le_mul_left hsupl hE₀pos
  have hpos : 0 < Module.finrank E₀ E := Module.finrank_pos
  have hne : Module.finrank E₀ E ≠ 1 := by
    intro h1
    rw [IntermediateField.finrank_eq_one_iff_eq_top] at h1
    apply IsCMField.complexConj_ne_one E
    ext x
    exact complexConj_eq_self_of_isTotallyReal E₀ (h1 ▸ IntermediateField.mem_top)
  omega

end CMField

section SplitCenter

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]
  (E₀ : IntermediateField ℚ E) [IsTotallyReal E₀]

/-- The CM conjugate of a place above a place of a totally real subfield lies above
the same place. -/
theorem conjPlace_liesOver_of_isTotallyReal (w : Langlands.Global.FinitePlace E₀)
    (v : Langlands.Global.FinitePlace E) [v.asIdeal.LiesOver w.asIdeal] :
    (Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal := by
  constructor
  ext x
  rw [Ideal.over_def v.asIdeal w.asIdeal]
  change algebraMap (𝓞 E₀) (𝓞 E) x ∈ v.asIdeal ↔
    RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
      (algebraMap (𝓞 E₀) (𝓞 E) x) ∈ v.asIdeal
  have heq : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
      (algebraMap (𝓞 E₀) (𝓞 E) x) = algebraMap (𝓞 E₀) (𝓞 E) x := by
    apply RingOfIntegers.ext
    exact complexConj_eq_self_of_isTotallyReal E₀ (x : E₀).2
  rw [heq]

omit [IsCMField E] [IsTotallyReal E₀] in
/-- The completed center map at a place above `w` is the corresponding coordinate of
the canonical completed tensor map. -/
theorem completedCenterMap_eq_finiteTensorMap_of_liesOver [IsTotallyReal E₀] [IsTotallyComplex E]
    [IsQuadraticExtension E₀ E] (w : Langlands.Global.FinitePlace E₀)
    (v : Langlands.Global.FinitePlace E) [v.asIdeal.LiesOver w.asIdeal]
    (z : LocalCenter E₀ E w) :
    completedCenterMap E₀ E w v z = finiteTensorMap (L := E) w z ⟨v, inferInstance⟩ := by
  induction z using TensorProduct.inductionOn with
  | tmul s k => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {E₀} in
/-- Complex conjugation transports the completion at the conjugate place to the
completion at `v`. -/
def conjCompletionEquiv (v : Langlands.Global.FinitePlace E) :
    FiniteCompletion E (Harris.conjPlace E v) ≃+* FiniteCompletion E v :=
  finiteCompletionEquiv (IsCMField.complexConj E).toRingEquiv v

theorem continuous_conjCompletionEquiv (v : Langlands.Global.FinitePlace E) :
    Continuous (conjCompletionEquiv v) :=
  continuous_finiteCompletionEquiv _ v

theorem conjCompletionEquiv_algebraMap (v : Langlands.Global.FinitePlace E) (k : E) :
    conjCompletionEquiv v (algebraMap E (FiniteCompletion E (Harris.conjPlace E v)) k) =
      algebraMap E (FiniteCompletion E v) (IsCMField.complexConj E k) :=
  finiteCompletionEquiv_coe _ v k

/-- On the base completion, conjugation transport intertwines the two completion maps. -/
theorem conjCompletionEquiv_completionMap (w : Langlands.Global.FinitePlace E₀)
    (v : Langlands.Global.FinitePlace E) [v.asIdeal.LiesOver w.asIdeal]
    [(Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal] (s : FiniteCompletion E₀ w) :
    conjCompletionEquiv v (FiniteExtension.completionMap w (Harris.conjPlace E v) s) =
      FiniteExtension.completionMap w v s := by
  have h := (HeightOneSpectrum.denseRange_algebraMap E₀ w).equalizer
    ((continuous_conjCompletionEquiv v).comp
      (FiniteExtension.continuous_completionMap w (Harris.conjPlace E v)))
    (FiniteExtension.continuous_completionMap w v) (by
      funext a
      change conjCompletionEquiv v (FiniteExtension.completionMap w (Harris.conjPlace E v)
        (algebraMap E₀ (FiniteCompletion E₀ w) a)) =
          FiniteExtension.completionMap w v (algebraMap E₀ (FiniteCompletion E₀ w) a)
      rw [FiniteExtension.completionMap_coe, FiniteExtension.completionMap_coe,
        conjCompletionEquiv_algebraMap,
        complexConj_eq_self_of_isTotallyReal E₀ (x := algebraMap E₀ E a) a.2])
  exact congrFun h s

variable [IsQuadraticExtension E₀ E]

/-- Conjugation carries the coordinate at the conjugate place to the coordinate at `v`
of the conjugated element. -/
theorem conjCompletionEquiv_completedCenterMap (w : Langlands.Global.FinitePlace E₀)
    (v : Langlands.Global.FinitePlace E) [v.asIdeal.LiesOver w.asIdeal]
    [(Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal] (z : LocalCenter E₀ E w) :
    conjCompletionEquiv v (completedCenterMap E₀ E w (Harris.conjPlace E v) z) =
      completedCenterMap E₀ E w v (localConjugation E₀ E w z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s k =>
    rw [completedCenterMap_tmul, localConjugation_tmul, completedCenterMap_tmul, map_mul,
      conjCompletionEquiv_completionMap, conjCompletionEquiv_algebraMap]
    rfl
  | add x y hx hy => simp [hx, hy]

/-- At a place `w` of `E₀` with two distinct CM-conjugate places `v` and `c(v)` above
it, these are all the places above `w`, both completions are identified with the
base completion, and the evaluations at `v` and `c(v)`, in that order, form a
split-center identification. -/
theorem exists_splitPlaceIdentification (w : Langlands.Global.FinitePlace E₀)
    (v : Langlands.Global.FinitePlace E) [h₁ : v.asIdeal.LiesOver w.asIdeal]
    [h₂ : (Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal]
    (hne : v ≠ Harris.conjPlace E v) :
    ∃ (C : SplitPlaceIdentification E₀ E w)
      (e₁ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w] FiniteCompletion E v)
      (e₂ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w]
        FiniteCompletion E (Harris.conjPlace E v)),
      (∀ q : Langlands.Global.FinitePlace E, q.asIdeal.LiesOver w.asIdeal →
        q = v ∨ q = Harris.conjPlace E v) ∧
      (∀ z, e₁ (C.equiv z).1 = completedCenterMap E₀ E w v z) ∧
      (∀ z, e₂ (C.equiv z).2 = completedCenterMap E₀ E w (Harris.conjPlace E v) z) := by
  let a : FinitePlacesAbove E w := ⟨v, h₁⟩
  let b : FinitePlacesAbove E w := ⟨Harris.conjPlace E v, h₂⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  obtain ⟨hall, hdeg₁, hdeg₂⟩ := placesAbove_eq_or_eq_of_finrank_eq_two w
    (IsQuadraticExtension.finrank_eq_two E₀ E) a b hab
  let e₁ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w] FiniteCompletion E v :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg₁)
  let e₂ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w]
      FiniteCompletion E (Harris.conjPlace E v) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg₂)
  let Φ : LocalCenter E₀ E w →ₐ[FiniteCompletion E₀ w]
      FiniteCompletion E₀ w × FiniteCompletion E₀ w :=
    AlgHom.prod ((e₁.symm : _ →ₐ[FiniteCompletion E₀ w] _).comp (completedCenterMap E₀ E w v))
      ((e₂.symm : _ →ₐ[FiniteCompletion E₀ w] _).comp
        (completedCenterMap E₀ E w (Harris.conjPlace E v)))
  have hΦ (z : LocalCenter E₀ E w) :
      Φ z = (e₁.symm (completedCenterMap E₀ E w v z),
        e₂.symm (completedCenterMap E₀ E w (Harris.conjPlace E v) z)) := rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [hΦ, Prod.mk_eq_zero, map_eq_zero_iff _ e₁.symm.injective,
      map_eq_zero_iff _ e₂.symm.injective] at hz
    have h0 : finiteTensorMap (L := E) w z = 0 := by
      funext q
      rcases hall q with rfl | rfl
      · exact (completedCenterMap_eq_finiteTensorMap_of_liesOver E₀ w v z).symm.trans hz.1
      · exact (completedCenterMap_eq_finiteTensorMap_of_liesOver E₀ w (Harris.conjPlace E v) z).symm.trans
          hz.2
    exact ((completedTensorComparison.{u, u} E₀ E).1 w).1 (h0.trans (map_zero _).symm)
  have hfinrank : Module.finrank (FiniteCompletion E₀ w) (LocalCenter E₀ E w) =
      Module.finrank (FiniteCompletion E₀ w) (FiniteCompletion E₀ w × FiniteCompletion E₀ w) := by
    rw [Module.finrank_baseChange, IsQuadraticExtension.finrank_eq_two E₀ E,
      Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective Φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank
      (f := Φ.toLinearMap)).mp hinj⟩
  have hswap (y : FiniteCompletion E (Harris.conjPlace E v)) :
      e₁.symm (conjCompletionEquiv v y) = e₂.symm y := by
    obtain ⟨t, rfl⟩ := e₂.surjective y
    rw [e₂.symm_apply_apply, AlgEquiv.symm_apply_eq]
    exact conjCompletionEquiv_completionMap E₀ w v t
  let C : SplitPlaceIdentification E₀ E w :=
    { equiv := AlgEquiv.ofBijective Φ hbij
      conjugation_eq := fun z => by
        change Φ (localConjugation E₀ E w z) = Prod.swap (Φ z)
        rw [hΦ, hΦ, Prod.swap_prod_mk, ← conjCompletionEquiv_completedCenterMap, hswap]
        congr 1
        conv_rhs => rw [← (localConjugation E₀ E w).apply_apply z]
        rw [← conjCompletionEquiv_completedCenterMap E₀ w v (localConjugation E₀ E w z), hswap] }
  refine ⟨C, e₁, e₂, fun q hq => ?_, fun z => e₁.apply_symm_apply _,
    fun z => e₂.apply_symm_apply _⟩
  rcases hall ⟨q, hq⟩ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end SplitCenter

/-- The split-center statement follows from distinctness of a place above a split
imaginary-quadratic prime and its CM conjugate. -/
theorem harrisCMCompositeSplitCenter_of_splitPlaceNeConjPlace
    (hne : Harris.SplitPlaceNeConjPlaceStatement.{u}) :
    HarrisCMCompositeSplitCenterStatement.{u} := by
  intro E _ _ _ E₀ K₀ _ hsup v hsplit
  have hquad := isQuadraticExtension_of_sup_eq_top E₀ K₀ hsup hsplit.1
  refine ⟨hquad, ?_⟩
  intro w
  have h₁ : v.asIdeal.LiesOver w.asIdeal := ⟨rfl⟩
  have h₂ : (Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal :=
    conjPlace_liesOver_of_isTotallyReal E₀ w v
  have : Fact (residueCharacteristic v).Prime := ⟨CharP.prime_ringChar (𝓞 E ⧸ v.asIdeal)⟩
  have hmem : ((residueCharacteristic v : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 E ⧸ v.asIdeal) (residueCharacteristic v)
  have hvne := hne (residueCharacteristic v) E K₀ v hsplit hmem
  obtain ⟨C, e₁, e₂, hall, hC₁, hC₂⟩ := exists_splitPlaceIdentification E₀ w v hvne
  exact ⟨h₁, h₂, C, e₁, e₂, hvne, hall, hC₁, hC₂⟩

/-- The oriented split center of Harris's CM composite. -/
theorem harrisCMCompositeSplitCenter : HarrisCMCompositeSplitCenterStatement.{u} :=
  harrisCMCompositeSplitCenter_of_splitPlaceNeConjPlace Harris.splitPlaceNeConjPlace

end Langlands.Shimura.FiniteUnitary
