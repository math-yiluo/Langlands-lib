import Langlands.GroupScheme.SimplyConnected.FactorialExhaustion
import Langlands.GroupScheme.SimplyConnected.FactorialWeights
import Langlands.CommutativeAlgebra.ChartPrimeValuation

/-! # Assembly of the factoriality criterion for split simply connected groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell Langlands.AlgebraicGeometry.FunctionFieldChart
  Langlands.CommutativeAlgebra.ChartUniqueFactorization

/-! ### Helpers -/

/-- A nonzero prime contained in a prime of height one equals it. -/
theorem eq_of_le_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R] {p q : Ideal R}
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p ≠ ⊥) (hq : q.height = 1) : p = q := by
  by_contra hne
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hpq hne)
  have h0 : p.height ≠ 0 := fun h0 => hp (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  have h1 : 1 ≤ p.height := Order.one_le_iff_ne_zero.2 h0
  rw [hq] at h
  have h2 : (1 : ℕ∞) + 1 ≤ p.height + 1 := by gcongr
  exact absurd (h2.trans h) (by norm_num)

/-- In an affine scheme, specialization of points is inclusion of their primes. -/
theorem specializes_iff_primeIdealOf_le {X : Scheme.{u}} [IsAffine X] (x z : X) :
    x ⤳ z ↔ (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ ≤
      (isAffineOpen_top X).primeIdealOf ⟨z, trivial⟩ := by
  rw [PrimeSpectrum.le_iff_specializes]
  let e := (isAffineOpen_top X).isoSpec
  have hemb : Topology.IsInducing e.hom.base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isInducing
  let a : (⊤ : X.Opens) := ⟨x, trivial⟩
  let c : (⊤ : X.Opens) := ⟨z, trivial⟩
  have h1 : (a : X) ⤳ (c : X) ↔ a ⤳ c := Topology.IsInducing.subtypeVal.specializes_iff
  have h2 : e.hom.base a ⤳ e.hom.base c ↔ a ⤳ c := hemb.specializes_iff
  exact h1.trans h2.symm

/-- **Height one gives maximality.** In an integral affine scheme, let `y` be the point of a
height-one prime and let `V` be a nonempty set. Every closed irreducible set `T` that contains
`closure {y}` and is disjoint from `V` is contained in `closure {y}`. (This does not assume that
`closure {y}` is disjoint from `V`; when it is, `closure {y}` is a maximal member of the family of
closed irreducible sets disjoint from `V`.) -/
theorem subset_closure_of_height_eq_one {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (q : PrimeSpectrum Γ(X, ⊤)) (hq : q.asIdeal.height = 1) {V : Set X} (hVne : V.Nonempty)
    (T : Set X) (hT : IsIrreducible T) (hTc : IsClosed T)
    (hyT : closure {(isAffineOpen_top X).fromSpec q} ⊆ T) (hTV : Disjoint T V) :
    T ⊆ closure {(isAffineOpen_top X).fromSpec q} := by
  set y := (isAffineOpen_top X).fromSpec q with hy
  have hgen := hT.isGenericPoint_genericPoint_closure
  rw [hTc.closure_eq] at hgen
  set ξ := hT.genericPoint
  have hyT' : y ∈ T := hyT (subset_closure rfl)
  have hξy : ξ ⤳ y := hgen.specializes hyT'
  have hle := (specializes_iff_primeIdealOf_le ξ y).1 hξy
  rw [hy, primeIdealOf_fromSpec_top] at hle
  have hne : ((isAffineOpen_top X).primeIdealOf ⟨ξ, trivial⟩).asIdeal ≠ ⊥ := by
    intro hbot
    obtain ⟨z, hz⟩ := hVne
    have hξz : ξ ⤳ z := by
      rw [specializes_iff_primeIdealOf_le]
      change ((isAffineOpen_top X).primeIdealOf ⟨ξ, trivial⟩).asIdeal ≤ _
      rw [hbot]
      exact bot_le
    have hzT : z ∈ T := by
      rw [← hgen]
      exact hξz.mem_closed isClosed_closure (subset_closure rfl)
    exact Set.disjoint_left.1 hTV hzT hz
  have heq : (isAffineOpen_top X).primeIdealOf ⟨ξ, trivial⟩ = q :=
    PrimeSpectrum.ext (eq_of_le_of_height_eq_one hle hne hq)
  have hξeq : ξ = y := by
    rw [hy, ← heq]
    exact ((isAffineOpen_top X).fromSpec_primeIdealOf ⟨ξ, trivial⟩).symm
  rw [← hgen, hξeq]

instance isAffine_cellSpec (k : Type u) [Field k] (I : Type u) [Fintype I] (m n : ℕ) :
    IsAffine (cellSpec k I m n).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (CellRing k I m n))))

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G) {m n : ℕ} (neg : Fin m ≃ {α // ¬ D.b.IsPos α})
  (pos : Fin n ≃ {α // D.b.IsPos α})

instance uniqueFactorizationMonoid_cellSpec :
    UniqueFactorizationMonoid Γ((cellSpec k D.I m n).left, ⊤) :=
  MulEquiv.uniqueFactorizationMonoid
    (Scheme.ΓSpecIso (CommRingCat.of (CellRing k D.I m n))).symm.commRingCatIsoToRingEquiv.toMulEquiv
    inferInstance

theorem charSection_mul_neg (χ : D.I → ℤ) :
    D.charSection m n χ * D.charSection m n (-χ) = 1 := by
  rw [charSection, charSection, ← map_mul]
  have : (D.charUnit m n χ : CellRing k D.I m n) * (D.charUnit m n (-χ) : CellRing k D.I m n) = 1 := by
    rw [← Units.val_mul, charUnit, charUnit, ← Finset.prod_mul_distrib]
    simp
  rw [this, map_one]

theorem prime_boundarySection {a : D.J} (ha : a ∈ D.b.support) :
    Prime (D.boundarySection n neg ha) := by
  rw [boundarySection]
  exact (MulEquiv.prime_iff (Scheme.ΓSpecIso
    (CommRingCat.of (CellRing k D.I m n))).symm.commRingCatIsoToRingEquiv.toMulEquiv).2
    (prime_one_add_negVar k D.I m n _)

variable [IsIntegral G.X.left]

/-- A torus character on a chart is a unit of the chart subalgebra. -/
theorem toFunctionField_charSection_mem {φ : (cellSpec k D.I m n).left ⟶ G.X.left}
    [IsOpenImmersion φ] (χ : D.I → ℤ) :
    toFunctionField φ (D.charSection m n χ) ∈ sectionSubalgebra (φ ''ᵁ ⊤) ∧
      (toFunctionField φ (D.charSection m n χ))⁻¹ ∈ sectionSubalgebra (φ ''ᵁ ⊤) := by
  refine ⟨toFunctionField_mem φ _, ?_⟩
  have h : toFunctionField φ (D.charSection m n χ) * toFunctionField φ (D.charSection m n (-χ)) = 1 := by
    rw [← map_mul, charSection_mul_neg, map_one]
  rw [inv_eq_of_mul_eq_one_right h]
  exact toFunctionField_mem φ _

omit [IsIntegral G.X.left] in
/-- The locus of the translated chart where the boundary function is invertible lies in the big
cell. -/
theorem basicOpen_boundary_subset {a : D.J} (ha : a ∈ D.b.support) :
    (G.X.left.basicOpen (((D.tchart neg pos a).left.appIso ⊤).inv
      (D.boundarySection n neg ha)) : Set G.X.left) ⊆
      Set.range (D.chart neg pos).left.base := by
  obtain ⟨ψ, h1, -⟩ := D.exists_boundary_comparison neg pos ha
  intro x hx
  rw [← Scheme.image_basicOpen] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  let c' : PrimeSpectrum (CellRing k D.I m n) := c
  have hc' : c' ∈ PrimeSpectrum.basicOpen (D.boundaryRing n neg ha) := by
    have h := AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of (CellRing k D.I m n))
      (D.boundaryRing n neg ha)
    rw [boundarySection] at hc
    have hc2 : c ∈ (Spec (CommRingCat.of (CellRing k D.I m n))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (CellRing k D.I m n))).inv
          (D.boundaryRing n neg ha)) := hc
    rw [h] at hc2
    exact hc2
  have hc'' : c' ∈ Set.range
      (PrimeSpectrum.comap (algebraMap (CellRing k D.I m n) (D.BoundaryLoc n neg ha))) := by
    rw [PrimeSpectrum.localization_away_comap_range (D.BoundaryLoc n neg ha)
      (D.boundaryRing n neg ha)]
    exact hc'
  obtain ⟨w, hw⟩ := hc''
  refine ⟨ψ.left.base w, ?_⟩
  change (ψ ≫ D.chart neg pos).left.base w = _
  rw [h1]
  change (D.tchart neg pos a).left.base ((D.boundaryIncl n neg ha).left.base w) =
    (D.tchart neg pos a).left.base c
  congr 1

open Classical in
include neg pos in
/-- **Factoriality from coordinate split data and fundamental weights.** -/
theorem uniqueFactorizationMonoid_of_weights [IsAffine G.X.left] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] [IsNoetherianRing Γ(G.X.left, ⊤)]
    [IsIntegrallyClosed Γ(G.X.left, ⊤)] (ω : D.J → (D.I → ℤ))
    (hω : ∀ i ∈ D.b.support, ∀ j ∈ D.b.support,
      coPairing (ω i) (D.P.coroot j) = if j = i then 1 else 0) :
    UniqueFactorizationMonoid Γ(G.X.left, ⊤) := by
  classical
  -- the big cell
  set φ := (D.chart neg pos).left with hφ
  have hV : IsAffineOpen (φ ''ᵁ ⊤) := isAffineOpen_image_top φ
  set S := sectionSubalgebra (φ ''ᵁ ⊤) with hSdef
  have : UniqueFactorizationMonoid S :=
    MulEquiv.uniqueFactorizationMonoid (chartEquiv φ).toMulEquiv inferInstance
  have hS : IsChart S := isChart_sectionSubalgebra hV
  -- the boundary charts
  let ψ : D.b.support → ((cellSpec k D.I m n).left ⟶ G.X.left) :=
    fun a => (D.tchart neg pos a).left
  have hVa : ∀ a, IsAffineOpen (ψ a ''ᵁ ⊤) := fun a => isAffineOpen_image_top (ψ a)
  let Sa : D.b.support → Subalgebra Γ(G.X.left, ⊤) G.X.left.functionField :=
    fun a => sectionSubalgebra (ψ a ''ᵁ ⊤)
  have hSa : ∀ a, IsChart (Sa a) := fun a => isChart_sectionSubalgebra (hVa a)
  have : ∀ a, UniqueFactorizationMonoid (Sa a) := fun a =>
    MulEquiv.uniqueFactorizationMonoid (chartEquiv (ψ a)).toMulEquiv inferInstance
  let π : ∀ a, Sa a := fun a => chartEquiv (ψ a) (D.boundarySection n neg a.2)
  have hπ : ∀ a, Prime (π a) := fun a =>
    (MulEquiv.prime_iff (chartEquiv (ψ a)).toMulEquiv).2 (D.prime_boundarySection neg a.2)
  have hπ0 : ∀ a, (π a : G.X.left.functionField) ≠ 0 := fun a h0 =>
    (hπ a).ne_zero (Subtype.ext h0)
  have hQ : ∀ a, (Ideal.span {π a}).IsPrime := fun a =>
    (Ideal.span_singleton_prime (hπ a).ne_zero).2 (hπ a)
  let p : D.b.support → Ideal Γ(G.X.left, ⊤) :=
    fun a => (Ideal.span {π a}).comap (algebraMap _ (Sa a))
  have : ∀ a, (p a).IsPrime := fun a => Ideal.comap_isPrime _ _
  have hloc : ∀ a (x : G.X.left.functionField),
      x ∈ loc G.X.left.functionField (p a) ↔
        x ∈ chartLoc G.X.left.functionField (Sa a) (Ideal.span {π a}) :=
    fun a x => (hSa a (Ideal.span {π a}) x).symm
  have hmemS : ∀ a (x : G.X.left.functionField), x ∈ Sa a →
      x ∈ chartLoc G.X.left.functionField (Sa a) (Ideal.span {π a}) := fun a x hx =>
    mem_chartLoc.2 ⟨⟨x, hx⟩, 1, fun h => (hQ a).ne_top ((Ideal.eq_top_iff_one _).2 h),
      by simp⟩
  -- the torus characters
  let U : D.b.support → D.b.support → G.X.left.functionField :=
    fun a b => toFunctionField (ψ b) (D.charSection m n (ω a))
  have hU : ∀ a b, U a b ∈ Sa b ∧ (U a b)⁻¹ ∈ Sa b := fun a b =>
    D.toFunctionField_charSection_mem (φ := ψ b) (ω a)
  let f : D.b.support → G.X.left.functionField :=
    fun a => toFunctionField φ (D.charSection m n (ω a))
  have hid : ∀ a b, f a = U a b * (π b : G.X.left.functionField) ^
      coPairing (ω a) (D.P.coroot b) := fun a b =>
    D.toFunctionField_charSection neg pos b.2 (ω a)
  have hidd : ∀ a, f a = U a a * (π a : G.X.left.functionField) := fun a => by
    rw [hid a a, hω a a.2 a a.2, ite_eq_left rfl, zpow_one]
  have hido : ∀ a b, a ≠ b → f a = U a b := fun a b hab => by
    rw [hid a b, hω a a.2 b b.2, ite_eq_right (fun h => hab (Subtype.ext h.symm)), zpow_zero, mul_one]
  have hU0 : ∀ a b, U a b ≠ 0 := fun a b h0 => by
    have := (hU a b).2
    have h1 : U a b * (U a b)⁻¹ = 1 := by
      have hmul := D.charSection_mul_neg (m := m) (n := n) (ω a)
      have : toFunctionField (ψ b) (D.charSection m n (ω a)) *
          toFunctionField (ψ b) (D.charSection m n (-ω a)) = 1 := by
        rw [← map_mul, hmul, map_one]
      rw [inv_eq_of_mul_eq_one_right this]
      exact this
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  refine uniqueFactorizationMonoid_of_chart S hS f
    (fun a => (D.toFunctionField_charSection_mem (φ := φ) (ω a)).1)
    (fun a => (D.toFunctionField_charSection_mem (φ := φ) (ω a)).2) p
    (fun a => ?_) (fun a => ?_) (fun a x hx => ?_) (fun a b hab => ?_) ?_
  · -- `f a` is regular at `p a`
    rw [hloc, hidd]
    exact Subalgebra.mul_mem _ (hmemS a _ (hU a a).1) (hmemS a _ (π a).2)
  · -- `f a` vanishes at `p a`
    rw [hloc]
    intro h
    apply inv_notMem_chartLoc (Ideal.mem_span_singleton_self (π a)) (hπ0 a)
    have : (π a : G.X.left.functionField)⁻¹ = (f a)⁻¹ * U a a := by
      rw [hidd, mul_inv, mul_comm (U a a)⁻¹, mul_assoc, inv_mul_cancel₀ (hU0 a a), mul_one]
    rw [this]
    exact Subalgebra.mul_mem _ h (hmemS a _ (hU a a).1)
  · -- the valuation at `p a`
    obtain ⟨n₀, h1, h2⟩ := exists_zpow_mul_unit (S := Sa a) (hπ a) hx
    have hUz : ∀ z : ℤ, U a a ^ z ∈ chartLoc G.X.left.functionField (Sa a) (Ideal.span {π a}) :=
      fun z => zpow_mem _ (hmemS a _ (hU a a).1) (hmemS a _ (hU a a).2) z
    have key : x * f a ^ (-n₀) = x * (π a : G.X.left.functionField) ^ (-n₀) * U a a ^ (-n₀) := by
      rw [hidd, mul_zpow]
      ring
    refine ⟨n₀, ?_, ?_⟩
    · rw [hloc, key]
      exact Subalgebra.mul_mem _ h1 (hUz _)
    · rw [hloc, key, mul_inv, ← zpow_neg, neg_neg]
      exact Subalgebra.mul_mem _ h2 (hUz _)
  · -- the other characters are units at `p a`
    rw [hloc, hloc, hido b a (Ne.symm hab)]
    exact ⟨hmemS a _ (hU b a).1, hmemS a _ (hU b a).2⟩
  · -- exhaustion of the height-one primes
    intro q hq h1
    have hmemV : ∀ (ψ' : (cellSpec k D.I m n).left ⟶ G.X.left) [IsOpenImmersion ψ'] (x : G.X.left),
        x ∈ ψ' ''ᵁ ⊤ ↔ x ∈ Set.range ψ'.base := fun ψ' _ x =>
      ⟨fun ⟨z, _, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, trivial, hz⟩⟩
    set y := (isAffineOpen_top G.X.left).fromSpec ⟨q, hq⟩ with hy
    have hprime : ((isAffineOpen_top G.X.left).primeIdealOf ⟨y, trivial⟩).asIdeal = q := by
      rw [hy, primeIdealOf_fromSpec_top]
    by_cases hyV : y ∈ φ ''ᵁ ⊤
    · left
      obtain ⟨Q, hQp, hQq⟩ := exists_prime_comap_eq hV hyV
      exact ⟨Q, hQp, hQq.trans hprime⟩
    by_cases hya : ∃ a, y ∈ ψ a ''ᵁ ⊤
    · right
      obtain ⟨a, hya⟩ := hya
      refine ⟨a, ?_⟩
      let Q' : Ideal (Sa a) := ((hVa a).primeIdealOf ⟨y, hya⟩).asIdeal.comap
        ((sectionEquiv (ψ a ''ᵁ ⊤)).symm : Sa a →+* Γ(G.X.left, ψ a ''ᵁ ⊤))
      have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
      have hQ'q : Q'.comap (algebraMap _ (Sa a)) = q := by
        rw [← hprime, ← comap_primeIdealOf_res (hVa a) hya]
        ext c
        simp only [Ideal.mem_comap, Q']
        rw [algebraMap_sectionSubalgebra]
        simp
      have hπQ' : π a ∈ Q' := by
        have hπe : π a = sectionEquiv (ψ a ''ᵁ ⊤)
            (((ψ a).appIso ⊤).inv (D.boundarySection n neg a.2)) := rfl
        simp only [Q', Ideal.mem_comap]
        rw [hπe]
        change (sectionEquiv (ψ a ''ᵁ ⊤)).symm (sectionEquiv (ψ a ''ᵁ ⊤) _) ∈ _
        rw [RingEquiv.symm_apply_apply]
        apply mem_primeIdealOf_of_notMem_basicOpen (hVa a) hya
        intro hmem
        apply hyV
        exact (hmemV φ y).2 (D.basicOpen_boundary_subset neg pos a.2 hmem)
      have hle : Ideal.span {π a} ≤ Q' := (Ideal.span_singleton_le_iff_mem _).2 hπQ'
      have hQ'h : Q'.height = 1 := by rw [← height_comap_eq (hSa a) Q', hQ'q, h1]
      have hbot : Ideal.span {π a} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact (hπ a).ne_zero
      have heq : Ideal.span {π a} = Q' := eq_of_le_of_height_eq_one hle hbot hQ'h
      change q = (Ideal.span {π a}).comap (algebraMap _ (Sa a))
      rw [heq, hQ'q]
    · exfalso
      push Not at hya
      obtain ⟨v₀⟩ : Nonempty (cellSpec k D.I m n).left := inferInstance
      have hdisj : ∀ (ψ' : (cellSpec k D.I m n).left ⟶ G.X.left) [IsOpenImmersion ψ'],
          y ∉ ψ' ''ᵁ ⊤ → Disjoint (closure {y}) (Set.range ψ'.base) := by
        intro ψ' _ hyψ
        rw [Set.disjoint_left]
        intro z hz hzV
        have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
        exact hyψ ((hmemV ψ' y).2 (hyz.mem_open ψ'.isOpenEmbedding.isOpen_range hzV))
      exact D.false_of_maximal neg pos (Z := closure {y}) isIrreducible_singleton.closure
        (fun T hT hTc hyT hTV => subset_closure_of_height_eq_one ⟨q, hq⟩ h1
          (V := Set.range φ.base) ⟨φ.base v₀, v₀, rfl⟩ T hT hTc hyT hTV)
        (hdisj φ hyV) (fun a ha => hdisj (ψ ⟨a, ha⟩) (hya ⟨a, ha⟩))

end CellData

end Langlands.GroupScheme.SplitFactorial
