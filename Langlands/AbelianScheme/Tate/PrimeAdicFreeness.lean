import Langlands.AbelianScheme.Tate.PrimeAdic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Freeness of the prime-adic Tate module from free torsion levels -/

set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X] {T : Over S}
  {p : ℕ} [Fact p.Prime] {r : ℕ}

/-- A family of `r` points of the level `p ^ n` is a residue basis when its
coordinate map from `(ZMod (p ^ n)) ^ r` is bijective. -/
def IsLevelBasis (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S) (p n : ℕ)
    {r : ℕ} (b : Fin r → Level G T (p ^ n)) : Prop :=
  Function.Bijective (fun c : Fin r → ZMod (p ^ n) => ∑ i, c i • b i)

/-- The cardinality hypothesis makes every prime-power level finite. -/
lemma level_finite (hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r) (n : ℕ) :
    Finite (Level G T (p ^ n)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- If every level `p ^ n` has `(p ^ n) ^ r` points, the successive transition
`x ↦ p • x` from level `p ^ (n + 1)` to level `p ^ n` is surjective: its kernel
consists of sections killed by `p`, so it embeds into the level `p`. -/
lemma transition_succ_surjective
    (hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r) (n : ℕ) :
    Function.Surjective (transition G T (pow_dvd_pow p (Nat.le_succ n))) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have := level_finite hcard n
  have := level_finite hcard (n + 1)
  set t := transition G T (pow_dvd_pow p (Nat.le_succ n)) with ht
  have hdiv : p ^ (n + 1) / p ^ n = p := by
    rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp n)]
  have hmem : ∀ x : t.ker, (Additive.toMul x.1).val ∈ levelGroup G T (p ^ 1) := by
    intro x
    have hx : t x.1 = 0 := x.2
    have h : (Additive.toMul (t x.1)).val = (Additive.toMul x.1).val ^ p := by
      change (Additive.toMul x.1).val ^ (p ^ (n + 1) / p ^ n) = _
      rw [hdiv]
    rw [hx] at h
    rw [mem_levelGroup, pow_one, ← h]
    rfl
  have hinj : Function.Injective
      (fun x : t.ker => (Additive.ofMul ⟨(Additive.toMul x.1).val, hmem x⟩ :
        Level G T (p ^ 1))) := by
    intro x y hxy
    have h := congrArg (fun z : Level G T (p ^ 1) => (Additive.toMul z).val) hxy
    exact Subtype.ext (toSection_injective G T _ (congrArg Additive.ofMul h))
  have := level_finite hcard 1
  have hker : Nat.card t.ker ≤ p ^ r := by
    calc Nat.card t.ker ≤ Nat.card (Level G T (p ^ 1)) := Nat.card_le_card_of_injective _ hinj
      _ = p ^ r := by rw [hcard, pow_one]
  have hmul := t.ker.card_mul_index
  rw [AddSubgroup.index_ker, hcard] at hmul
  have hrange : (p ^ n) ^ r ≤ Nat.card t.range := by
    have h1 : (p ^ (n + 1)) ^ r = p ^ r * (p ^ n) ^ r := by ring
    have h2 : p ^ r * (p ^ n) ^ r ≤ p ^ r * Nat.card t.range := by
      rw [← h1, ← hmul]
      exact Nat.mul_le_mul_right _ hker
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos hp r)
  have htop : t.range = ⊤ :=
    AddSubgroup.eq_top_of_le_card _ (by rw [hcard]; exact hrange)
  exact AddMonoidHom.range_eq_top.mp htop

/-- The successive transition carries a residue basis to a residue basis. -/
lemma isLevelBasis_transition
    (hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r) (n : ℕ)
    {b : Fin r → Level G T (p ^ (n + 1))} (hb : IsLevelBasis G T p (n + 1) b) :
    IsLevelBasis G T p n (fun i => transition G T (pow_dvd_pow p (Nat.le_succ n)) (b i)) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine Function.Surjective.bijective_of_nat_card_le ?_ ?_
  · intro y
    obtain ⟨x, rfl⟩ := transition_succ_surjective hcard n y
    obtain ⟨c, rfl⟩ := hb.2 x
    refine ⟨fun i => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (c i), ?_⟩
    simp only [map_sum, transition_zmod_smul]
  · rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

omit [Fact p.Prime] in
/-- A free residue module of rank `r` at a level has a residue basis. -/
lemma exists_isLevelBasis (n : ℕ)
    (e : (Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n)) :
    IsLevelBasis G T p n (fun i => e (Pi.single i 1)) := by
  have h : (fun c : Fin r → ZMod (p ^ n) => ∑ i, c i • e (Pi.single i 1)) = e := by
    funext c
    simp_rw [← LinearEquiv.map_smul, ← map_sum]
    congr 1
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  unfold IsLevelBasis
  rw [h]
  exact e.bijective

/-- Kőnig's lemma for the finite nonempty sets of residue bases gives a basis
at every level, compatible with the actual transitions. -/
lemma exists_compatible_isLevelBasis
    (hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r)
    (hfree : ∀ n, Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n))) :
    ∃ b : ∀ n, Fin r → Level G T (p ^ n), (∀ n, IsLevelBasis G T p n (b n)) ∧
      ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (b (n + 1) i) = b n i := by
  let X : ℕ → Type u := fun n => {b : Fin r → Level G T (p ^ n) // IsLevelBasis G T p n b}
  let f : ∀ n, X (n + 1) ⟶ X n := fun n => TypeCat.ofHom (fun b =>
    ⟨fun i => transition G T (pow_dvd_pow p (Nat.le_succ n)) (b.1 i),
      isLevelBasis_transition hcard n b.2⟩)
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence f
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    have := level_finite hcard j.unop
    change Finite (X j.unop)
    exact Subtype.finite
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    obtain ⟨e⟩ := hfree j.unop
    exact ⟨(⟨fun i => e (Pi.single i 1), exists_isLevelBasis j.unop e⟩ : X j.unop)⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => (u (Opposite.op n)).2, fun n i => ?_⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg (fun b : X n => b.1 i) h

/-- Compatible residue bases give an equivalence of `ℤ_[p] ^ r` with the actual
prime-adic Tate module. -/
def linearEquivOfCompatibleBases (b : ∀ n, Fin r → Level G T (p ^ n))
    (hb : ∀ n, IsLevelBasis G T p n (b n))
    (hcomp : ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (b (n + 1) i) = b n i) :
    (Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p := by
  let f : ∀ n, (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] Level G T (p ^ n) :=
    fun n => Fintype.linearCombination ℤ_[p] (b n)
  have hf : ∀ n c, transition G T (pow_dvd_pow p (Nat.le_succ n)) (f (n + 1) c) = f n c := by
    intro n c
    simp only [f, Fintype.linearCombination_apply, map_sum,
      transition_smul G T p (Nat.le_succ n), hcomp]
  have hfz : ∀ n (c : Fin r → ℤ_[p]),
      f n c = ∑ i, PadicInt.toZModPow n (c i) • b n i := fun _ _ => rfl
  let φ := lift G T p f hf
  refine LinearEquiv.ofBijective φ ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext i
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    have h0 : f n c = 0 := by
      rw [← evaluation_lift G T p f hf n c]
      exact (congrArg (evaluation G T p n) hc).trans (map_zero _)
    have h1 := (hb n).1 (a₁ := fun i => PadicInt.toZModPow n (c i)) (a₂ := 0)
      (by simpa [hfz] using h0)
    simpa using congrFun h1 i
  · intro y
    let e : ∀ n, (Fin r → ZMod (p ^ n)) ≃ Level G T (p ^ n) :=
      fun n => Equiv.ofBijective _ (hb n)
    let c : ∀ n, Fin r → ZMod (p ^ n) := fun n => (e n).symm (evaluation G T p n y)
    have hc : ∀ n, ∑ i, c n i • b n i = evaluation G T p n y :=
      fun n => (e n).apply_symm_apply _
    have hsucc : ∀ n i, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
        (c (n + 1) i) = c n i := by
      intro n
      have h := (hb n).1 (a₁ := fun i => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n))
        (ZMod (p ^ n)) (c (n + 1) i)) (a₂ := c n) (by
          change ∑ i, _ • b n i = ∑ i, c n i • b n i
          rw [hc n, ← evaluation_transition G T p n y, ← hc (n + 1)]
          simp only [map_sum, transition_zmod_smul, hcomp])
      exact congrFun h
    have hcompat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) i,
        ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁)) (c k₂ i) = c k₁ i := by
      intro k₁ k₂ hk i
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
      induction d with
      | zero => exact ZMod.cast_id _ _
      | succ d ih =>
        rw [← ih (Nat.le_add_right _ _), ← hsucc (k₁ + d) i]
        exact (RingHom.congr_fun (Subsingleton.elim
          ((ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k₁ d)) (ZMod (p ^ k₁))).comp
            (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (k₁ + d))) (ZMod (p ^ (k₁ + d)))))
          (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁)))) _).symm
    let g : ∀ i k, Polynomial ℤ →+* ZMod (p ^ k) :=
      fun i k => Polynomial.eval₂RingHom (Int.castRingHom _) (c k i)
    have hg : ∀ i (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
        (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (g i k₂) = g i k₁ := by
      intro i k₁ k₂ hk
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp [g]
      · simp [g, hcompat k₁ k₂ hk i]
    let x : Fin r → ℤ_[p] := fun i => PadicInt.lift (hg i) Polynomial.X
    have hx : ∀ n i, PadicInt.toZModPow n (x i) = c n i := by
      intro n i
      have h := RingHom.congr_fun (PadicInt.lift_spec (hg i) n) Polynomial.X
      simpa [g] using h
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext n
    change f n x = evaluation G T p n y
    rw [hfz]
    simp only [hx]
    exact hc n

/-- If every prime-power level is a free residue module of rank `r`, with the
corresponding cardinality, then the actual integral prime-adic Tate module is
free of rank `r`. -/
theorem integral_linearEquiv_of_level
    (hcard : ∀ n, Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r)
    (hfree : ∀ n, Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n))) :
    Nonempty ((Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p) := by
  obtain ⟨b, hb, hcomp⟩ := exists_compatible_isLevelBasis hcard hfree
  exact ⟨linearEquivOfCompatibleBases b hb hcomp⟩

/-- A free integral Tate module of rank `r` has rational Tate module of
dimension `r`. -/
theorem rational_finrank_of_linearEquiv
    (e : (Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p) :
    FiniteDimensional ℚ_[p] (Rational G T p) ∧
      Module.finrank ℚ_[p] (Rational G T p) = r := by
  have : Module.Free ℤ_[p] (Integral G T p) := Module.Free.of_equiv e
  have : Module.Finite ℤ_[p] (Integral G T p) := Module.Finite.equiv e
  change FiniteDimensional ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p) ∧
    Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p) = r
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange, ← e.finrank_eq, Module.finrank_fin_fun]

end Langlands.GroupScheme.Tate.PrimeAdic
