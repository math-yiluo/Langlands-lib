/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicPairingLimit
public import WeilConjectures.Algebra.Module.RationalPerfectPairing

/-!
# Transport of finite-level duality to an extension of `ℚ_p`

This file proves the linear algebra of the transport of Poincaré duality from the finite
coefficient rings `ℤ/ℓᵐ` to `ℚ̄_ℓ` (blueprint `theorem-poincare-duality--9`,
`theorem-poincare-duality--6`), in the following abstract form
(`LinearMap.exists_isPerfPair_of_finiteLevel`).

Let `A`, `B` be finitely generated `ℤ_p`-modules (the integral cohomology groups `Hⁱ(X, ℤ_ℓ)`,
`H^{2d-i}(X, ℤ_ℓ)`) with endomorphisms `F_A`, `F_B` (Frobenius), and let `V`, `W` be their
extensions of scalars to a field `K ⊇ ℤ_p` (e.g. `ℚ̄_ℓ`), with the induced endomorphisms. Suppose
that for every `m`:

* there are maps `ρ : A ⟶ Eₘ`, `σ : B ⟶ Fₘ` to modules (the cohomology groups with coefficients
  `ℤ/ℓᵐ`) whose kernels are `pᵐ A`, `pᵐ B` and whose images contain `pᵉ Eₘ`, `pᵉ Fₘ` for a fixed
  `e` (the Bockstein sequences, when `pᵉ` kills the torsion of the cohomology);
* there is a pairing `Qₘ : Eₘ × Fₘ ⟶ ℤ_p / pᵐ`, nondegenerate on both sides (finite-level
  Poincaré duality), whose restriction along `ρ`, `σ` is a `c`-similitude for `F_A`, `F_B`.

The finite-level pairings need not be compatible with each other. Then there is a perfect
`K`-bilinear pairing `V × W ⟶ K` which is a `c`-similitude for the induced endomorphisms. It is
obtained by compactness (`LinearMap.exists_isSimilitude_of_forall_level`) on the free quotients
of `A` and `B`, followed by extension of scalars (`LinearMap.isPerfPair_of_span_eq_top`).
-/

@[expose] public section

open Function

namespace LinearMap

variable {p : ℕ} [Fact p.Prime]

section Torsion

variable {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]

/-- Over `ℤ_p`, a torsion element is killed by a power of `p`. -/
lemma exists_pow_smul_eq_zero_of_mem_torsion {a : A} (ha : a ∈ Submodule.torsion ℤ_[p] A) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • a = 0 := by
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  refine ⟨r.valuation, ?_⟩
  have hr' : r • a = 0 := hra
  set u := PadicInt.unitCoeff hr0
  have hu : r = ↑u * (p : ℤ_[p]) ^ r.valuation := PadicInt.unitCoeff_spec hr0
  have h1 : ((↑u⁻¹ : ℤ_[p]) * r) • a = 0 := by
    rw [mul_smul, hr', smul_zero]
  rwa [hu, ← mul_assoc, Units.inv_mul, one_mul] at h1

/-- In a finitely generated `ℤ_p`-module, a single power of `p` kills the torsion. -/
lemma exists_pow_smul_eq_zero_of_finite [Module.Finite ℤ_[p] A] :
    ∃ c : ℕ, ∀ a ∈ Submodule.torsion ℤ_[p] A, (p : ℤ_[p]) ^ c • a = 0 := by
  obtain ⟨c, hc⟩ := Submodule.exists_pow_smul_eq_zero_of_isNoetherian (A := A) (p : ℤ_[p])
  exact ⟨c, fun a ha ↦ hc a (exists_pow_smul_eq_zero_of_mem_torsion ha)⟩

end Torsion

section Descent

variable {A B M : Type*} [AddCommGroup A] [Module ℤ_[p] A] [AddCommGroup B] [Module ℤ_[p] B]
  [AddCommGroup M] [Module ℤ_[p] M]

/-- A bilinear map killing torsion in both variables is determined by its values on lifts of
bases of the free quotients by torsion. -/
lemma eq_of_eq_on_lifts [Module.Finite ℤ_[p] A] [Module.Finite ℤ_[p] B]
    {I J : Type*} [Finite I] [Finite J]
    (bA : Module.Basis I ℤ_[p] (A ⧸ Submodule.torsion ℤ_[p] A))
    (bB : Module.Basis J ℤ_[p] (B ⧸ Submodule.torsion ℤ_[p] B)) (aI : I → A) (bJ : J → B)
    (haI : ∀ i, (Submodule.torsion ℤ_[p] A).mkQ (aI i) = bA i)
    (hbJ : ∀ j, (Submodule.torsion ℤ_[p] B).mkQ (bJ j) = bB j)
    (P P' : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] M)
    (hA : ∀ t ∈ Submodule.torsion ℤ_[p] A, P t = P' t)
    (hB : ∀ t ∈ Submodule.torsion ℤ_[p] B, P.flip t = P'.flip t)
    (h : ∀ i j, P (aI i) (bJ j) = P' (aI i) (bJ j)) : P = P' := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have hdecA (x : A) : x - ∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i ∈
      Submodule.torsion ℤ_[p] A := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, haI, Module.Basis.sum_repr, sub_self]
  have hdecB (y : B) : y - ∑ j, bB.repr ((Submodule.torsion ℤ_[p] B).mkQ y) j • bJ j ∈
      Submodule.torsion ℤ_[p] B := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hbJ, Module.Basis.sum_repr, sub_self]
  ext x y
  have hx := hA _ (hdecA x)
  have hy := hB _ (hdecB y)
  rw [← sub_add_cancel x (∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i), map_add,
    map_add, add_apply, add_apply, hx]
  congr 1
  rw [← sub_add_cancel y (∑ j, bB.repr ((Submodule.torsion ℤ_[p] B).mkQ y) j • bJ j)]
  have hy' := congr($hy (∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i))
  simp only [flip_apply] at hy'
  rw [map_add, map_add, hy']
  congr 1
  simp only [map_sum, map_smul, sum_apply, smul_apply, h]

end Descent

section Transport

variable {A B : Type*} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A]
  [AddCommGroup B] [Module ℤ_[p] B] [Module.Finite ℤ_[p] B]
  (FA : A →ₗ[ℤ_[p]] A) (FB : B →ₗ[ℤ_[p]] B) (c : ℤ_[p]) (e : ℕ)
  {E F : ℕ → Type*} [∀ m, AddCommGroup (E m)] [∀ m, Module ℤ_[p] (E m)]
  [∀ m, AddCommGroup (F m)] [∀ m, Module ℤ_[p] (F m)]
  (ρ : ∀ m, A →ₗ[ℤ_[p]] E m) (σ : ∀ m, B →ₗ[ℤ_[p]] F m)
  (Q : ∀ m, E m →ₗ[ℤ_[p]] F m →ₗ[ℤ_[p]] ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})

/-- **Integral duality from finite-level dualities.** Under the finite-level hypotheses of
`LinearMap.exists_isPerfPair_of_finiteLevel`, there is a `c`-similitude `A × B ⟶ ℤ_p` with
torsion left and right kernels. -/
theorem exists_isSimilitude_torsion_of_finiteLevel
    (hkerA : ∀ m a, ρ m a = 0 → ∃ a', a = (p : ℤ_[p]) ^ m • a')
    (hkerB : ∀ m b, σ m b = 0 → ∃ b', b = (p : ℤ_[p]) ^ m • b')
    (hrangeE : ∀ m (y : E m), (p : ℤ_[p]) ^ e • y ∈ range (ρ m))
    (hrangeF : ∀ m (y : F m), (p : ℤ_[p]) ^ e • y ∈ range (σ m))
    (hQl : ∀ m, Injective (Q m)) (hQr : ∀ m, Injective (Q m).flip)
    (hQF : ∀ m a b, Q m (ρ m (FA a)) (σ m (FB b)) = c • Q m (ρ m a) (σ m b)) :
    ∃ P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p], (∀ a b, P (FA a) (FB b) = c * P a b) ∧
      (∀ a, P a = 0 → a ∈ Submodule.torsion ℤ_[p] A) ∧
      (∀ b, P.flip b = 0 → b ∈ Submodule.torsion ℤ_[p] B) := by
  classical
  obtain ⟨cA, hcA⟩ := exists_pow_smul_eq_zero_of_finite (p := p) (A := A)
  obtain ⟨cB, hcB⟩ := exists_pow_smul_eq_zero_of_finite (p := p) (A := B)
  let TA := Submodule.torsion ℤ_[p] A
  let TB := Submodule.torsion ℤ_[p] B
  have hTA : TA ≤ TA.comap FA := fun a ha ↦ by
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_torsion ha
    exact ⟨⟨(p : ℤ_[p]) ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)) n⟩, by
        change (p : ℤ_[p]) ^ n • FA a = 0
        rw [← map_smul, hn, map_zero]⟩
  have hTB : TB ≤ TB.comap FB := fun b hb ↦ by
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_torsion hb
    exact ⟨⟨(p : ℤ_[p]) ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)) n⟩, by
        change (p : ℤ_[p]) ^ n • FB b = 0
        rw [← map_smul, hn, map_zero]⟩
  let FA' := TA.mapQ TA FA hTA
  let FB' := TB.mapQ TB FB hTB
  let bA := Module.Free.chooseBasis ℤ_[p] (A ⧸ TA)
  let bB := Module.Free.chooseBasis ℤ_[p] (B ⧸ TB)
  let aI (i : Module.Free.ChooseBasisIndex ℤ_[p] (A ⧸ TA)) : A :=
    (Submodule.mkQ_surjective TA (bA i)).choose
  have haI (i) : TA.mkQ (aI i) = bA i := (Submodule.mkQ_surjective TA (bA i)).choose_spec
  let bJ (j : Module.Free.ChooseBasisIndex ℤ_[p] (B ⧸ TB)) : B :=
    (Submodule.mkQ_surjective TB (bB j)).choose
  have hbJ (j) : TB.mkQ (bJ j) = bB j := (Submodule.mkQ_surjective TB (bB j)).choose_spec
  -- the finite-level pairings, made to kill torsion
  let P0 (m : ℕ) : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} :=
    (Q m).compl₁₂ ((ρ m) ∘ₗ ((p : ℤ_[p]) ^ cA • LinearMap.id))
      ((σ m) ∘ₗ ((p : ℤ_[p]) ^ cB • LinearMap.id))
  have hP0 (m : ℕ) (a : A) (b : B) :
      P0 m a b = Q m (ρ m ((p : ℤ_[p]) ^ cA • a)) (σ m ((p : ℤ_[p]) ^ cB • b)) := rfl
  -- integral lifts of the finite-level pairings on the free quotients
  let G (m : ℕ) : Matrix _ _ ℤ_[p] := fun i j ↦ Quotient.out (P0 m (aI i) (bJ j))
  let Pm (m : ℕ) : (A ⧸ TA) →ₗ[ℤ_[p]] (B ⧸ TB) →ₗ[ℤ_[p]] ℤ_[p] := Matrix.toLinearMap₂ bA bB (G m)
  have hPm (m : ℕ) (a : A) (b : B) :
      Ideal.Quotient.mk _ (Pm m (TA.mkQ a) (TB.mkQ b)) = P0 m a b := by
    have := eq_of_eq_on_lifts bA bB aI bJ haI hbJ
      (((Pm m).compl₁₂ TA.mkQ TB.mkQ).compr₂ (Ideal.span {(p : ℤ_[p]) ^ m}).mkQ)
      (P0 m) ?_ ?_ ?_
    · exact congr($this a b)
    · intro t ht
      ext b
      have : TA.mkQ t = 0 := (Submodule.Quotient.mk_eq_zero _).2 ht
      simp [this, hP0, hcA t ht]
    · intro t ht
      ext a
      have : TB.mkQ t = 0 := (Submodule.Quotient.mk_eq_zero _).2 ht
      simp [this, hP0, hcB t ht]
    · intro i j
      simp only [compl₁₂_apply, compr₂_apply, haI, hbJ, Pm, Matrix.toLinearMap₂_apply_basis,
        Submodule.mkQ_apply, G]
      exact Quotient.out_eq _
  have hmem {m : ℕ} {z : ℤ_[p]} :
      z ∈ PadicInt.powOpenAddSubgroup p m ↔ Ideal.Quotient.mk _ z = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).symm
  have hlevel (m : ℕ) : IsLevelSimilitude FA' FB' c (e + cB + cA) m (Pm m) := by
    refine ⟨fun x y ↦ ?_, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective TA x
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective TB y
      have e1 : FA' (TA.mkQ a) = TA.mkQ (FA a) := rfl
      have e2 : FB' (TB.mkQ b) = TB.mkQ (FB b) := rfl
      rw [hmem, map_sub, map_mul, e1, e2, hPm, hPm, hP0, hP0, ← map_smul, ← map_smul,
        hQF, ← Ideal.Quotient.algebraMap_eq,
        ← Algebra.smul_def, sub_self]
    · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective TA x
      have hab (b : B) : P0 m a b = 0 := by
        rw [← hPm]
        exact hmem.1 (hx _)
      set z := ρ m ((p : ℤ_[p]) ^ cB • (p : ℤ_[p]) ^ cA • a) with hzdef
      have hz : (p : ℤ_[p]) ^ e • z = 0 := by
        refine hQl m ?_
        rw [map_zero]
        ext y
        obtain ⟨b, hb⟩ := hrangeF m y
        rw [map_smul, smul_apply, ← map_smul, ← hb, zero_apply, hzdef, map_smul, map_smul,
          smul_apply,
          ← map_smul, ← map_smul]
        exact hab b
      rw [← map_smul] at hz
      obtain ⟨a', ha'⟩ := hkerA m _ hz
      refine ⟨TA.mkQ a', ?_⟩
      rw [← map_smul, ← map_smul, ← ha', smul_smul, smul_smul, ← pow_add, ← pow_add]
    · obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective TB y
      have hab (a : A) : P0 m a b = 0 := by
        rw [← hPm]
        exact hmem.1 (hy _)
      set z := σ m ((p : ℤ_[p]) ^ cA • (p : ℤ_[p]) ^ cB • b) with hzdef
      have hz : (p : ℤ_[p]) ^ e • z = 0 := by
        refine hQr m ?_
        rw [map_zero]
        ext x
        obtain ⟨a, ha⟩ := hrangeE m x
        rw [flip_apply, map_smul, ← smul_apply, ← map_smul, ← ha, zero_apply, hzdef,
          map_smul, map_smul, ← smul_apply, ← map_smul, ← map_smul]
        exact hab a
      rw [← map_smul] at hz
      obtain ⟨b', hb'⟩ := hkerB m _ hz
      refine ⟨TB.mkQ b', ?_⟩
      rw [← map_smul, ← map_smul, ← hb', smul_smul, smul_smul, ← pow_add, ← pow_add,
        add_right_comm e cA cB]
  obtain ⟨Gr, hGF, hGl, hGr⟩ :=
    exists_isSimilitude_of_forall_level FA' FB' c _ fun m ↦ ⟨Pm m, hlevel m⟩
  refine ⟨Gr.compl₁₂ TA.mkQ TB.mkQ, fun a b ↦ ?_, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have := hGF (TA.mkQ a) (TB.mkQ b)
    erw [Submodule.mapQ_apply, Submodule.mapQ_apply] at this
    exact this
  · have h0 : Gr (TA.mkQ a) = 0 := LinearMap.ext fun y ↦ by
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective TB y
      exact congr($ha b)
    exact (Submodule.Quotient.mk_eq_zero _).1 (hGl _ h0)
  · have h0 : Gr.flip (TB.mkQ b) = 0 := LinearMap.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective TA x
      exact congr($hb a)
    exact (Submodule.Quotient.mk_eq_zero _).1 (hGr _ h0)

omit [Module.Finite ℤ_[p] A] [Module.Finite ℤ_[p] B] in
/-- The `K`-bilinear extension of a `ℤ_p`-bilinear pairing along base changes. -/
noncomputable def baseChangePairing {K V W : Type*} [Field K] [Algebra ℤ_[p] K] [AddCommGroup V]
    [Module K V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] K V] [AddCommGroup W] [Module K W]
    [Module ℤ_[p] W] [IsScalarTower ℤ_[p] K W] {ι : A →ₗ[ℤ_[p]] V} (hι : IsBaseChange K ι)
    {κ : B →ₗ[ℤ_[p]] W} (hκ : IsBaseChange K κ) (P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p]) :
    V →ₗ[K] W →ₗ[K] K :=
  hι.lift
    { toFun a := hκ.lift ((Algebra.linearMap ℤ_[p] K) ∘ₗ P a)
      map_add' a a' := hκ.algHom_ext _ _ fun b ↦ by
        simp only [add_apply, IsBaseChange.lift_eq, coe_comp, Function.comp_apply, map_add,
          Algebra.linearMap_apply]
      map_smul' r a := hκ.algHom_ext _ _ fun b ↦ by
        simp only [smul_apply, IsBaseChange.lift_eq, coe_comp, Function.comp_apply, map_smul,
          Algebra.linearMap_apply, RingHom.id_apply, smul_eq_mul, map_mul, Algebra.smul_def] }

omit [Module.Finite ℤ_[p] A] [Module.Finite ℤ_[p] B] in
lemma baseChangePairing_apply {K V W : Type*} [Field K] [Algebra ℤ_[p] K] [AddCommGroup V]
    [Module K V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] K V] [AddCommGroup W] [Module K W]
    [Module ℤ_[p] W] [IsScalarTower ℤ_[p] K W] {ι : A →ₗ[ℤ_[p]] V} (hι : IsBaseChange K ι)
    {κ : B →ₗ[ℤ_[p]] W} (hκ : IsBaseChange K κ) (P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p]) (a : A)
    (b : B) : baseChangePairing hι hκ P (ι a) (κ b) = algebraMap ℤ_[p] K (P a b) := by
  simp [baseChangePairing, IsBaseChange.lift_eq]

/-- **Transport of finite-level duality to `K`** (the linear algebra of blueprint
`theorem-poincare-duality--6`). Let `A`, `B` be finitely generated `ℤ_p`-modules with
endomorphisms `F_A`, `F_B`, and `V`, `W` their extensions of scalars to a field `K ⊇ ℤ_p` with
endomorphisms `F_V`, `F_W` extending them. Suppose that for every `m` there are maps
`ρ : A ⟶ Eₘ`, `σ : B ⟶ Fₘ` with kernels in `pᵐ A`, `pᵐ B` and images containing `pᵉ Eₘ`,
`pᵉ Fₘ`, and a pairing `Qₘ : Eₘ × Fₘ ⟶ ℤ_p / pᵐ`, nondegenerate on both sides, whose
restriction along `ρ`, `σ` is a `c`-similitude. Then there is a perfect pairing `V × W ⟶ K`
which is a `c`-similitude for `F_V`, `F_W`. -/
theorem exists_isPerfPair_of_finiteLevel
    (hkerA : ∀ m a, ρ m a = 0 → ∃ a', a = (p : ℤ_[p]) ^ m • a')
    (hkerB : ∀ m b, σ m b = 0 → ∃ b', b = (p : ℤ_[p]) ^ m • b')
    (hrangeE : ∀ m (y : E m), (p : ℤ_[p]) ^ e • y ∈ range (ρ m))
    (hrangeF : ∀ m (y : F m), (p : ℤ_[p]) ^ e • y ∈ range (σ m))
    (hQl : ∀ m, Injective (Q m)) (hQr : ∀ m, Injective (Q m).flip)
    (hQF : ∀ m a b, Q m (ρ m (FA a)) (σ m (FB b)) = c • Q m (ρ m a) (σ m b))
    {K V W : Type*} [Field K] [Algebra ℤ_[p] K] [FaithfulSMul ℤ_[p] K] [AddCommGroup V]
    [Module K V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] K V] [AddCommGroup W] [Module K W]
    [Module ℤ_[p] W] [IsScalarTower ℤ_[p] K W] {ι : A →ₗ[ℤ_[p]] V} (hι : IsBaseChange K ι)
    {κ : B →ₗ[ℤ_[p]] W} (hκ : IsBaseChange K κ) (FV : V →ₗ[K] V) (FW : W →ₗ[K] W)
    (hFV : ∀ a, FV (ι a) = ι (FA a)) (hFW : ∀ b, FW (κ b) = κ (FB b)) :
    ∃ P : V →ₗ[K] W →ₗ[K] K, P.IsPerfPair ∧
      ∀ x y, P (FV x) (FW y) = algebraMap ℤ_[p] K c * P x y := by
  obtain ⟨P, hPF, hPl, hPr⟩ := exists_isSimilitude_torsion_of_finiteLevel FA FB c e ρ σ Q hkerA
    hkerB hrangeE hrangeF hQl hQr hQF
  have hspanV : Submodule.span K (Set.range ι) = ⊤ :=
    eq_top_iff.2 fun v _ ↦ hι.inductionOn v
      (fun m ↦ Submodule.subset_span ⟨m, rfl⟩) (fun s _ hn ↦ Submodule.smul_mem _ s hn)
      (fun _ _ ↦ add_mem)
  have hspanW : Submodule.span K (Set.range κ) = ⊤ :=
    eq_top_iff.2 fun v _ ↦ hκ.inductionOn v
      (fun m ↦ Submodule.subset_span ⟨m, rfl⟩) (fun s _ hn ↦ Submodule.smul_mem _ s hn)
      (fun _ _ ↦ add_mem)
  refine ⟨baseChangePairing hι hκ P, isPerfPair_of_span_eq_top ι κ hspanV hspanW P _
    (baseChangePairing_apply hι hκ P) hPl hPr, fun x y ↦ ?_⟩
  induction x using hι.inductionOn with
  | smul s x hx =>
    simp only [map_smul, smul_apply, smul_eq_mul, hx]
    ring
  | add x x' hx hx' =>
    simp only [map_add, add_apply, hx, hx']
    ring
  | tmul a =>
    induction y using hκ.inductionOn with
    | smul s y hy =>
      simp only [map_smul, smul_eq_mul, hy]
      ring
    | add y y' hy hy' =>
      simp only [map_add, hy, hy']
      ring
    | tmul b => rw [hFV, hFW, baseChangePairing_apply, baseChangePairing_apply, hPF, map_mul]

end Transport

end LinearMap
