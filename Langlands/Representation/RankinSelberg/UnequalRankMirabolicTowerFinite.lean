import Langlands.Representation.RankinSelberg.UnequalRankMirabolicTower
import Langlands.Representation.Parabolic.JacquetCenterSpanProof
import Langlands.Representation.Smooth.IsotypicProjector

/-!
# Spectral finiteness of tower data

Let `(ρ, q)` be a tower datum at level `i + 1` for a representation `η` of
`GL_(N+1)`. The upper unipotent radical of the block shape `(i + 1, N - i)` acts on
`q`-images through embedded radical elements of `P_(i+1)`. Hence `q` descends to a
map from the unnormalized Jacquet module of `η` for this shape to the quotient of
the carrier of `ρ` by its radical span. The block scalar `diag(a I_(i+1), I_(N-i))`
is the embedded element `leviScalar a`. If the block-scalar action on the Jacquet
module has finite-dimensional span, then `ρ (leviScalar a)` satisfies a nonzero
polynomial modulo the radical span.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankTower

open GeneralLinear HarmonicAnalysis Whittaker Polynomial

universe uF uW uA

section Polynomial

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {M' : Type*} [AddCommGroup M'] [Module ℂ M']

/-- A linear map intertwining two endomorphisms intertwines every polynomial in them. -/
theorem comp_aeval (f : M →ₗ[ℂ] M') {S : Module.End ℂ M} {S' : Module.End ℂ M'}
    (h : f ∘ₗ S = S' ∘ₗ f) (P : ℂ[X]) :
    f ∘ₗ aeval S P = aeval S' P ∘ₗ f := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hr]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial]
    have hk := Module.End.commute_pow_left_of_commute h.symm k
    ext x
    simp only [LinearMap.comp_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul]
    rw [← LinearMap.comp_apply f (S ^ k), ← hk, LinearMap.comp_apply]

end Polynomial

section Shape

/-- The block shape of rank `N + 1` with blocks of sizes `i + 1` and `N - i`. -/
def towerShape {i N : ℕ} (h : i + 1 ≤ N) : BlockShape (N + 1) where
  length := 2
  size := ![i + 1, N - i]
  positive := by
    intro b
    fin_cases b <;> simp
    omega
  sum_eq := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

theorem towerShape_index_val {i N : ℕ} (h : i + 1 ≤ N) (b : Fin (towerShape h).length)
    (r : Fin ((towerShape h).size b)) :
    ((towerShape h).index b r : ℕ) = (if b.val = 0 then 0 else i + 1) + r := by
  change ((finSigmaFinEquiv.trans (finCongr (towerShape h).sum_eq)) ⟨b, r⟩ : ℕ) = _
  rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  have hb : b.val < 2 := b.isLt
  rcases b with ⟨b, hb'⟩
  interval_cases b
  · simp
  · simp [towerShape]

/-- A coordinate lies in the first block exactly when it is smaller than `i + 1`. -/
theorem towerShape_index_lt_iff {i N : ℕ} (h : i + 1 ≤ N) (b : Fin (towerShape h).length)
    (r : Fin ((towerShape h).size b)) :
    ((towerShape h).index b r : ℕ) < i + 1 ↔ b.val = 0 := by
  have e := towerShape_index_val h b r
  have hr : (r : ℕ) < (towerShape h).size b := r.isLt
  have hb : b.val < 2 := b.isLt
  rcases b with ⟨b, hb'⟩
  interval_cases b
  · have hr' : (r : ℕ) < i + 1 := lt_of_lt_of_eq hr rfl
    have e' : ((towerShape h).index ⟨0, hb'⟩ r : ℕ) = r := by simpa using e
    exact ⟨fun _ => rfl, fun _ => by omega⟩
  · simp only [one_ne_zero, ite_false] at e
    simp only [one_ne_zero, iff_false, not_lt]
    omega

variable {F : Type uF} [Field F]

/-- Entries of the block unipotent radical outside the upper right block. -/
theorem towerShape_unipotent_entry {i N : ℕ} (h : i + 1 ≤ N)
    {g : Langlands.GeneralLinear (N + 1) F} (hg : g ∈ (towerShape h).unipotentSubgroup F)
    (x y : Fin (N + 1)) (hxy : ¬ (x.val < i + 1 ∧ i + 1 ≤ y.val)) :
    g x y = if x = y then 1 else 0 := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hg
  obtain ⟨hP, hD⟩ := hg
  rw [BlockShape.mem_parabolic_iff] at hP
  obtain ⟨⟨c, r⟩, rfl⟩ := (towerShape h).indexEquiv.surjective x
  obtain ⟨⟨d, t⟩, rfl⟩ := (towerShape h).indexEquiv.surjective y
  have ex := towerShape_index_lt_iff h c r
  have ey := towerShape_index_lt_iff h d t
  change ¬ (((towerShape h).index c r : ℕ) < i + 1 ∧ i + 1 ≤ ((towerShape h).index d t : ℕ))
    at hxy
  change g ((towerShape h).index c r) ((towerShape h).index d t) =
    if (towerShape h).index c r = (towerShape h).index d t then 1 else 0
  have hc : c.val < 2 := c.isLt
  have hd : d.val < 2 := d.isLt
  by_cases hcd : c = d
  · subst hcd
    rw [hD c r t]
    by_cases hrt : r = t
    · subst hrt
      simp
    · rw [ite_eq_right hrt, ite_eq_right]
      intro heq
      exact hrt (((towerShape h).index c).injective heq)
  · have hlt : d < c := by
      rcases lt_or_gt_of_ne hcd with hlt | hlt
      · exfalso
        apply hxy
        rw [Fin.lt_def] at hlt
        constructor
        · exact ex.mpr (by omega)
        · exact not_lt.mp fun h' => by have := ey.mp h'; omega
      · exact hlt
    rw [hP c d r t hlt, ite_eq_right]
    intro heq
    have h1 := congrArg Fin.val heq
    rw [Fin.lt_def] at hlt
    have h2 : ((towerShape h).index d t : ℕ) < i + 1 := ey.mpr (by omega)
    have h3 : ¬ ((towerShape h).index c r : ℕ) < i + 1 := fun h' => by
      have := ex.mp h'
      omega
    omega

/-- An element of the block unipotent radical as an upper unipotent matrix. -/
theorem towerShape_mem_upperUnipotent {i N : ℕ} (h : i + 1 ≤ N)
    (u : (towerShape h).unipotentRadical F) :
    u.val.val ∈ upperUnipotent (N + 1) F := by
  have hmem : u.val.val ∈ (towerShape h).unipotentSubgroup F := ⟨u.val, u.property, rfl⟩
  refine ⟨fun x y hyx => ?_, fun x => ?_⟩
  · have hlt : (y : ℕ) < x := hyx
    rw [towerShape_unipotent_entry h hmem x y (by omega), ite_eq_right]
    intro hxy
    subst hxy
    exact lt_irrefl _ hlt
  · rw [towerShape_unipotent_entry h hmem x x (by omega), ite_eq_left rfl]

/-- The block unipotent radical inside the upper unipotent group. -/
def towerShapeUnipotent {i N : ℕ} (h : i + 1 ≤ N) (u : (towerShape h).unipotentRadical F) :
    upperUnipotent (N + 1) F :=
  ⟨u.val.val, towerShape_mem_upperUnipotent h u⟩

theorem isLeading_towerShapeUnipotent {i N : ℕ} (h : i + 1 ≤ N)
    (u : (towerShape h).unipotentRadical F) : IsLeading i (towerShapeUnipotent h u) := by
  intro x y hx hy
  exact towerShape_unipotent_entry h ⟨u.val, u.property, rfl⟩ x y (by omega)

/-- The block scalar `diag(a I_(i+1), I_(N-i))` is the embedded `leviScalar a`. -/
theorem towerShape_blockScalar {i N : ℕ} (h : i + 1 ≤ N) (a : Fˣ) :
    (towerShape h).blockScalar F (fun b => if b.val = 0 then a else 1) =
      towerEmbedding h (MirabolicRigidity.leviScalar (n := i + 1) a).val := by
  apply Units.ext
  ext x y
  rw [BlockShape.coe_blockScalar, Matrix.diagonal_apply]
  rw [towerEmbedding_entry]
  obtain ⟨⟨c, r⟩, hx⟩ := (towerShape h).indexEquiv.surjective x
  have hlab : ((towerShape h).indexEquiv.symm x).1 = c := by rw [← hx, Equiv.symm_apply_apply]
  have ex := towerShape_index_lt_iff h c r
  change (towerShape h).index c r = x at hx
  rw [hx] at ex
  rw [hlab]
  have hlevi := levi_entry (GeneralLinear.scalar a : Langlands.GeneralLinear (i + 1) F)
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl]
    by_cases hx1 : x.val < i + 1
    · rw [ite_eq_left (ex.mp hx1), dite_eq_left (by omega), dite_eq_left (by omega)]
      change _ = (MirabolicRigidity.leviScalar (n := i + 1) a).val.val _ _
      unfold MirabolicRigidity.leviScalar
      rw [hlevi, dite_eq_left hx1, dite_eq_left hx1]
      simp [Matrix.GeneralLinearGroup.coe_scalar]
    · rw [ite_eq_right (fun h' => hx1 (ex.mpr h'))]
      by_cases hx2 : x.val < i + 1 + 1
      · rw [dite_eq_left hx2, dite_eq_left hx2]
        change _ = (MirabolicRigidity.leviScalar (n := i + 1) a).val.val _ _
        unfold MirabolicRigidity.leviScalar
        rw [hlevi, dite_eq_right hx1, ite_eq_left rfl]
        simp
      · rw [dite_eq_right hx2, ite_eq_left rfl]
        simp
  · rw [ite_eq_right hxy]
    have hne : ∀ (a' b' : ℕ), a' = x.val → b' = y.val → a' ≠ b' := fun a' b' ha hb hab =>
      hxy (Fin.ext (ha ▸ hb ▸ hab))
    split_ifs with h1 h2
    · change (0 : F) = (MirabolicRigidity.leviScalar (n := i + 1) a).val.val _ _
      unfold MirabolicRigidity.leviScalar
      rw [hlevi]
      split_ifs with h4 h5 h6
      · simp [Matrix.GeneralLinearGroup.coe_scalar, Fin.ext_iff, hne _ _ rfl rfl]
      · rfl
      · exact (hne _ _ rfl rfl (Fin.mk.inj h6)).elim
      · rfl
    · rfl
    · rfl

end Shape

section Tower

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

/-- The standard character of a block unipotent element reads its entry `(i, i+1)`. -/
theorem standardCharacter_towerShapeUnipotent (ψ : UnitaryAdditiveCharacter F) {i N : ℕ}
    (h : i + 1 ≤ N) (u : (towerShape h).unipotentRadical F) :
    (standardCharacter ψ N (towerShapeUnipotent h u) : ℂ) =
      ψ.complex (towerColumn h (towerShapeUnipotent h u) (Fin.last i)) := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin N)]
  · rfl
  · intro k _ hk
    have hki : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
    have e := towerShape_unipotent_entry h (g := u.val.val) ⟨u.val, u.property, rfl⟩
      k.castSucc k.succ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    rw [ite_eq_right (by simp [Fin.ext_iff])] at e
    exact e
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- The block unipotent radical moves `q`-images only by radical relations. -/
theorem IsTower.sub_mem_radicalSpan {ψ : UnitaryAdditiveCharacter F} {N i : ℕ}
    {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} (h : i + 1 ≤ N)
    {ρ : Representation ℂ (mirabolic (i + 1) F) A} {q : W →ₗ[ℂ] A}
    (hT : IsTower ψ η h ρ q) (u : (towerShape h).unipotentRadical F) (w : W) :
    q (η u.val.val w) - q w ∈ (MirabolicRigidity.radicalSpan ρ).toSubmodule := by
  set v := towerShapeUnipotent h u with hv
  obtain ⟨u', hu', hl'⟩ := exists_towerRadical_mul h v (isLeading_towerShapeUnipotent h u)
  have hchar := standardCharacter_eq_mul ψ h v u' hu'
  rw [standardCharacter_towerShapeUnipotent] at hchar
  have h1 : (standardCharacter ψ N u' : ℂ) = 1 := by
    have hne : ψ.complex (towerColumn h v (Fin.last i)) ≠ 0 := by
      rw [ψ.complex_apply]
      exact Circle.coe_ne_zero _
    exact (mul_eq_left₀ hne).mp hchar.symm
  have hη : η u.val.val w = η (towerRadical h (towerColumn h v)).val (η u'.val w) := by
    change η v.val w = _
    conv_lhs => rw [hu']
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  rw [hη, towerRadical_val, hT.levi, hT.unipotent u' hl', h1, one_smul]
  exact Submodule.subset_span ⟨(Mirabolic.radicalElement (towerColumn h v), q w), rfl⟩

/-- If the block-scalar action on the Jacquet module of the shape `(i + 1, N - i)` has
finite-dimensional span, then every `ρ (leviScalar a)` is annihilated modulo the
radical span by a nonzero polynomial. -/
theorem IsTower.exists_polynomial_of_finiteDimensional {ψ : UnitaryAdditiveCharacter F}
    {N i : ℕ} {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} (h : i + 1 ≤ N)
    {ρ : Representation ℂ (mirabolic (i + 1) F) A} {q : W →ₗ[ℂ] A}
    (hT : IsTower ψ η h ρ q)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun a : Fin (towerShape h).length → Fˣ =>
        Parabolic.leviCoinvariants (towerShape h)
          (η.comp ((towerShape h).parabolic F).subtype)
          ((towerShape h).blockScalarLevi F a)))))
    (a : Fˣ) :
    ∃ P : ℂ[X], P ≠ 0 ∧ ∀ y : A,
      aeval (ρ (MirabolicRigidity.leviScalar a)) P y ∈
        (MirabolicRigidity.radicalSpan ρ).toSubmodule := by
  let B := towerShape h
  let ρ' := η.comp (B.parabolic F).subtype
  let σ := Parabolic.leviCoinvariants B ρ'
  let a₀ : Fin B.length → Fˣ := fun b => if b.val = 0 then a else 1
  let S := σ (B.blockScalarLevi F a₀)
  have hint : IsIntegral ℂ S := by
    refine IsIntegral.of_mem_of_fg (Algebra.adjoin ℂ {S}) ?_ S
      (Algebra.self_mem_adjoin_singleton ℂ S)
    rw [Algebra.adjoin_eq_span]
    apply Submodule.FG.of_le ((Submodule.fg_iff_finiteDimensional _).mpr hfd)
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hx
    apply Submodule.subset_span
    exact ⟨a₀ ^ k, by simp only [S, map_pow]; rfl⟩
  refine ⟨minpoly ℂ S, minpoly.ne_zero hint, fun y => ?_⟩
  let R := (MirabolicRigidity.radicalSpan ρ).toSubmodule
  let z : mirabolic (i + 1) F := MirabolicRigidity.leviScalar a
  have hR : R ≤ R.comap (ρ z) := fun x hx =>
    (MirabolicRigidity.radicalSpan ρ).apply_mem_toSubmodule z hx
  let ρbar : Module.End ℂ (A ⧸ R) := R.mapQ R (ρ z) hR
  let Q : W →ₗ[ℂ] A ⧸ R := R.mkQ ∘ₗ q
  have hQ : ∀ u : B.unipotentRadical F, Q ∘ₗ ρ' u = Q := by
    intro u
    apply LinearMap.ext
    intro w
    change R.mkQ (q (η u.val.val w)) = R.mkQ (q w)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hT.sub_mem_radicalSpan h u w
  let Qbar := Jacquet.lift ρ' (B.unipotentRadical F) Q hQ
  have hcomm : Qbar ∘ₗ S = ρbar ∘ₗ Qbar := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro w
    change R.mkQ (q (η (B.blockScalar F a₀) w)) = R.mapQ R (ρ z) hR (R.mkQ (q w))
    rw [towerShape_blockScalar h a, hT.levi]
    rfl
  have hcomm' : R.mkQ ∘ₗ ρ z = ρbar ∘ₗ R.mkQ := by
    apply LinearMap.ext
    intro x
    rfl
  obtain ⟨w, rfl⟩ := hT.surjective y
  have key := comp_aeval Qbar hcomm (minpoly ℂ S)
  have key' := comp_aeval R.mkQ hcomm' (minpoly ℂ S)
  have h0 : R.mkQ (aeval (ρ z) (minpoly ℂ S) (q w)) = 0 := by
    rw [← LinearMap.comp_apply, key', LinearMap.comp_apply]
    change aeval ρbar (minpoly ℂ S) (Qbar (Jacquet.mk ρ' (B.unipotentRadical F) w)) = 0
    rw [← LinearMap.comp_apply, ← key, LinearMap.comp_apply, minpoly.aeval,
      LinearMap.zero_apply, map_zero]
  exact (Submodule.Quotient.mk_eq_zero R).mp h0

end Tower

section Padic

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

/-- For an admissible irreducible `η`, the operator `ρ (leviScalar a)` of a tower datum
at a positive level is annihilated modulo the radical span by a nonzero polynomial. -/
theorem IsTower.exists_polynomial {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ {ψ : UnitaryAdditiveCharacter F.Carrier} {N i : ℕ}
      {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F.Carrier) W} (h : i + 1 ≤ N)
      {ρ : Representation ℂ (mirabolic (i + 1) F.Carrier) A} {q : W →ₗ[ℂ] A},
      IsTower ψ η h ρ q → IsAdmissible η → η.IsIrreducible → ∀ a : F.Carrierˣ,
        ∃ P : ℂ[X], P ≠ 0 ∧ ∀ y : A,
          aeval (ρ (MirabolicRigidity.leviScalar a)) P y ∈
            (MirabolicRigidity.radicalSpan ρ).toSubmodule := by
  let := T.topology
  intro ψ N i η h ρ q hT hadm hirr a
  exact hT.exists_polynomial_of_finiteDimensional h
    (Parabolic.jacquetCenterSpan.{uF, uW} p F T (N + 1) (towerShape h) W η hadm
      (moduleFinite_asModule_of_isIrreducible η hirr)) a

end Padic

end Langlands.RankinSelberg.UnequalRankTower
