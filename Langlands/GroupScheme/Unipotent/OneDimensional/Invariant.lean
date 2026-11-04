import Langlands.GroupScheme.Unipotent.OneDimensional.Hopf
import Langlands.GroupScheme.Unipotent.HopfFixed

/-! # A primitive coordinate outside the polynomials in a given primitive coordinate -/

noncomputable section

universe u

open CategoryTheory Polynomial TensorProduct
open Algebra.TensorProduct (includeLeft includeRight productMap)

namespace Langlands.GroupScheme.Unipotent.OneDimensional

open AffineLinearEmbedding Chevalley

section Polys

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

/-- The subspace `k[y]` of polynomials in `y`. -/
abbrev polys (y : B) : Submodule k B :=
  LinearMap.range (aeval y : k[X] →ₐ[k] B).toLinearMap

theorem aeval_mem_polys (y : B) (f : k[X]) : aeval y f ∈ polys (k := k) y :=
  ⟨f, rfl⟩

theorem one_mem_polys (y : B) : (1 : B) ∈ polys (k := k) y :=
  ⟨1, map_one (aeval y : k[X] →ₐ[k] B)⟩

/-- Contracting the second factor commutes with a map on the first factor. -/
theorem rid_lTensor_map {R : Type*} [CommRing R] [Algebra k R] (φ : R →ₗ[k] B)
    (g : Module.Dual k B) (w : R ⊗[k] B) :
    TensorProduct.rid k B (g.lTensor B (φ.rTensor B w)) =
      φ (TensorProduct.rid k R (g.lTensor R w)) := by
  induction w with
  | tmul r b => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- Contracting the first factor with a functional vanishing on the image of `φ`. -/
theorem lid_rTensor_map_eq_zero {R : Type*} [CommRing R] [Algebra k R] (φ : R →ₗ[k] B)
    (θ : Module.Dual k B) (hθ : ∀ r, θ (φ r) = 0) (w : R ⊗[k] B) :
    TensorProduct.lid k B (θ.rTensor B (φ.rTensor B w)) = 0 := by
  induction w with
  | tmul r b => simp [hθ]
  | add w w' hw hw' => simp only [map_add, hw, hw', add_zero]

end Polys

section Invariant

variable {k B : Type*} [Field k] [CommRing B] [Bialgebra k B]

open Coalgebra

/-- The comultiplication of a polynomial in a primitive element. -/
theorem comul_aeval {y : B} (hy : Bialgebra.IsPrimitiveElem k y) (f : k[X]) :
    comul (R := k) (aeval y f) = (aeval y : k[X] →ₐ[k] B).toLinearMap.rTensor B
      (aeval ((X : k[X]) ⊗ₜ[k] (1 : B) + 1 ⊗ₜ y) f) := by
  have h : (Bialgebra.comulAlgHom k B).comp (aeval y) =
      (Algebra.TensorProduct.map (aeval y) (AlgHom.id k B)).comp
        (aeval ((X : k[X]) ⊗ₜ[k] (1 : B) + 1 ⊗ₜ y)) := by
    apply Polynomial.algHom_ext
    simp [hy.comul_eq_tmul_add_tmul, add_comm]
  exact AlgHom.congr_fun h f

theorem rightAct_aeval_mem {y : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (g : Module.Dual k B) (f : k[X]) : rightAct g (aeval y f) ∈ polys (k := k) y := by
  rw [rightAct_apply, comul_aeval hy, rid_lTensor_map]
  exact ⟨_, rfl⟩

theorem leftAct_aeval_eq_zero {y : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (θ : Module.Dual k B) (hθ : ∀ f : k[X], θ (aeval y f) = 0) (f : k[X]) :
    leftAct θ (aeval y f) = 0 := by
  rw [leftAct_apply, comul_aeval hy]
  exact lid_rTensor_map_eq_zero _ θ hθ _

/-- **Invariant vector modulo `k[y]`.** In a unipotent bialgebra, if some element is not a
polynomial in the primitive element `y`, then some element `a ∉ k[y]` with `ε(a) = 0` is
invariant modulo `k[y]` under all right translations. -/
theorem exists_invariant_mod_polys (hB : OneMemStable k B) {y : B}
    (hy : Bialgebra.IsPrimitiveElem k y) {b : B} (hb : b ∉ polys (k := k) y) :
    ∃ a : B, a ∉ polys (k := k) y ∧ counit (R := k) a = 0 ∧
      ∀ g : Module.Dual k B, rightAct g a - g 1 • a ∈ polys (k := k) y := by
  classical
  let S : Submodule k B := polys y
  let Q := B ⧸ S
  let T : Module.Dual k B → Q →ₗ[k] Q :=
    fun g => S.mapQ S (rightAct g) (fun _ hs => by
      obtain ⟨f, rfl⟩ := hs
      exact rightAct_aeval_mem hy g f)
  let I := {θ : Module.Dual k B // ∀ s ∈ S, θ s = 0}
  let π : I → Q →ₗ[k] B := fun θ =>
    S.liftQ (leftAct θ.val) (fun _ hs => by
      obtain ⟨f, rfl⟩ := hs
      exact LinearMap.mem_ker.2
        (leftAct_aeval_eq_zero hy θ.val (fun f => θ.property _ ⟨f, rfl⟩) f))
  have hπ : ∀ i g m, π i (T g m) = rightAct g (π i m) := by
    intro i g m
    induction m using Submodule.Quotient.induction_on with
    | _ b =>
        change leftAct i.val (rightAct g b) = rightAct g (leftAct i.val b)
        exact (rightAct_leftAct g i.val b).symm
  have hsep : ∀ m : Q, (∀ i, π i m = 0) → m = 0 := by
    intro m hm
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro ψ
    let θ : Module.Dual k B := ψ ∘ₗ S.mkQ
    have hθ : ∀ s ∈ S, θ s = 0 := by
      intro s hs
      change ψ (S.mkQ s) = 0
      rw [show S.mkQ s = 0 from (Submodule.Quotient.mk_eq_zero S).2 hs, map_zero]
    have h := hm ⟨θ, hθ⟩
    have heq : counit (R := k) (π ⟨θ, hθ⟩ m) = ψ m := by
      induction m using Submodule.Quotient.induction_on with
      | _ b =>
          change counit (R := k) (leftAct θ b) = ψ (S.mkQ b)
          exact counit_leftAct θ b
    rw [h, map_zero] at heq
    exact heq.symm
  let V : Submodule k B := regularSpan ({b} : Finset B)
  let W : Submodule k Q := V.map S.mkQ
  have hW : ∀ g m, m ∈ W → T g m ∈ W := by
    rintro g _ ⟨b', hb', rfl⟩
    exact ⟨rightAct g b', rightAct_mem_regularSpan _ g hb', rfl⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have hm : S.mkQ b ∈ W :=
      ⟨b, subset_regularSpan {b} (Finset.mem_singleton_self b), rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact hb ((Submodule.Quotient.mk_eq_zero S).1 hm)
  obtain ⟨w, -, hw0, hw⟩ := Unipotent.exists_invariant hB T π hπ hsep W hW hW0
  obtain ⟨b', rfl⟩ := S.mkQ_surjective w
  have h1 : (1 : B) ∈ S := one_mem_polys y
  refine ⟨b' - counit (R := k) b' • (1 : B), ?_, ?_, ?_⟩
  · intro h
    apply hw0
    apply (Submodule.Quotient.mk_eq_zero S).2
    have h' := S.add_mem h (S.smul_mem (counit (R := k) b') h1)
    rwa [sub_add_cancel] at h'
  · simp [Bialgebra.counit_one]
  · intro g
    have heq : rightAct g (b' - counit (R := k) b' • (1 : B)) -
        g 1 • (b' - counit (R := k) b' • (1 : B)) = rightAct g b' - g 1 • b' := by
      rw [map_sub, map_smul, Unipotent.rightAct_one, smul_sub, smul_smul, smul_smul, mul_comm]
      abel
    rw [heq]
    apply (Submodule.Quotient.mk_eq_zero S).1
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
    exact sub_eq_zero.2 (hw g)

/-- **Invariance gives a polynomial cocycle.** If `y` is primitive and transcendental, the
comultiplication is cocommutative, and `a` is invariant modulo `k[y]` under right translations,
then `Δ a - a ⊗ 1 - 1 ⊗ a = c(y ⊗ 1, 1 ⊗ y)` for a polynomial `c` in two variables. -/
theorem exists_comul_eq_of_invariant {y : B} (hinj : Function.Injective (aeval y : k[X] →ₐ[k] B))
    (hcomm : ∀ b : B, TensorProduct.comm k B B (comul (R := k) b) = comul (R := k) b)
    {a : B} (ha : ∀ g : Module.Dual k B, rightAct g a - g 1 • a ∈ polys (k := k) y) :
    ∃ c : k[X][X], comul (R := k) a = a ⊗ₜ 1 + 1 ⊗ₜ a + tensorEval (aeval y) y c := by
  let φ : k[X] →ₗ[k] B := (aeval y : k[X] →ₐ[k] B).toLinearMap
  obtain ⟨ρ, hρ⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  let P : B →ₗ[k] B := φ ∘ₗ ρ
  have hP : ∀ s ∈ polys (k := k) y, P s = s := by
    rintro _ ⟨f, rfl⟩
    change φ (ρ (φ f)) = φ f
    rw [← LinearMap.comp_apply ρ φ, hρ, LinearMap.id_apply]
  let D : B ⊗[k] B := comul (R := k) a - a ⊗ₜ 1 - 1 ⊗ₜ a
  have hDg : ∀ g : Module.Dual k B, TensorProduct.rid k B (g.lTensor B D) =
      rightAct g a - g 1 • a - g a • (1 : B) := by
    intro g
    simp only [D, map_sub, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, rightAct_apply]
  have hD1 : P.rTensor B D = D := by
    apply tensor_ext
    intro g
    rw [rid_lTensor_map, hDg]
    exact hP _ (sub_mem (ha g) (Submodule.smul_mem _ _ (one_mem_polys y)))
  have hDs : TensorProduct.comm k B B D = D := by
    simp only [D, map_sub, hcomm, TensorProduct.comm_tmul]
    abel
  have hD2 : P.lTensor B D = D := by
    conv_lhs => rw [← hDs]
    rw [LinearMap.lTensor_comm, hD1, hDs]
  have hDP : TensorProduct.map φ φ (TensorProduct.map ρ ρ D) = D := by
    rw [← LinearMap.comp_apply (TensorProduct.map φ φ), ← TensorProduct.map_comp,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
    exact (congrArg (P.lTensor B) hD1).trans hD2
  refine ⟨(polyEquivTensor k k[X]).symm (TensorProduct.map ρ ρ D), ?_⟩
  rw [tensorEval_eq_map, AlgHom.comp_apply]
  erw [(polyEquivTensor k k[X]).apply_symm_apply]
  change comul (R := k) a = a ⊗ₜ 1 + 1 ⊗ₜ a + TensorProduct.map φ φ (TensorProduct.map ρ ρ D)
  rw [hDP]
  simp only [D]
  abel

end Invariant

section Eval

variable {k : Type*} [Field k]

theorem ev2_swap {R : Type*} [CommRing R] [Algebra k R] (u v : R) (c : k[X][X]) :
    ev2 u v (Bivariate.swap c) = ev2 v u c := by
  have h : (ev2 u v).comp (Bivariate.swap (R := k)).toAlgHom = ev2 v u := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [CAlgHom, Bivariate.swap_X]
    · simp [Bivariate.swap_Y]
  exact AlgHom.congr_fun h c

theorem tensorEval_eq_ev2 {S T : Type*} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    (y : S) (y' : T) : tensorEval (aeval y) y' = ev2 (y ⊗ₜ[k] (1 : T)) ((1 : S) ⊗ₜ y') := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [CAlgHom]
  · simp

theorem productMap_comp_tensorEval {S A : Type*} [CommRing S] [Algebra k S] [CommRing A]
    [Algebra k A] (f g : S →ₐ[k] A) (y : S) :
    (productMap f g).comp (tensorEval (aeval y) y) = ev2 (f y) (g y) := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [CAlgHom]
  · simp

theorem map_add_sub_sub {S T : Type*} [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    (φ : S →ₐ[k] T) (a b c d : S) : φ (a + b - c - d) = φ a + φ b - φ c - φ d := by
  simp only [map_sub, map_add]

/-- An algebra map applied to the cocycle defect. -/
theorem map_defect {S : Type*} [CommRing S] [Algebra k S] (φ : k[X][X][X] →ₐ[k] S)
    (c : k[X][X]) :
    φ (defect c) = ev2 (φ (varU + varV)) (φ varW) c + ev2 (φ varU) (φ varV) c -
      ev2 (φ varU) (φ (varV + varW)) c - ev2 (φ varV) (φ varW) c := by
  rw [← comp_ev2 (R := k[X][X][X]) φ, ← comp_ev2 (R := k[X][X][X]) φ,
    ← comp_ev2 (R := k[X][X][X]) φ, ← comp_ev2 (R := k[X][X][X]) φ]
  exact map_add_sub_sub (S := k[X][X][X]) φ _ _ _ _

end Eval

section Points

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- Points commute when the comultiplication is cocommutative. -/
theorem mul_comm_of_comm
    (hcomm : (Algebra.TensorProduct.comm k B B).toAlgHom.comp (comul e) = comul e)
    {A : CommAlgCat.{u} (CommRingCat.of k)} (u v : F.obj A) : u * v = v * u := by
  apply val_injective e
  rw [val_mul, val_mul]
  conv_rhs => rw [← hcomm]
  rw [← AlgHom.comp_assoc]
  congr 1
  ext b <;> simp [mul_comm]

variable {y a : B} {c : k[X][X]}
  (ha : comul e a = a ⊗ₜ 1 + 1 ⊗ₜ a + tensorEval (aeval y) y c)
include ha

/-- The point formula: `a(u v) = a(u) + a(v) + c(y(u), y(v))`. -/
theorem val_mul_apply_of_comul {A : CommAlgCat.{u} (CommRingCat.of k)} (u v : F.obj A) :
    val e (u * v) a = val e u a + val e v a + ev2 (val e u y) (val e v y) c := by
  rw [val_mul, AlgHom.comp_apply, ha, map_add, map_add,
    Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, map_one, mul_one, one_mul, ← AlgHom.comp_apply, productMap_comp_tensorEval]

variable (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
  (hinj : Function.Injective (aeval y : k[X] →ₐ[k] B))
include hy hinj

/-- The cocycle is normalized: `c(X, 0) = 0`. -/
theorem coeff_zero_eq_zero_of_comul (hε : counit e a = 0) : c.coeff 0 = 0 := by
  have hy0 : counit e y = 0 := by
    let := bialgebra e
    exact hy.counit_eq_zero
  have h := val_mul_apply_of_comul ha (univ e) (1 : F.obj B)
  simp only [mul_one, val_one, val_univ, AlgHom.comp_apply, hε, hy0, map_zero,
    AlgHom.id_apply, add_zero] at h
  have h' : ev2 y 0 c = 0 := by linear_combination -h
  rw [ev2_apply, eval₂_at_zero] at h'
  exact hinj (h'.trans (map_zero (aeval y : k[X] →ₐ[k] B)).symm)

omit hy hinj in
/-- The cocycle is symmetric when the comultiplication is cocommutative. -/
theorem swap_eq_of_comul
    (hcomm : (Algebra.TensorProduct.comm k B B).toAlgHom.comp (comul e) = comul e)
    (hinj2 : Function.Injective (tensorEval (aeval y : k[X] →ₐ[k] B) y)) :
    Bivariate.swap c = c := by
  let A := CommAlgCat.of (CommRingCat.of k) (B ⊗[k] B)
  have h := val_mul_apply_of_comul ha (pt e (A := A) includeLeft) (pt e (A := A) includeRight)
  rw [mul_comm_of_comm hcomm, val_mul_apply_of_comul ha, val_pt, val_pt] at h
  apply hinj2
  rw [tensorEval_eq_ev2, ev2_swap]
  rw [show (includeLeft : B →ₐ[k] B ⊗[k] B) y = y ⊗ₜ 1 from rfl,
    show (includeRight : B →ₐ[k] B ⊗[k] B) y = 1 ⊗ₜ y from rfl] at h
  linear_combination h

/-- The cocycle satisfies the two-cocycle identity, by associativity of points. -/
theorem isCocycle_of_comul : IsCocycle c := by
  let A := CommAlgCat.of (CommRingCat.of k) ((B ⊗[k] B) ⊗[k] B)
  let E2 : k[X][X] →ₐ[k] B ⊗[k] B := tensorEval (aeval y) y
  let E3 : k[X][X][X] →ₐ[k] (B ⊗[k] B) ⊗[k] B := tensorEval E2 y
  have htr : Transcendental k y := transcendental_iff_injective.mpr hinj
  have hE3 : Function.Injective E3 :=
    tensorEval_injective E2 (tensorEval_injective _ hinj htr) htr
  have h := congrArg (fun x => val e x a)
    (mul_assoc (pt e (A := A) ((includeLeft : B ⊗[k] B →ₐ[k] A).comp includeLeft))
      (pt e (A := A) ((includeLeft : B ⊗[k] B →ₐ[k] A).comp includeRight))
      (pt e (A := A) includeRight))
  simp only [val_mul_apply_of_comul ha, val_mul_apply hy, val_pt] at h
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply] at h
  rw [show (includeRight : B →ₐ[k] (B ⊗[k] B) ⊗[k] B) a = 1 ⊗ₜ a from rfl,
    show (includeRight : B →ₐ[k] (B ⊗[k] B) ⊗[k] B) y = 1 ⊗ₜ y from rfl,
    show (includeRight : B →ₐ[k] B ⊗[k] B) y = 1 ⊗ₜ y from rfl,
    show (includeRight : B →ₐ[k] B ⊗[k] B) a = 1 ⊗ₜ a from rfl] at h
  have hU : E3 varU = (y ⊗ₜ[k] (1 : B)) ⊗ₜ[k] (1 : B) := by simp [E3, E2]
  have hV : E3 varV = ((1 : B) ⊗ₜ[k] y) ⊗ₜ[k] (1 : B) := by simp [E3, E2]
  have hW : E3 varW = (1 : B ⊗[k] B) ⊗ₜ[k] y := by simp [E3, E2]
  show defect c = 0
  apply hE3
  rw [map_zero, map_defect, map_add, map_add, hU, hV, hW]
  linear_combination h

omit hinj in
/-- `a(uⁿ) = n a + ∑_{i<n} c(i y, y)` for the universal point. -/
theorem val_univ_pow_apply_of_comul (hε : counit e a = 0) (n : ℕ) :
    val e (univ e ^ n) a = n • a + ∑ i ∈ Finset.range n, ev2 ((i : B) * y) y c := by
  induction n with
  | zero =>
      rw [pow_zero, val_one, AlgHom.comp_apply, hε, map_zero, zero_smul, Finset.sum_range_zero,
        add_zero]
  | succ n ih =>
      rw [pow_succ, val_mul_apply_of_comul ha, ih, val_pow_apply hy, val_univ, AlgHom.id_apply,
        AlgHom.id_apply, Finset.sum_range_succ, succ_nsmul]
      simp only [nsmul_eq_mul]
      abel

/-- The `p`-power obstruction of the cocycle vanishes when `uᵖ = 1`. -/
theorem powerSum_eq_zero_of_comul (p : ℕ) [CharP k p] (hp : univ e ^ p = 1)
    (hε : counit e a = 0) : powerSum p c = 0 := by
  have h := val_univ_pow_apply_of_comul ha hy hε p
  rw [hp, val_one, AlgHom.comp_apply, hε, map_zero] at h
  have hpa : p • a = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
  rw [hpa, zero_add] at h
  apply hinj
  rw [map_zero, powerSum, map_sum]
  simp only [comp_ev2 (aeval y), map_mul, map_natCast, aeval_X]
  exact h.symm

end Points

section Main

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The comultiplication of a polynomial in a primitive element, as `f(y ⊗ 1 + 1 ⊗ y)`. -/
theorem comul_aeval_eq {y : B} (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
    (f : k[X]) : comul e (aeval y f) = aeval (y ⊗ₜ[k] (1 : B) + 1 ⊗ₜ y) f := by
  let := bialgebra e
  rw [← aeval_algHom_apply,
    show comul e y = 1 ⊗ₜ[k] y + y ⊗ₜ[k] 1 from hy.comul_eq_tmul_add_tmul, add_comm]

/-- **A second primitive coordinate.** Over a perfect field, let `B` be a unipotent coordinate
ring with `B` and `B ⊗ B` domains, and `y` a nonzero primitive element with `B / yB`
finite-dimensional. If some element of `B` is not a polynomial in `y`, then some primitive
element of `B` is not a polynomial in `y`. -/
theorem exists_primitive_not_mem_polys [PerfectField k] [IsDomain B] [IsDomain (B ⊗[k] B)]
    (hB : letI := bialgebra e; OneMemStable k B) {y : B}
    (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y) (hy0 : y ≠ 0)
    (hfin : Module.Finite k (B ⧸ Ideal.span {y})) {b : B} (hb : b ∉ polys (k := k) y) :
    ∃ t : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k t) ∧ t ∉ polys (k := k) y := by
  let := bialgebra e
  have hy0' : counit e y = 0 := hy.counit_eq_zero
  have htr : Transcendental k y := transcendental_of_augmentation_eq_zero (counit e) hy0 hy0'
  have hinj : Function.Injective (aeval y : k[X] →ₐ[k] B) := transcendental_iff_injective.mp htr
  have hcomm := comm_comp_comul e hy hfin
  obtain ⟨a, ha, haε, hainv⟩ := exists_invariant_mod_polys hB hy hb
  obtain ⟨c, hc⟩ := exists_comul_eq_of_invariant hinj (fun b => AlgHom.congr_fun hcomm b) hainv
  have hc' : comul e a = a ⊗ₜ 1 + 1 ⊗ₜ a + tensorEval (aeval y) y c := hc
  have haε' : counit e a = 0 := haε
  have h0 := coeff_zero_eq_zero_of_comul hc' hy hinj haε'
  have hsw := swap_eq_of_comul hc' hcomm (tensorEval_injective (aeval y) hinj htr)
  have hcoc := isCocycle_of_comul hc' hy hinj
  have hf : ∃ f : k[X], c = coboundary f := by
    rcases CharP.exists' k with hk | ⟨p, hp, hpk⟩
    · exact exists_eq_coboundary_of_charZero hcoc h0
    · have hps := powerSum_eq_zero_of_comul hc' hy hinj p (univ_pow_char e p hy hfin) haε'
      exact exists_eq_coboundary_of_charP p c.natDegree c le_rfl hcoc hsw h0 hps
  obtain ⟨f, rfl⟩ := hf
  refine ⟨a - aeval y f, ?_, ?_⟩
  · rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    change comul e (a - aeval y f) = _
    have hL : aeval (y ⊗ₜ[k] (1 : B)) f = aeval y f ⊗ₜ[k] (1 : B) :=
      aeval_algHom_apply (includeLeft : B →ₐ[k] B ⊗[k] B) y f
    have hR : aeval ((1 : B) ⊗ₜ[k] y) f = (1 : B) ⊗ₜ[k] aeval y f :=
      aeval_algHom_apply (includeRight : B →ₐ[k] B ⊗[k] B) y f
    rw [map_sub, hc', comul_aeval_eq e hy, tensorEval_eq_ev2, ev2_coboundary, hL, hR,
      tmul_sub, sub_tmul]
    abel
  · intro ht
    have h := (polys (k := k) y).add_mem ht (aeval_mem_polys y f)
    rw [sub_add_cancel] at h
    exact ha h

end Main

end Langlands.GroupScheme.Unipotent.OneDimensional
