/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded

/-! # The contraction formula on a head-tail tensor summand

Source: Stacks Project, More on Algebra, Tags 0622 and 0664.
(blueprint: lem-weil-pbc-koszul-join-summand-leibniz).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

private theorem exteriorMap_coe_local {E F : Type (u + 1)} [AddCommGroup E] [Module A E]
    [AddCommGroup F] [Module A F] (g : E →ₗ[A] F) (n : ℕ) (x : ⋀[A]^n E) :
    (exteriorPower.map n g x : ExteriorAlgebra A F) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra A E) := by
  have h : (⋀[A]^n F).subtype.comp (exteriorPower.map n g) =
      (ExteriorAlgebra.map g).toLinearMap.comp (⋀[A]^n E).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply,
      ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

private theorem contract_natural_local {E F : Type (u + 1)} [AddCommGroup E] [Module A E]
    [AddCommGroup F] [Module A F] (g : E →ₗ[A] F)
    (φ : F →ₗ[A] A) (ψ : E →ₗ[A] A) (h : ψ = φ.comp g)
    (x : ExteriorAlgebra A E) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A F)) φ
        (ExteriorAlgebra.map g x) =
      ExteriorAlgebra.map g
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A E)) ψ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hv : φ (g v) = ψ v := by rw [h]; rfl
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hv, hx, map_sub, map_smul]

private theorem join_contract_leibniz_local
    (r n k : ℕ) (a : Fin (r + 1) → A) (m : ℕ)
    (x : ⋀[A]^n (Fin 1 →₀ A)) (y : ⋀[A]^k (Fin r →₀ A)) :
    CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm A (Fin (r + 1) →₀ A)))
        (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1)))
        (koszulJoinWedge r n k (x ⊗ₜ[A] y) : ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      ExteriorAlgebra.map (koszulHeadInclusion r)
          (CliffordAlgebra.contractLeft
            (Q := (0 : QuadraticForm A (Fin 1 →₀ A)))
            (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1)))
            (x : ExteriorAlgebra A (Fin 1 →₀ A))) *
        ExteriorAlgebra.map (koszulTailInclusion r) (y : ExteriorAlgebra A (Fin r →₀ A)) +
      algebraMap A (ExteriorAlgebra A (Fin (r + 1) →₀ A)) ((-1 : A) ^ n) *
        ExteriorAlgebra.map (koszulHeadInclusion r) (x : ExteriorAlgebra A (Fin 1 →₀ A)) *
        ExteriorAlgebra.map (koszulTailInclusion r)
          (CliffordAlgebra.contractLeft
            (Q := (0 : QuadraticForm A (Fin r →₀ A)))
            (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1)))
            (y : ExteriorAlgebra A (Fin r →₀ A))) := by
  obtain ⟨Df, hDf1, hDfre, hDfun, hDfgen, hDfzero, hDfdeg, hDfform,
    hDflei, hDfuniq⟩ := ExteriorAlgebra.koszul_differential A (Fin (r + 1) →₀ A)
      (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1)))
  obtain ⟨Dh, hDh1, hDhre, hDhun, hDhgen, hDhzero, hDhdeg, hDhform,
    hDhlei, hDhuniq⟩ := ExteriorAlgebra.koszul_differential A (Fin 1 →₀ A)
      (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1)))
  obtain ⟨Dt, hDt1, hDtre, hDtun, hDtgen, hDtzero, hDtdeg, hDtform,
    hDtlei, hDtuniq⟩ := ExteriorAlgebra.koszul_differential A (Fin r →₀ A)
      (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1)))
  have hhead : Finsupp.linearCombination A (fun _ : Fin 1 ↦ a 0 ^ (m + 1)) =
      (Finsupp.linearCombination A (fun j : Fin (r + 1) ↦ a j ^ (m + 1))).comp
        (koszulHeadInclusion r) := by
    apply Finsupp.lhom_ext
    intro j c
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [koszulHeadInclusion, Finsupp.linearCombination]
  have htail : Finsupp.linearCombination A (fun j : Fin r ↦ a j.succ ^ (m + 1)) =
      (Finsupp.linearCombination A (fun j : Fin (r + 1) ↦ a j ^ (m + 1))).comp
        (koszulTailInclusion r) := by
    apply Finsupp.lhom_ext
    intro j c
    simp [koszulTailInclusion, Finsupp.linearCombination]
  have hch : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin (r + 1) →₀ A)))
      (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1))) = Df := by
    apply hDfun
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v z
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin (r + 1) →₀ A)))
          (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1))) v z
  have hhh : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin 1 →₀ A)))
      (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1))) = Dh := by
    apply hDhun
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v z
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin 1 →₀ A)))
          (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1))) v z
  have hht : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1))) = Dt := by
    apply hDtun
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro v z
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm A (Fin r →₀ A)))
          (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1))) v z
  rw [hch, hhh, hht, koszulJoinWedge_tmul_coe]
  rw [exteriorMap_coe_local, exteriorMap_coe_local]
  let xh : ⋀[A]^n (Fin (r + 1) →₀ A) :=
    exteriorPower.map n (koszulHeadInclusion r) x
  have hxh : (xh : ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      ExteriorAlgebra.map (koszulHeadInclusion r)
        (x : ExteriorAlgebra A (Fin 1 →₀ A)) := by
    exact exteriorMap_coe_local _ _ _
  rw [← hxh]
  rw [hDflei n xh (ExteriorAlgebra.map (koszulTailInclusion r)
    (y : ExteriorAlgebra A (Fin r →₀ A)))]
  rw [← hch, ← hhh, ← hht]
  rw [hxh]
  rw [contract_natural_local (koszulHeadInclusion r)
      (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1))) _ hhead]
  rw [contract_natural_local (koszulTailInclusion r)
      (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1))) _ htail]

private noncomputable def exteriorCoordinate (r : ℕ) (a : Fin r → A) (m : ℕ)
    (i : ℤ) (n : ℕ) (h : -(n : ℤ) = i) :
    (completedKoszulPower (A := A) r a m).X i →ₗ[A]
      ExteriorAlgebra A (Fin r →₀ A) :=
  (⋀[A]^n (Fin r →₀ A)).subtype.comp
    ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat h).hom.hom

private theorem exteriorCoordinate_injective (r : ℕ) (a : Fin r → A) (m : ℕ)
    (i : ℤ) (n : ℕ) (h : -(n : ℤ) = i) :
    Function.Injective (exteriorCoordinate r a m i n h) := by
  intro x y hxy
  have he : ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat h).hom x =
    ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat h).hom y := Subtype.ext hxy
  apply_fun ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
    ComplexShape.embeddingDownNat h).inv at he
  simpa using he

private theorem exteriorCoordinate_d (r : ℕ) (a : Fin r → A) (m : ℕ)
    (i j : ℤ) (n : ℕ) (hi : -((n + 1 : ℕ) : ℤ) = i) (hj : -(n : ℤ) = j)
    (x : (completedKoszulPower (A := A) r a m).X i) :
    exteriorCoordinate r a m j n hj ((completedKoszulPower r a m).d i j x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A (fun k ↦ a k ^ (m + 1)))
        (exteriorCoordinate r a m i (n + 1) hi x) := by
  have hd := (ExteriorAlgebra.koszulComplex A r
    (fun k ↦ a k ^ (m + 1))).extend_d_eq ComplexShape.embeddingDownNat hi hj
  rw [show (completedKoszulPower r a m).d i j = _ from hd]
  change (((ExteriorAlgebra.koszulComplex A r (fun k ↦ a k ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat hj).hom
    (((ExteriorAlgebra.koszulComplex A r (fun k ↦ a k ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat hj).inv
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ a k ^ (m + 1))).d (n + 1) n
        (((ExteriorAlgebra.koszulComplex A r (fun k ↦ a k ^ (m + 1))).extendXIso
          ComplexShape.embeddingDownNat hi).hom x)))).val = _
  rw [Iso.inv_hom_id_apply]
  simp only [ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
  rfl

private theorem exteriorCoordinate_join (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ)
    (p q i : ℤ) (n k : ℕ) (hp : -(n : ℤ) = p) (hq : -(k : ℤ) = q)
    (h : p + q = i) (hi : -((n + k : ℕ) : ℤ) = i)
    (x : (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).X p)
    (y : (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).X q) :
    exteriorCoordinate (r + 1) a m i (n + k) hi
        (koszulJoinSummand r a m p q i h (x ⊗ₜ[A] y)) =
      ExteriorAlgebra.map (koszulHeadInclusion r)
          (exteriorCoordinate 1 (fun _ ↦ a 0) m p n hp x) *
        ExteriorAlgebra.map (koszulTailInclusion r)
          (exteriorCoordinate r (fun j ↦ a j.succ) m q k hq y) := by
  have hn : n = (-p).toNat := by omega
  have hk : k = (-q).toNat := by omega
  subst n k
  simp only [koszulJoinSummand, dite_eq_left (show p ≤ 0 by omega),
    dite_eq_left (show q ≤ 0 by omega), ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  change (((ExteriorAlgebra.koszulComplex A (r + 1) (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat hi).hom
    (((ExteriorAlgebra.koszulComplex A (r + 1) (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat hi).inv
      (koszulJoinWedge r (-p).toNat (-q).toNat
        (((koszulGradedTermIso 1 (fun _ ↦ a 0) m p (by omega)).hom x) ⊗ₜ[A]
          ((koszulGradedTermIso r (fun j ↦ a j.succ) m q (by omega)).hom y))))).val = _
  rw [Iso.inv_hom_id_apply, koszulJoinWedge_tmul_coe,
    exteriorMap_coe_local, exteriorMap_coe_local]
  rfl

private theorem contract_zero_exterior (r : ℕ) (a : Fin r → A) (m : ℕ)
    (x : ⋀[A]^0 (Fin r →₀ A)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
        (Finsupp.linearCombination A (fun j ↦ a j ^ (m + 1)))
        (x : ExteriorAlgebra A (Fin r →₀ A)) = 0 := by
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.surjective x
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_zero_apply]

private theorem exteriorCoordinate_head (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ)
    (p q i : ℤ) (n k s : ℕ) (hp : -(n : ℤ) = p) (hq : -(k : ℤ) = q)
    (hi : -(s : ℤ) = i) (hs : n + k = s + 1) (h : p + 1 + q = i)
    (x : (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).X p)
    (y : (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).X q) :
    exteriorCoordinate (r + 1) a m i s hi
        (koszulJoinSummand r a m (p + 1) q i h
          (((completedKoszulPower 1 (fun _ ↦ a 0) m).d p (p + 1) x) ⊗ₜ[A] y)) =
      ExteriorAlgebra.map (koszulHeadInclusion r)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin 1 →₀ A)))
            (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1)))
            (exteriorCoordinate 1 (fun _ ↦ a 0) m p n hp x)) *
        ExteriorAlgebra.map (koszulTailInclusion r)
          (exteriorCoordinate r (fun j ↦ a j.succ) m q k hq y) := by
  cases n with
  | zero =>
    have hp0 : p = 0 := by omega
    subst hp0
    have hz := contract_zero_exterior 1 (fun _ ↦ a 0) m
      (((ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a 0 ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom x)
    change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin 1 →₀ A)))
      (Finsupp.linearCombination A (fun _ ↦ a 0 ^ (m + 1)))
      (exteriorCoordinate 1 (fun _ ↦ a 0) m 0 0 rfl x) = 0 at hz
    rw [hz]
    simp [koszulJoinSummand]
  | succ n =>
    have hsk : s = n + k := by omega
    subst s
    rw [exteriorCoordinate_join r a m (p + 1) q i n k (by omega) hq h hi]
    rw [exteriorCoordinate_d 1 (fun _ ↦ a 0) m p (p + 1) n hp (by omega)]

private theorem exteriorCoordinate_tail (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ)
    (p q i : ℤ) (n k s : ℕ) (hp : -(n : ℤ) = p) (hq : -(k : ℤ) = q)
    (hi : -(s : ℤ) = i) (hs : n + k = s + 1) (h : p + (q + 1) = i)
    (x : (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).X p)
    (y : (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).X q) :
    exteriorCoordinate (r + 1) a m i s hi
        (koszulJoinSummand r a m p (q + 1) i h
          (x ⊗ₜ[A] ((completedKoszulPower r (fun j ↦ a j.succ) m).d q (q + 1) y))) =
      ExteriorAlgebra.map (koszulHeadInclusion r)
          (exteriorCoordinate 1 (fun _ ↦ a 0) m p n hp x) *
        ExteriorAlgebra.map (koszulTailInclusion r)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
            (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1)))
            (exteriorCoordinate r (fun j ↦ a j.succ) m q k hq y)) := by
  cases k with
  | zero =>
    have hq0 : q = 0 := by omega
    subst hq0
    have hz := contract_zero_exterior r (fun j ↦ a j.succ) m
      (((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j.succ ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom y)
    change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A (fun j ↦ a j.succ ^ (m + 1)))
      (exteriorCoordinate r (fun j ↦ a j.succ) m 0 0 rfl y) = 0 at hz
    rw [hz]
    simp [koszulJoinSummand, show p ≤ 0 by omega]
  | succ k =>
    have hsn : s = n + k := by omega
    subst s
    rw [exteriorCoordinate_join r a m p (q + 1) i n k hp (by omega) h hi]
    rw [exteriorCoordinate_d r (fun j ↦ a j.succ) m q (q + 1) k hq (by omega)]

private theorem koszul_sign_smul (r : ℕ) (p q : ℤ) (n : ℕ) (hp : -(n : ℤ) = p)
    (z : ExteriorAlgebra A (Fin (r + 1) →₀ A)) :
    ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) • z =
      algebraMap A (ExteriorAlgebra A (Fin (r + 1) →₀ A)) ((-1 : A) ^ n) * z := by
  change p.negOnePow • z = _
  rw [← hp, Int.negOnePow_neg, Units.smul_def, ← Int.cast_smul_eq_zsmul A,
    Int.cast_negOnePow_natCast, Algebra.smul_def]

/-- The nonpositive-degree part of the local Leibniz equation.

Source: Stacks Project, Tags 0622 and 0664.
(blueprint: lem-weil-pbc-koszul-join-summand-leibniz-nonpositive).

The proof identifies the extended terms with exterior powers and applies the
graded contraction Leibniz rule; the main theorem handles the zero extensions
in positive degrees. -/
theorem koszulJoinSummand_leibniz_nonpositive
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (p q : ℤ) (hp : p ≤ 0) (hq : q ≤ 0) :
    koszulJoinSummand (A := A) r a m p q (p + q) rfl ≫
        (completedKoszulPower (A := A) (r + 1) a m).d (p + q) (p + q + 1) =
      ((completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).d p (p + 1) ⊗ₘ 𝟙 _) ≫
          koszulJoinSummand r a m (p + 1) q (p + q + 1) (by omega) +
        ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
          ((𝟙 _ ⊗ₘ
            (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).d q (q + 1)) ≫
              koszulJoinSummand r a m p (q + 1) (p + q + 1) (by omega)) := by
  have hd0 (s : ℕ) (b : Fin s → A) : (completedKoszulPower s b m).d 0 1 = 0 := by
    apply HomologicalComplex.extend_d_from_eq_zero _ ComplexShape.embeddingDownNat
      0 1 0 rfl
    simp [ComplexShape.down_Rel]
  by_cases hpq : p + q = 0
  · have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst p q
    simp [hd0]
  · let n := (-p).toNat
    let k := (-q).toNat
    let s := (-(p + q + 1)).toNat
    have hn : -(n : ℤ) = p := by dsimp [n]; omega
    have hk : -(k : ℤ) = q := by dsimp [k]; omega
    have hs : -(s : ℤ) = p + q + 1 := by dsimp [s]; omega
    have hdeg : s + 1 = n + k := by dsimp [s, n, k]; omega
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    apply exteriorCoordinate_injective (r + 1) a m (p + q + 1) s hs
    change exteriorCoordinate (r + 1) a m (p + q + 1) s hs
        ((completedKoszulPower (r + 1) a m).d (p + q) (p + q + 1)
          (koszulJoinSummand r a m p q (p + q) rfl (x ⊗ₜ[A] y))) =
      exteriorCoordinate (r + 1) a m (p + q + 1) s hs
        (koszulJoinSummand r a m (p + 1) q (p + q + 1) (by omega)
            (((completedKoszulPower 1 (fun _ ↦ a 0) m).d p (p + 1) x) ⊗ₜ[A] y) +
          ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
            koszulJoinSummand r a m p (q + 1) (p + q + 1) (by omega)
              (x ⊗ₜ[A] ((completedKoszulPower r (fun j ↦ a j.succ) m).d q (q + 1) y)))
    have hd := exteriorCoordinate_d (r + 1) a m (p + q) (p + q + 1) s
      (by omega) hs (koszulJoinSummand r a m p q (p + q) rfl (x ⊗ₜ[A] y))
    simp only [hdeg] at hd
    rw [hd, exteriorCoordinate_join r a m p q (p + q) n k hn hk rfl (by omega)]
    rw [map_add, Units.smul_def, map_zsmul, ← Units.smul_def]
    rw [exteriorCoordinate_head r a m p q (p + q + 1) n k s hn hk hs
        hdeg.symm (by omega),
      exteriorCoordinate_tail r a m p q (p + q + 1) n k s hn hk hs
        hdeg.symm (by omega), koszul_sign_smul r p q n hn]
    have hlei := join_contract_leibniz_local r n k a m
      (((ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a 0 ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat hn).hom x)
      (((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j.succ ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat hk).hom y)
    simpa only [koszulJoinWedge_tmul_coe, exteriorMap_coe_local,
      exteriorCoordinate, LinearMap.comp_apply, Submodule.subtype_apply,
      ModuleCat.Hom.hom, mul_assoc] using! hlei

/-- The local Leibniz equation before assembling the total tensor differential.

Source: Stacks Project, Tag 0622, definition-koszul, and Tag 0664,
lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-koszul-join-summand-leibniz).
-/
theorem koszulJoinSummand_leibniz
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (p q : ℤ) :
    koszulJoinSummand (A := A) r a m p q (p + q) rfl ≫
        (completedKoszulPower (A := A) (r + 1) a m).d (p + q) (p + q + 1) =
      ((completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).d p (p + 1) ⊗ₘ 𝟙 _) ≫
          koszulJoinSummand r a m (p + 1) q (p + q + 1) (by omega) +
        ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
          ((𝟙 _ ⊗ₘ
            (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).d q (q + 1)) ≫
              koszulJoinSummand r a m p (q + 1) (p + q + 1) (by omega)) := by
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · exact koszulJoinSummand_leibniz_nonpositive r a m p q hp hq
    · have hqnone : ComplexShape.embeddingDownNat.r q = none :=
        ComplexShape.embeddingDownNat.r_eq_none q (by
          intro j hj
          dsimp [ComplexShape.embeddingDownNat] at hj
          change -(j : ℤ) = q at hj
          omega)
      have hzq : (completedKoszulPower (A := A) r
          (fun j ↦ a j.succ) m).d q (q + 1) = 0 := by
        change HomologicalComplex.extend.d _ _ _ = 0
        exact HomologicalComplex.extend.d_none_eq_zero _ _ _ hqnone
      simp [koszulJoinSummand, hp, hq, hzq]
  · have hpnone : ComplexShape.embeddingDownNat.r p = none :=
      ComplexShape.embeddingDownNat.r_eq_none p (by
        intro j hj
        dsimp [ComplexShape.embeddingDownNat] at hj
        change -(j : ℤ) = p at hj
        omega)
    have hzp : (completedKoszulPower (A := A) 1
        (fun _ ↦ a 0) m).d p (p + 1) = 0 := by
      change HomologicalComplex.extend.d _ _ _ = 0
      exact HomologicalComplex.extend.d_none_eq_zero _ _ _ hpnone
    simp [koszulJoinSummand, hp, hzp]

end AlgebraicGeometry.Scheme
