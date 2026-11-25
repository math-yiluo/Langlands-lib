/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Prod

/-! # Nonpositive-degree exterior basis splitting

Projection to the tail and contraction with the head coordinate give an explicit
inverse to exterior assembly. Only head degrees zero and one survive in the tensor
coproduct; checking these summands proves the graded join map is bijective.
(Source: Stacks Project, Tag 0664; blueprint: new-weil-pbc-koszul-join-graded-nonpositive.)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

namespace KoszulHeadSplit

open ExteriorAlgebra

variable (R : Type (u + 1)) [CommRing R] (r : ℕ)

/-- Wedge on the left with the first standard generator, after prefix inclusion.
Source: Stacks Project, Tags 0628 and 0629
(head-generator version of the source-library last-generator assembly proof). -/
private noncomputable def headWedge (n : ℕ) :
    ⋀[R]^n (Fin r →₀ R) →ₗ[R] ⋀[R]^(n + 1) (Fin (r + 1) →₀ R) :=
  (LinearMap.codRestrict (⋀[R]^(n + 1) (Fin (r + 1) →₀ R))
    { toFun := fun x ↦ ι R (Finsupp.single (0 : Fin (r + 1)) 1) * x.val
      map_add' := fun x y ↦ by simp [mul_add]
      map_smul' := fun c x ↦ by simp }
    (fun x ↦ by
      change _ ∈ (LinearMap.range (ι R)) ^ (n + 1)
      rw [Nat.add_comm n 1, pow_add, pow_one]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self (ι R) _) x.property)).comp
    (exteriorPower.map n (koszulTailInclusion (A := R) r))

/-- The explicit assembly map `(a,b) ↦ inclusion(a) + e_head ∧ inclusion(b)`.
Source: Stacks Project, Tags 0628 and 0629
(head-generator version of the source-library last-generator assembly proof). -/
private noncomputable def headAssembly (n : ℕ) :
    (⋀[R]^(n + 1) (Fin r →₀ R) × ⋀[R]^n (Fin r →₀ R)) →ₗ[R]
      ⋀[R]^(n + 1) (Fin (r + 1) →₀ R) :=
  LinearMap.coprod (exteriorPower.map (n + 1) (koszulTailInclusion (A := R) r))
    (headWedge R r n)

private noncomputable def tailRetraction : (Fin (r + 1) →₀ R) →ₗ[R] Fin r →₀ R :=
  Finsupp.lcomapDomain Fin.succ (Fin.succ_injective r)

private theorem tail_retraction_inclusion (v : Fin r →₀ R) :
    tailRetraction R r (koszulTailInclusion (A := R) r v) = v :=
  Finsupp.leftInverse_lcomapDomain_mapDomain Fin.succ (Fin.succ_injective r) v

private theorem tail_retraction_head :
    tailRetraction R r (Finsupp.single (0 : Fin (r + 1)) 1) = 0 := by
  ext i
  simp [tailRetraction]

private theorem head_tail_decomposition (v : Fin (r + 1) →₀ R) :
    koszulTailInclusion (A := R) r (tailRetraction R r v) +
      v (0 : Fin (r + 1)) • Finsupp.single (0 : Fin (r + 1)) 1 = v := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, koszulTailInclusion, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_of_notMem_range]
    · exact zero_add _
    · simp
  · simp [koszulTailInclusion, Finsupp.mapDomain_apply_of_injective (Fin.succ_injective r),
      tailRetraction, Fin.succ_ne_zero]

private theorem exterior_map_coe {E F : Type (u + 1)} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (q : E →ₗ[R] F) (n : ℕ) (x : ⋀[R]^n E) :
    (exteriorPower.map n q x : ExteriorAlgebra R F) =
      ExteriorAlgebra.map q (x : ExteriorAlgebra R E) := by
  have h : (⋀[R]^n F).subtype.comp (exteriorPower.map n q) =
      (ExteriorAlgebra.map q).toLinearMap.comp (⋀[R]^n E).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, AlgHom.toLinearMap_apply]
    exact (ExteriorAlgebra.map_apply_ιMulti q v).symm
  exact LinearMap.congr_fun h x

private theorem head_form_tail (v : Fin r →₀ R) :
    Finsupp.linearCombination R (fun i : Fin (r + 1) ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0)
      (koszulTailInclusion (A := R) r v) = 0 := by
  rw [koszulTailInclusion, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  have h : ((fun i : Fin (r + 1) ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0) ∘
      Fin.succ) = fun _ : Fin r ↦ (0 : R) := by
    funext i
    simp [Fin.succ_ne_zero]
  rw [h]
  simp [Finsupp.linearCombination_apply]

private theorem contract_head_tail (x : ExteriorAlgebra R (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
      (Finsupp.linearCombination R
        (fun i ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0))
      (ExteriorAlgebra.map (koszulTailInclusion (A := R) r) x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | ι_mul x v hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      head_form_tail, zero_smul, hx, mul_zero, sub_zero]

private theorem exterior_projection_tail (x : ExteriorAlgebra R (Fin r →₀ R)) :
    ExteriorAlgebra.map (tailRetraction R r)
      (ExteriorAlgebra.map (koszulTailInclusion (A := R) r) x) = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap c => simp
  | ι v => simp [tail_retraction_inclusion]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem head_form_apply (v : Fin (r + 1) →₀ R) :
    Finsupp.linearCombination R (fun i ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0) v =
      v (0 : Fin (r + 1)) := by
  have h : Finsupp.linearCombination R
      (fun i : Fin (r + 1) ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0) =
      Finsupp.lapply (0 : Fin (r + 1)) := by
    ext i
    simp [Finsupp.lapply, Finsupp.single_apply]
  exact LinearMap.congr_fun h v

private theorem exterior_split (x : ExteriorAlgebra R (Fin (r + 1) →₀ R)) :
    ExteriorAlgebra.map (koszulTailInclusion (A := R) r)
      (ExteriorAlgebra.map (tailRetraction R r) x) +
    ι R (Finsupp.single (0 : Fin (r + 1)) 1) *
      ExteriorAlgebra.map (koszulTailInclusion (A := R) r)
        (ExteriorAlgebra.map (tailRetraction R r)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
            (Finsupp.linearCombination R
              (fun i ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0)) x)) = x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy =>
    simp only [map_add, mul_add]
    rw [← add_add_add_comm, hx, hy]
  | ι_mul x v hx =>
    let L : ExteriorAlgebra R (Fin (r + 1) →₀ R) :=
      ι R (Finsupp.single (0 : Fin (r + 1)) 1)
    let W : ExteriorAlgebra R (Fin (r + 1) →₀ R) :=
      ι R (koszulTailInclusion (A := R) r (tailRetraction R r v))
    let T := (ExteriorAlgebra.map (koszulTailInclusion (A := R) r)).comp
      (ExteriorAlgebra.map (tailRetraction R r))
    let D := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
      (Finsupp.linearCombination R (fun i ↦ if i = (0 : Fin (r + 1)) then (1 : R) else 0))
    have hW : W + v (0 : Fin (r + 1)) • L = ι R v := by
      dsimp [W, L]
      rw [← map_smul, ← map_add, head_tail_decomposition]
    have hswap : W * L = -(L * W) :=
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap _ _)
    have hL : L * L = 0 := ι_sq_zero _
    simp only [map_mul, ExteriorAlgebra.map_apply_ι]
    change W * T x + L * T (D (ι R v * x)) = ι R v * x
    have hDx : T (D (ι R v * x)) = v (0 : Fin (r + 1)) • T x - W * T (D x) := by
      simp only [D, CliffordAlgebra.contractLeft_ι_mul, head_form_apply,
        map_sub, map_smul, map_mul, T, AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι]
      rfl
    rw [hDx, ← hW]
    change T x + L * T (D x) = x at hx
    conv_rhs => rw [← hx]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      ← mul_assoc, hswap, neg_mul, hL, smul_zero, add_zero, sub_eq_add_neg]
    abel_nf
    simp only [mul_smul_comm, ← mul_assoc]

/-- Source: Stacks Project, Tags 0628 and 0629, splitting the exterior algebra on
adjoining the first generator
(head-generator version of the source-library last-generator assembly proof).

Proof: let `p` be restriction of a finitely supported vector to the tail and
let `δ` evaluate its head coordinate. Inclusion `j` and restriction satisfy
`p ∘ j = id`, and `p(e_head)=0`. Define the inverse on degree `n+1` by
`x ↦ (Λ^(n+1)(p)(x), Λ^n(p)(contractLeft δ x))`. Contraction kills the exterior
algebra of the tail: prove this by left induction using its defining Leibniz
rule. Consequently contracting `j(a) + e_head ∧ j(b)` gives `j(b)`, so both
components of the proposed inverse recover `(a,b)`.

For the other inverse identity put `T=Λ(j) ∘ Λ(p)` on the full exterior algebra
and `L=ι(e_head)`. Left induction proves `T(x) + L*T(contractLeft δ x) = x`.
The scalar and addition cases are immediate. For `ι(v)*x`, decompose the vector
as `j(p(v)) + δ(v)*e_head`; use the contraction rule, the induction hypothesis,
anticommutation of `ι(j(p(v)))` with `L`, and `L*L=0`. Restrict this identity to
degree `n+1`. All maps are genuine constructions and the identities hold also
for `r=0`, the zero ring, and degrees above the rank. -/
private theorem headAssembly_bijective (n : ℕ) :
    Function.Bijective (headAssembly R r n) := by
  let δ : Fin (r + 1) → R := fun i ↦ if i = (0 : Fin (r + 1)) then 1 else 0
  let inv (x : ⋀[R]^(n + 1) (Fin (r + 1) →₀ R)) :=
    (exteriorPower.map (n + 1) (tailRetraction R r) x,
      exteriorPower.map n (tailRetraction R r) (koszulBoundary R (r + 1) δ n x))
  have hleft : Function.LeftInverse inv (headAssembly R r n) := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply Subtype.ext
      change (exteriorPower.map (n + 1) (tailRetraction R r)
        (headAssembly R r n (a, b)) : ExteriorAlgebra R (Fin r →₀ R)) = a.val
      rw [exterior_map_coe]
      change ExteriorAlgebra.map (tailRetraction R r)
        ((exteriorPower.map (n + 1) (koszulTailInclusion (A := R) r) a :
            ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
          ι R (Finsupp.single (0 : Fin (r + 1)) 1) *
            (exteriorPower.map n (koszulTailInclusion (A := R) r) b :
              ExteriorAlgebra R (Fin (r + 1) →₀ R))) = _
      simp only [exterior_map_coe, map_add, map_mul, ExteriorAlgebra.map_apply_ι,
        tail_retraction_head, map_zero, zero_mul, add_zero, exterior_projection_tail]
    · apply Subtype.ext
      change (exteriorPower.map n (tailRetraction R r)
        (koszulBoundary R (r + 1) δ n (headAssembly R r n (a, b))) :
          ExteriorAlgebra R (Fin r →₀ R)) = b.val
      rw [exterior_map_coe]
      change ExteriorAlgebra.map (tailRetraction R r)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
          (Finsupp.linearCombination R δ)
          ((exteriorPower.map (n + 1) (koszulTailInclusion (A := R) r) a :
              ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
            ι R (Finsupp.single (0 : Fin (r + 1)) 1) *
              (exteriorPower.map n (koszulTailInclusion (A := R) r) b :
                ExteriorAlgebra R (Fin (r + 1) →₀ R)))) = _
      simp only [exterior_map_coe, map_add, δ, contract_head_tail,
        CliffordAlgebra.contractLeft_ι_mul, Finsupp.linearCombination_single,
        ite_true, one_smul, mul_zero, sub_zero, zero_add, exterior_projection_tail]
  have hright : Function.RightInverse inv (headAssembly R r n) := by
    intro x
    apply Subtype.ext
    change (exteriorPower.map (n + 1) (koszulTailInclusion (A := R) r)
      (exteriorPower.map (n + 1) (tailRetraction R r) x) :
        ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
      ι R (Finsupp.single (0 : Fin (r + 1)) 1) *
        (exteriorPower.map n (koszulTailInclusion (A := R) r)
          (exteriorPower.map n (tailRetraction R r) (koszulBoundary R (r + 1) δ n x)) :
            ExteriorAlgebra R (Fin (r + 1) →₀ R)) = x.val
    simp only [exterior_map_coe]
    exact exterior_split R r x.val
  exact ⟨hleft.injective, hright.surjective⟩

end KoszulHeadSplit

variable {A : Type (u + 1)} [CommRing A]

private theorem power_isZero_pos (s : ℕ) (a : Fin s → A) (m : ℕ)
    (i : ℤ) (hi : 0 < i) : IsZero ((completedKoszulPower s a m).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -(n : ℤ) = i at h
  omega

private theorem head_isZero (a : Fin 1 → A) (m : ℕ) (i : ℤ)
    (h0 : i ≠ 0) (h1 : i ≠ -1) :
    IsZero ((completedKoszulPower 1 a m).X i) := by
  classical
  by_cases hi : 0 < i
  · exact power_isZero_pos 1 a m i hi
  · have hn : 1 < (-i).toNat := by omega
    have : IsEmpty (Set.powersetCard (Fin 1) (-i).toNat) := ⟨fun s ↦ by
      have h := Finset.card_le_univ s.val
      have hs : s.val.card = (-i).toNat := s.property
      simp only [Fintype.card_fin, hs] at h
      omega⟩
    let b := (Finsupp.basisSingleOne :
      Module.Basis (Fin 1) A (Fin 1 →₀ A)).exteriorPower (-i).toNat
    have : Subsingleton (⋀[A]^((-i).toNat) (Fin 1 →₀ A)) :=
      b.repr.injective.subsingleton
    exact (ModuleCat.isZero_of_subsingleton _).of_iso
      (koszulGradedTermIso 1 a m i (by omega))

/-- Testing a tensor totalization on its two possible head degrees. -/
private theorem tensor_test_bijective
    (K L : CochainComplex (ModuleCat.{u + 1} A) ℤ) (i q0 q1 : ℤ)
    (hq0 : 0 + q0 = i) (hq1 : -1 + q1 = i)
    (hK : ∀ p : ℤ, p ≠ 0 → p ≠ -1 → IsZero (K.X p))
    (V W M : ModuleCat.{u + 1} A)
    (e0 : V ≅ K.X 0 ⊗ L.X q0) (e1 : W ≅ K.X (-1) ⊗ L.X q1)
    (f : (HomologicalComplex.tensorObj K L).X i ⟶ M)
    (hb : Function.Bijective (LinearMap.coprod
      (e0.hom ≫ HomologicalComplex.ιTensorObj K L 0 q0 i hq0 ≫ f).hom
      (e1.hom ≫ HomologicalComplex.ιTensorObj K L (-1) q1 i hq1 ≫ f).hom)) :
    Function.Bijective f.hom := by
  let u0 := e0.hom ≫ HomologicalComplex.ιTensorObj K L 0 q0 i hq0
  let u1 := e1.hom ≫ HomologicalComplex.ιTensorObj K L (-1) q1 i hq1
  let U : ModuleCat.of A (V × W) ⟶ (HomologicalComplex.tensorObj K L).X i :=
    ModuleCat.ofHom (LinearMap.coprod u0.hom u1.hom)
  have hU : Epi U := by
    constructor
    intro Z g h he
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = i at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = q0 := by omega
      subst q
      apply (cancel_epi e0.hom).mp
      ext x
      have hh := congrArg
        (fun k : ModuleCat.of A (V × W) ⟶ Z ↦ k (x, 0)) he
      have hUx : U (x, 0) = u0.hom x := by
        change u0.hom x + u1.hom 0 = u0.hom x
        rw [map_zero, add_zero]
      change g (U (x, 0)) = h (U (x, 0)) at hh
      rw [hUx] at hh
      exact hh
    · by_cases hp1 : p = -1
      · subst p
        have hq : q = q1 := by omega
        subst q
        apply (cancel_epi e1.hom).mp
        ext x
        have hh := congrArg
          (fun k : ModuleCat.of A (V × W) ⟶ Z ↦ k (0, x)) he
        have hUx : U (0, x) = u1.hom x := by
          change u0.hom 0 + u1.hom x = u1.hom x
          rw [map_zero, zero_add]
        change g (U (0, x)) = h (U (0, x)) at hh
        rw [hUx] at hh
        exact hh
      · exact ((MonoidalCategory.tensorRight (L.X q)).map_isZero (hK p hp hp1)).eq_of_src _ _
  have hs : Function.Surjective U := (ModuleCat.epi_iff_surjective U).mp hU
  have hc : Function.Bijective (f ∘ U) := by
    change Function.Bijective (f.hom.comp U.hom)
    simpa only [U, u0, u1, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_coprod,
      Category.assoc, LinearMap.comp_assoc] using hb
  exact ⟨hc.injective.of_comp_right hs, hc.surjective.of_comp⟩

private def headZero : (⋀[A]^0 (Fin 1 →₀ A)) ≃ₗ[A] A :=
  exteriorPower.zeroEquiv A _

private def headOne : (⋀[A]^1 (Fin 1 →₀ A)) ≃ₗ[A] A :=
  (exteriorPower.oneEquiv A _).trans (Finsupp.uniqueLinearEquiv A A (0 : Fin 1))

private def headTensor (d r n : ℕ) (e : (⋀[A]^d (Fin 1 →₀ A)) ≃ₗ[A] A) :
    (⋀[A]^n (Fin r →₀ A)) ≃ₗ[A]
      (⋀[A]^d (Fin 1 →₀ A) ⊗[A] ⋀[A]^n (Fin r →₀ A)) :=
  (TensorProduct.lid A _).symm.trans
    (TensorProduct.congr e.symm (LinearEquiv.refl A _))

private theorem headTensor_apply (d r n : ℕ)
    (e : (⋀[A]^d (Fin 1 →₀ A)) ≃ₗ[A] A) (y : ⋀[A]^n (Fin r →₀ A)) :
    headTensor d r n e y = e.symm 1 ⊗ₜ[A] y := by
  simp [headTensor]

private theorem join_zero_coe (r n : ℕ) (y : ⋀[A]^n (Fin r →₀ A)) :
    (koszulJoinWedge r 0 n (headTensor 0 r n headZero y) :
        ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      ExteriorAlgebra.map (koszulTailInclusion r) y.val := by
  rw [headTensor_apply, koszulJoinWedge_tmul_coe,
    KoszulHeadSplit.exterior_map_coe, KoszulHeadSplit.exterior_map_coe]
  have hz : ((headZero (A := A)).symm 1 : ExteriorAlgebra A (Fin 1 →₀ A)) = 1 := by
    simp [headZero, exteriorPower.zeroEquiv_symm_apply,
      exteriorPower.ιMulti_apply_coe]
  rw [hz, map_one, one_mul]

private theorem join_one_coe (r n : ℕ) (y : ⋀[A]^n (Fin r →₀ A)) :
    (koszulJoinWedge r 1 n (headTensor 1 r n headOne y) :
        ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      ExteriorAlgebra.ι A (Finsupp.single 0 1) *
        ExteriorAlgebra.map (koszulTailInclusion r) y.val := by
  rw [headTensor_apply, koszulJoinWedge_tmul_coe,
    KoszulHeadSplit.exterior_map_coe, KoszulHeadSplit.exterior_map_coe]
  have h1 : ((headOne (A := A)).symm 1 : ExteriorAlgebra A (Fin 1 →₀ A)) =
      ExteriorAlgebra.ι A (Finsupp.single 0 1) := by
    simp [headOne, exteriorPower.oneEquiv_symm_apply,
      Finsupp.uniqueLinearEquiv_symm_apply, exteriorPower.ιMulti_apply_coe]
  rw [h1, ExteriorAlgebra.map_apply_ι]
  simp [koszulHeadInclusion]

private def termIso (s : ℕ) (a : Fin s → A) (m n : ℕ) :
    (completedKoszulPower s a m).X (-(n : ℤ)) ≅
      ModuleCat.of A (⋀[A]^n (Fin s →₀ A)) :=
  (ExteriorAlgebra.koszulComplex A s (fun j ↦ a j ^ (m + 1))).extendXIso
    ComplexShape.embeddingDownNat rfl

private theorem summand_formula (r : ℕ) (a : Fin (r + 1) → A) (m d n : ℕ) :
    ((termIso 1 (fun _ ↦ a 0) m d).inv ⊗ₘ
        (termIso r (fun j ↦ a j.succ) m n).inv) ≫
      koszulJoinSummand r a m (-(d : ℤ)) (-(n : ℤ)) (-((d + n : ℕ) : ℤ)) (by omega) ≫
      (termIso (r + 1) a m (d + n)).hom =
        ModuleCat.ofHom (koszulJoinWedge r d n) := by
  cases d <;> cases n <;>
    simp only [koszulJoinSummand, neg_nonpos, Int.natCast_nonneg, dite_true,
      koszulGradedTermIso, termIso, Category.assoc,
      tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, id_tensorHom_id,
      Category.id_comp, Category.comp_id]
  all_goals rfl

private theorem join_formula (r : ℕ) (a : Fin (r + 1) → A) (m d n : ℕ) :
    ((termIso 1 (fun _ ↦ a 0) m d).inv ⊗ₘ
        (termIso r (fun j ↦ a j.succ) m n).inv) ≫
      HomologicalComplex.ιTensorObj
        (completedKoszulPower 1 (fun _ ↦ a 0) m)
        (completedKoszulPower r (fun j ↦ a j.succ) m)
        (-(d : ℤ)) (-(n : ℤ)) (-((d + n : ℕ) : ℤ)) (by omega) ≫
      koszulJoinGraded r a m (-((d + n : ℕ) : ℤ)) ≫
      (termIso (r + 1) a m (d + n)).hom =
        ModuleCat.ofHom (koszulJoinWedge r d n) := by
  simp only [koszulJoinGraded, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  exact summand_formula r a m d n

/-- The ambient exterior algebra removes dependence on the chosen degree equality. -/
private theorem join_formula_coe (r : ℕ) (a : Fin (r + 1) → A) (m d n N : ℕ)
    (hN : d + n = N)
    (x : ⋀[A]^d (Fin 1 →₀ A) ⊗[A] ⋀[A]^n (Fin r →₀ A)) :
    ((((termIso 1 (fun _ ↦ a 0) m d).inv ⊗ₘ
        (termIso r (fun j ↦ a j.succ) m n).inv) ≫
      HomologicalComplex.ιTensorObj
        (completedKoszulPower 1 (fun _ ↦ a 0) m)
        (completedKoszulPower r (fun j ↦ a j.succ) m)
        (-(d : ℤ)) (-(n : ℤ)) (-(N : ℤ)) (by omega) ≫
      koszulJoinGraded r a m (-(N : ℤ)) ≫
      (termIso (r + 1) a m N).hom) x :
        ExteriorAlgebra A (Fin (r + 1) →₀ A)) = (koszulJoinWedge r d n x).val := by
  subst N
  exact congrArg
    (fun f : ModuleCat.of A
        (⋀[A]^d (Fin 1 →₀ A) ⊗[A] ⋀[A]^n (Fin r →₀ A)) ⟶
        ModuleCat.of A (⋀[A]^(d + n) (Fin (r + 1) →₀ A)) ↦
      (f x : ExteriorAlgebra A (Fin (r + 1) →₀ A))) (join_formula r a m d n)

private theorem join_negative (r : ℕ) (a : Fin (r + 1) → A) (m n : ℕ) :
    Function.Bijective (koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ))).hom := by
  let K := completedKoszulPower 1 (fun _ ↦ a 0) m
  let L := completedKoszulPower r (fun j ↦ a j.succ) m
  let e0 := (headTensor 0 r (n + 1) (headZero (A := A))).toModuleIso ≪≫
    ((termIso 1 (fun _ ↦ a 0) m 0).symm ⊗ᵢ
      (termIso r (fun j ↦ a j.succ) m (n + 1)).symm)
  let e1 := (headTensor 1 r n (headOne (A := A))).toModuleIso ≪≫
    ((termIso 1 (fun _ ↦ a 0) m 1).symm ⊗ᵢ
      (termIso r (fun j ↦ a j.succ) m n).symm)
  let t := termIso (r + 1) a m (n + 1)
  have hb : Function.Bijective
      (koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ)) ≫ t.hom).hom := by
    apply tensor_test_bijective K L (-((n + 1 : ℕ) : ℤ))
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (by omega)
      (head_isZero (fun _ ↦ a 0) m) _ _ _ e0 e1
    have h0 :
        (e0.hom ≫ HomologicalComplex.ιTensorObj K L 0 (-((n + 1 : ℕ) : ℤ))
          (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
          koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ)) ≫ t.hom).hom =
        (exteriorPower.map (n + 1) (koszulTailInclusion r)) := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      change ((((termIso 1 (fun _ ↦ a 0) m 0).inv ⊗ₘ
          (termIso r (fun j ↦ a j.succ) m (n + 1)).inv) ≫
        HomologicalComplex.ιTensorObj K L 0 (-((n + 1 : ℕ) : ℤ))
          (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
        koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ)) ≫ t.hom)
          (headTensor 0 r (n + 1) headZero y) :
          ExteriorAlgebra A (Fin (r + 1) →₀ A)) = _
      dsimp only [K, L, t]
      exact (join_formula_coe r a m 0 (n + 1) (n + 1) (by omega)
        (headTensor 0 r (n + 1) headZero y)).trans
          ((join_zero_coe r (n + 1) y).trans
            (KoszulHeadSplit.exterior_map_coe A _ _ _).symm)
    have h1 :
        (e1.hom ≫ HomologicalComplex.ιTensorObj K L (-1) (-(n : ℤ))
          (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
          koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ)) ≫ t.hom).hom =
        KoszulHeadSplit.headWedge A r n := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      change ((((termIso 1 (fun _ ↦ a 0) m 1).inv ⊗ₘ
          (termIso r (fun j ↦ a j.succ) m n).inv) ≫
        HomologicalComplex.ιTensorObj K L (-1) (-(n : ℤ))
          (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
        koszulJoinGraded r a m (-((n + 1 : ℕ) : ℤ)) ≫ t.hom)
          (headTensor 1 r n headOne y) :
          ExteriorAlgebra A (Fin (r + 1) →₀ A)) = _
      dsimp only [K, L, t]
      exact (join_formula_coe r a m 1 n (n + 1) (by omega)
        (headTensor 1 r n headOne y)).trans ((join_one_coe r n y).trans (by
          change _ = ExteriorAlgebra.ι A (Finsupp.single 0 1) *
            (exteriorPower.map n (koszulTailInclusion r) y).val
          rw [KoszulHeadSplit.exterior_map_coe]))
    simpa only [Category.assoc, h0, h1, KoszulHeadSplit.headAssembly] using
      KoszulHeadSplit.headAssembly_bijective A r n
  exact (Function.Bijective.of_comp_iff' t.toLinearEquiv.bijective _).mp hb

private theorem join_zero (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) :
    Function.Bijective (koszulJoinGraded r a m 0).hom := by
  let K := completedKoszulPower 1 (fun _ ↦ a 0) m
  let L := completedKoszulPower r (fun j ↦ a j.succ) m
  let e0 := (headTensor 0 r 0 (headZero (A := A))).toModuleIso ≪≫
    ((termIso 1 (fun _ ↦ a 0) m 0).symm ⊗ᵢ
      (termIso r (fun j ↦ a j.succ) m 0).symm)
  have hz : IsZero (ModuleCat.of A PUnit : ModuleCat.{u + 1} A) :=
    ModuleCat.isZero_of_subsingleton _
  have hL : IsZero (K.X (-1) ⊗ L.X 1) :=
    (MonoidalCategory.tensorLeft (K.X (-1))).map_isZero
      (power_isZero_pos r (fun j ↦ a j.succ) m 1 (by omega))
  let e1 := hz.iso hL
  let t := termIso (r + 1) a m 0
  have hb : Function.Bijective (koszulJoinGraded r a m 0 ≫ t.hom).hom := by
    apply tensor_test_bijective K L 0 0 1 (by omega) (by omega)
      (head_isZero (fun _ ↦ a 0) m) _ _ _ e0 e1
    have h0 :
        (e0.hom ≫ HomologicalComplex.ιTensorObj K L 0 0 0 (by omega) ≫
          koszulJoinGraded r a m 0 ≫ t.hom).hom =
        exteriorPower.map 0 (koszulTailInclusion r) := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      change ((((termIso 1 (fun _ ↦ a 0) m 0).inv ⊗ₘ
          (termIso r (fun j ↦ a j.succ) m 0).inv) ≫
        HomologicalComplex.ιTensorObj K L 0 0 0 (by omega) ≫
        koszulJoinGraded r a m 0 ≫ t.hom) (headTensor 0 r 0 headZero y) :
          ExteriorAlgebra A (Fin (r + 1) →₀ A)) = _
      dsimp only [K, L, t]
      exact (join_formula_coe r a m 0 0 0 rfl
        (headTensor 0 r 0 headZero y)).trans ((join_zero_coe r 0 y).trans
          (KoszulHeadSplit.exterior_map_coe A _ _ _).symm)
    have h1 :
        (e1.hom ≫ HomologicalComplex.ιTensorObj K L (-1) 1 0 (by omega) ≫
          koszulJoinGraded r a m 0 ≫ t.hom).hom = 0 := by
      ext y
      have hy : y = 0 := Subsingleton.elim _ _
      rw [hy]
      simp
    have hm : Function.Bijective (exteriorPower.map 0 (koszulTailInclusion (A := A) r)) := by
      have hn := exteriorPower.zeroEquiv_naturality (koszulTailInclusion (A := A) r)
      apply (Function.Bijective.of_comp_iff'
        (exteriorPower.zeroEquiv A (Fin (r + 1) →₀ A)).bijective _).mp
      change Function.Bijective ((exteriorPower.zeroEquiv A (Fin (r + 1) →₀ A)).toLinearMap.comp
        (exteriorPower.map 0 (koszulTailInclusion r)))
      rw [hn]
      exact (exteriorPower.zeroEquiv A (Fin r →₀ A)).bijective
    simp only [h0, h1]
    constructor
    · intro x y h
      apply Prod.ext
      · apply hm.injective
        simpa only [LinearMap.coprod_apply, LinearMap.zero_apply, add_zero] using h
      · exact Subsingleton.elim _ _
    · intro y
      obtain ⟨x, hx⟩ := hm.surjective y
      exact ⟨(x, 0), by simpa using hx⟩
  exact (Function.Bijective.of_comp_iff' t.toLinearEquiv.bijective _).mp hb

/-- Exterior projection and contraction split each negative-degree target into
its head-free and head-containing summands. The tensor coproduct has exactly these
surviving summands. Degree zero instead uses naturality of the zeroth exterior
power. This includes rank zero, the zero ring, and exterior degrees above the rank.
Source: Stacks Project, Tags 0628 and 0664.
(blueprint: new-weil-pbc-koszul-join-graded-nonpositive). -/
theorem koszulJoinGraded_bijective_of_nonpositive
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (i : ℤ) (hi : i ≤ 0) :
    Function.Bijective (koszulJoinGraded r a m i).hom := by
  by_cases h0 : i = 0
  · subst i
    exact join_zero r a m
  · have hn : i = -((((-i).toNat - 1) + 1 : ℕ) : ℤ) := by omega
    rw [hn]
    exact join_negative r a m ((-i).toNat - 1)

end AlgebraicGeometry.Scheme
