/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Principal localization and the naive cotangent complex

Source: Stacks Project, Algebra, Lemma 08JZ, statement and proof
(blueprint: lem-weil-pbc-principal-localization-naive-cotangent).
-/

@[expose] public section

universe u v w z

open TensorProduct MvPolynomial

namespace Algebra.Generators

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
/-- A polynomial presentation and its principal localization have the displayed conormal
and differential splittings. Source: Stacks Project, Algebra, Lemma 08JZ
(blueprint: lem-weil-pbc-principal-localization-naive-cotangent).

`P` bundles the surjection alpha from `A[x_s]` and a chosen section; its kernel is `P.ker`.
`localizationAway Bg g` sends its sole variable to `1/g`; its `comp P` is beta.
Its ring `A[x_s,x]` is the usual flattening of `P[x]`. Mathlib writes tensors with the
scalar extension on the left. Thus the degree-zero base change is
`Bg ⊗[B] (B ⊗[P.Ring] Ω[P.Ring⁄A])`, canonically `Bg ⊗[P.Ring] Ω[P.Ring⁄A]`.
The equivalences `e1`, `e2` give clauses (1), (2) with their specified generators;
`e0` and the commuting-square equation give the isomorphism of two-term complexes.

Proof, following the node's eight steps:
1. Apply lem-weil-pbc-polynomial-coefficient-map-kernel to alpha on coefficients and
lem-weil-pbc-localization-away-polynomial-quotient to `B[x] → Bg`. Their composite is beta
by def-weil-pbc-mv-polynomial-ring. Both are surjective. Lift a multiplier of `gx-1`
through the first map to show its inverse image is `I P[x] + (fx-1)`.
2. Use theorem-finite-etale-covers-proper-henselian--2 and tensor associativity:
the differential module splits into the old differentials and the free generator `dx`.
3. Inclusion of kernels induces the conormal map; extend its scalars to Bg. Step 1 shows
this image and the class of `fx-1` generate the new conormal module.
4. This inclusion after localization is injective by
lem-weil-pbc-principal-localization-conormal-injective. Its proof maps to `(P/I²)[1/f]`,
where the image of J is square-zero, so a class killed by J² vanishes after localization.
5. By def-weil-pbc-kahler-differentials, the differential on an old class is its old
differential. Leibniz gives `d(fx-1) = g⁻¹ df + g dx`; its dx-coordinate is g.
6. If an old class plus `b[fx-1]` vanishes, apply the dx-coordinate of its differential:
`bg = 0`. Since g is a unit, b = 0; then step 4 kills the old class. Together with
step 3 this proves clause (1), including its rank-one generator.
7. Replace dx by `g⁻² df + dx`. This change of basis fixes the old summand and sends
the differential of `[fx-1]` to g times the new generator. Hence the two equivalences
commute with the differential, proving clause (3).
8. Multiplication by g is bijective. Kernels and cokernels of a direct sum of maps are
the direct sums of their kernels and cokernels. The extra summand therefore has zero
kernel and cokernel, giving the injectivity equivalence and cokernel isomorphism. -/
theorem principal_localization_naive_cotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {S : Type w} (P : Generators A B S) (g : B) (f : P.Ring)
    (hf : algebraMap P.Ring B f = g)
    {Bg : Type z} [CommRing Bg] [Algebra B Bg] [Algebra A Bg]
    [IsScalarTower A B Bg] [IsLocalization.Away g Bg] :
    Function.Surjective (aeval (R := A) ((localizationAway Bg g).comp P).val) ∧
    ((localizationAway Bg g).comp P).ker =
      Ideal.map ((localizationAway Bg g).toComp P).toAlgHom.toRingHom P.ker ⊔
      Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} ∧
    ∃ (r : ((localizationAway Bg g).comp P).ker),
      r.val = rename Sum.inr f * X (Sum.inl ()) - 1 ∧
      ∃ (e1 : ((localizationAway Bg g).comp P).toExtension.Cotangent ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.Cotangent) × Bg)
        (e2 : ((localizationAway Bg g).comp P).toExtension.CotangentSpace ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.CotangentSpace) × Bg)
        (e0 : ((localizationAway Bg g).comp P).toExtension.CotangentSpace ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.CotangentSpace) × Bg),
        (∀ a b, e1.symm (a, b) =
          LinearMap.liftBaseChange Bg
            (Extension.Cotangent.map ((localizationAway Bg g).toComp P).toExtensionHom) a +
          b • Extension.Cotangent.mk r) ∧
        (∀ a b, e2.symm (a, b) =
          LinearMap.liftBaseChange Bg
            (Extension.CotangentSpace.map ((localizationAway Bg g).toComp P).toExtensionHom) a +
          b • ((1 : Bg) ⊗ₜ[((localizationAway Bg g).comp P).toExtension.Ring]
            KaehlerDifferential.D A ((localizationAway Bg g).comp P).toExtension.Ring
              (X (Sum.inl ())))) ∧
        (∀ a, e0.symm (a, 0) =
          LinearMap.liftBaseChange Bg
            (Extension.CotangentSpace.map ((localizationAway Bg g).toComp P).toExtensionHom) a) ∧
        (∀ a b, ((localizationAway Bg g).comp P).toExtension.cotangentComplex (e1.symm (a, b)) =
          e0.symm (P.toExtension.cotangentComplex.baseChange Bg a,
            algebraMap B Bg g * b)) ∧
        (Function.Injective (P.toExtension.cotangentComplex.baseChange Bg) ↔
          Function.Injective ((localizationAway Bg g).comp P).toExtension.cotangentComplex) ∧
        Nonempty (((Bg ⊗[B] P.toExtension.CotangentSpace) ⧸
            LinearMap.range (P.toExtension.cotangentComplex.baseChange Bg)) ≃ₗ[Bg]
          (((localizationAway Bg g).comp P).toExtension.CotangentSpace ⧸
            LinearMap.range ((localizationAway Bg g).comp P).toExtension.cotangentComplex)) := by
  classical
  -- Mathlib supplies the kernel and conormal splitting (steps 1, 3, 4, 6), and
  -- its composition basis supplies step 2 without a polynomial-extension lemma.
  let Q := localizationAway Bg g
  let W := Q.comp P
  have hker := comp_localizationAway_ker g P f hf (T := Bg)
  have hr : rename Sum.inr f * X (Sum.inl ()) - 1 ∈ W.ker := by
    rw [show W.ker = _ from hker]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  let r : W.ker := ⟨_, hr⟩
  have hx : Extension.Cotangent.map (Q.ofComp P).toExtensionHom
      (Extension.Cotangent.mk r) = cMulXSubOneCotangent Bg g := by
    rw [Extension.Cotangent.map_mk]
    apply congrArg Extension.Cotangent.mk
    apply Subtype.ext
    change (Q.ofComp P).toAlgHom (rename Sum.inr f * X (Sum.inl ()) - 1) =
      C g * X () - 1
    rw [map_sub, map_mul, map_one, toAlgHom_ofComp_rename, hf, Hom.toAlgHom_X]
    rfl
  let c := (basisCotangentAway Bg g).equivFun.trans (LinearEquiv.funUnique Unit Bg Bg)
  have hc (b : Bg) : c.symm b = b • cMulXSubOneCotangent Bg g := by
    simp [c, LinearEquiv.trans_symm, Module.Basis.equivFun_symm_apply,
      basisCotangentAway_apply, LinearEquiv.funUnique]
  let e1 := (cotangentCompLocalizationAwayEquiv g P hx).trans
    ((LinearEquiv.refl Bg _).prodCongr c)
  have he1 (a) (b) : e1.symm (a, b) =
      LinearMap.liftBaseChange Bg (Extension.Cotangent.map (Q.toComp P).toExtensionHom) a +
      b • Extension.Cotangent.mk r := by
    change (cotangentCompLocalizationAwayEquiv g P hx).symm (a, c.symm b) = _
    rw [hc, show (a, b • cMulXSubOneCotangent Bg g) =
      (a, 0) + b • (0, cMulXSubOneCotangent Bg g) by simp]
    rw [map_add, map_smul, cotangentCompLocalizationAwayEquiv_symm_inl,
      cotangentCompLocalizationAwayEquiv_symm_inr]
  let d := Q.cotangentSpaceBasis.equivFun.trans (LinearEquiv.funUnique Unit Bg Bg)
  let e2 := (CotangentSpace.compEquiv Q P).trans
    ((d.prodCongr (LinearEquiv.refl Bg _)).trans (LinearEquiv.prodComm Bg _ _))
  have hd (b : Bg) : d.symm b = b • Q.cotangentSpaceBasis () := by
    simp [d, LinearEquiv.trans_symm, Module.Basis.equivFun_symm_apply,
      LinearEquiv.funUnique]
  have hdx : (CotangentSpace.compEquiv Q P).symm (Q.cotangentSpaceBasis (), 0) =
      W.cotangentSpaceBasis (Sum.inl ()) := by
    dsimp only [W]
    apply (Q.comp P).cotangentSpaceBasis.repr.injective
    simp only [CotangentSpace.compEquiv, LinearEquiv.trans_symm,
      LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange Bg)).repr
      (Q.cotangentSpaceBasis (), 0) = W.cotangentSpaceBasis.repr
        (W.cotangentSpaceBasis (Sum.inl ()))
    rw [Module.Basis.repr_self]
    ext (i | i) <;> simp
  have he2 (a) (b) : e2.symm (a, b) =
      LinearMap.liftBaseChange Bg
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom) a +
      b • ((1 : Bg) ⊗ₜ[W.toExtension.Ring]
        KaehlerDifferential.D A W.toExtension.Ring (X (Sum.inl ()))) := by
    change (CotangentSpace.compEquiv Q P).symm (d.symm b, a) = _
    rw [hd, show (b • Q.cotangentSpaceBasis (), a) =
      (0, a) + b • (Q.cotangentSpaceBasis (), 0) by simp]
    rw [map_add, map_smul, CotangentSpace.compEquiv_symm_zero, hdx,
      cotangentSpaceBasis_apply]
    rfl
  let F := P.toExtension.cotangentComplex.baseChange Bg
  let D := W.toExtension.cotangentComplex
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Bg) g
  have hsnd : (e2 (D (Extension.Cotangent.mk r))).2 = algebraMap B Bg g := by
    change d ((CotangentSpace.compEquiv Q P (D (Extension.Cotangent.mk r))).1) = _
    rw [CotangentSpace.fst_compEquiv_apply, Extension.CotangentSpace.map_cotangentComplex, hx]
    change Q.cotangentSpaceBasis.repr
      (Q.toExtension.cotangentComplex (cMulXSubOneCotangent Bg g)) () = _
    rw [cMulXSubOneCotangent_eq, Extension.cotangentComplex_mk]
    have hrepr := Q.cotangentSpaceBasis_repr_one_tmul (C g * X () - 1) ()
    have heval : aeval Q.val (pderiv () (C g * X () - 1)) = algebraMap B Bg g := by
      simp [Q]
    exact hrepr.trans heval
  -- Adjust the differential complement so the relation maps to g times its generator.
  let v := (e2 (D (Extension.Cotangent.mk r))).1
  let k := (↑u⁻¹ : Bg) • v
  let t : ((Bg ⊗[B] P.toExtension.CotangentSpace) × Bg) ≃ₗ[Bg]
      (Bg ⊗[B] P.toExtension.CotangentSpace) × Bg :=
    { toFun := fun x ↦ (x.1 + x.2 • k, x.2)
      invFun := fun x ↦ (x.1 - x.2 • k, x.2)
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by
        intro x y
        apply Prod.ext
        · change (x.1 + y.1) + (x.2 + y.2) • k =
            (x.1 + x.2 • k) + (y.1 + y.2 • k)
          rw [add_smul, add_add_add_comm]
        · rfl
      map_smul' := by
        intro a x
        apply Prod.ext
        · change a • x.1 + (a * x.2) • k = a • (x.1 + x.2 • k)
          exact ((smul_add a x.1 (x.2 • k)).trans
            (congrArg (fun z ↦ a • x.1 + z) (smul_smul a x.2 k))).symm
        · rfl }
  let e0 := e2.trans t.symm
  have he0 (a) (b) : e0.symm (a, b) = e2.symm (a + b • k, b) := rfl
  have he00 (a) : e0.symm (a, 0) = LinearMap.liftBaseChange Bg
      (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom) a := by
    rw [he0]; simpa using he2 a 0
  have hDr : D (Extension.Cotangent.mk r) = e0.symm (0, algebraMap B Bg g) := by
    apply e2.injective
    rw [he0, e2.apply_symm_apply]
    apply Prod.ext
    · change v = 0 + algebraMap B Bg g • ((↑u⁻¹ : Bg) • v)
      rw [← hu, smul_smul, Units.mul_inv, one_smul, zero_add]
    · exact hsnd
  have hcomm (a) (b) : D (e1.symm (a, b)) =
      e0.symm (F a, algebraMap B Bg g * b) := by
    rw [he1, map_add, map_smul]
    have hnat := DFunLike.congr_fun (H1Cotangent.map_comp_cotangentComplex_baseChange Q P) a
    change LinearMap.liftBaseChange Bg
      (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom) (F a) =
      D (LinearMap.liftBaseChange Bg
        (Extension.Cotangent.map (Q.toComp P).toExtensionHom) a) at hnat
    rw [← hnat, ← he00, hDr, ← map_smul]
    rw [← map_add]
    congr 1
    simp [smul_eq_mul, mul_comm]
  refine ⟨W.aeval_val_surjective, hker, r, rfl, e1, e2, e0,
    he1, he2, he00, hcomm, ?_, ?_⟩
  · constructor
    · intro h x y hxy
      have hp := congrArg e0 hxy
      have hdiag (z) : e0 (D z) = (F (e1 z).1, algebraMap B Bg g * (e1 z).2) := by
        obtain ⟨⟨a, b⟩, rfl⟩ := e1.symm.surjective z
        rw [hcomm, e0.apply_symm_apply, e1.apply_symm_apply]
      rw [hdiag, hdiag] at hp
      apply e1.injective
      apply Prod.ext
      · exact h (congrArg Prod.fst hp)
      · have hb := congrArg Prod.snd hp
        change algebraMap B Bg g * (e1 x).2 = algebraMap B Bg g * (e1 y).2 at hb
        rw [← hu] at hb
        exact u.isUnit.mul_left_cancel hb
    · intro h x y hxy
      have hd : D (e1.symm (x, 0)) = D (e1.symm (y, 0)) := by
        rw [hcomm, hcomm, hxy]
      exact congrArg Prod.fst (e1.symm.injective (h hd))
  -- Projection to the old cokernel is surjective and has kernel exactly range D.
  · let q := LinearMap.range F
    let φ := q.mkQ.comp ((LinearMap.fst Bg _ Bg).comp e0.toLinearMap)
    have hφ (x) : φ x = q.mkQ (e0 x).1 := rfl
    have hsurj : Function.Surjective φ := by
      intro x
      obtain ⟨a, rfl⟩ := q.mkQ_surjective x
      refine ⟨e0.symm (a, 0), ?_⟩
      rw [hφ, e0.apply_symm_apply]
    have hkerφ : LinearMap.ker φ = LinearMap.range D := by
      ext x
      constructor
      · intro hx
        have ha : (e0 x).1 ∈ q := by
          simpa only [LinearMap.mem_ker, hφ, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero] using hx
        obtain ⟨a, ha⟩ := ha
        refine ⟨e1.symm (a, (↑u⁻¹ : Bg) * (e0 x).2), ?_⟩
        apply e0.injective
        rw [hcomm, e0.apply_symm_apply]
        apply Prod.ext
        · exact ha
        · change algebraMap B Bg g * ((↑u⁻¹ : Bg) * (e0 x).2) = (e0 x).2
          rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
      · rintro ⟨a, rfl⟩
        obtain ⟨⟨a, b⟩, rfl⟩ := e1.symm.surjective a
        rw [LinearMap.mem_ker, hφ, hcomm, e0.apply_symm_apply]
        exact (Submodule.Quotient.mk_eq_zero q).mpr ⟨a, rfl⟩
    exact ⟨((Submodule.quotEquivOfEq (LinearMap.range D) (LinearMap.ker φ) hkerφ.symm).trans
      (φ.quotKerEquivOfSurjective hsurj)).symm⟩

end Algebra.Generators
