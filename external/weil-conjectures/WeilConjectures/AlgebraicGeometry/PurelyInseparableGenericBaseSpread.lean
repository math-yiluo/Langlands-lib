/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-! # Affine steps in the radicial generic field construction

Source: Stacks Project, Tags 0559 and 030R. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

private theorem fraction_at_generic {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (η : S) (hη : IsGenericPoint η Set.univ) :
    let := (S.Γevaluation η).hom.toAlgebra
    IsFractionRing Γ(S, ⊤) (S.residueField η) := by
  have heq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  let := (S.Γevaluation (genericPoint S)).hom.toAlgebra
  have : Nonempty (⊤ : S.Opens) := ⟨⟨genericPoint S, trivial⟩⟩
  have : IsFractionRing Γ(S, ⊤) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  let er : S.functionField ≃+* S.residueField (genericPoint S) :=
    RingEquiv.ofBijective (S.residue (genericPoint S)).hom
      ⟨RingHom.injective _, S.residue_surjective (genericPoint S)⟩
  let ea : S.functionField ≃ₐ[Γ(S, ⊤)] S.residueField (genericPoint S) :=
    { er with commutes' a := rfl }
  exact IsFractionRing.of_algEquiv ea

-- Clearing a denominator puts every extension element in the fraction field of the model.
private theorem perfectClosure_fractionRing
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsPurelyInseparable K L]
    (p : ℕ) [ExpChar K p] [ExpChar L p] :
    IsFractionRing (Subalgebra.perfectClosure A L p) L := by
  let B := Subalgebra.perfectClosure A L p
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K p x
  obtain ⟨a, d, hd, had⟩ := IsFractionRing.div_surjective A y
  have hdL : algebraMap A L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero (algebraMap K L)).mpr (by
      simpa using (IsFractionRing.injective A K).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp hd))
  have hscaled : (algebraMap A L d * x) ^ p ^ n =
      algebraMap A L (d ^ (p ^ n - 1) * a) := by
    rw [mul_pow, ← hy, ← had, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_mul, map_pow]
    have hp := expChar_pow_pos K p n
    rw [← Nat.sub_add_cancel hp, pow_succ]
    field_simp
    simp only [Nat.add_sub_cancel]
    ring
  let b : B := ⟨algebraMap A L d * x, n,
    d ^ (p ^ n - 1) * a, hscaled.symm⟩
  exact ⟨b, algebraMap A B d, by
    change x = (algebraMap A L d * x) / algebraMap A L d
    field_simp⟩

-- Root uniqueness is checked on field-valued points, including the exponent-one case.
private theorem perfectClosure_universalHomeomorphism
    (A L : Type u) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L))
    (p : ℕ) [ExpChar L p] :
    Algebra.IsUniversalHomeomorphism A (Subalgebra.perfectClosure A L p) := by
  let B := Subalgebra.perfectClosure A L p
  have hint : Algebra.IsIntegral A B := by
    constructor
    intro b
    obtain ⟨n, a, ha⟩ := b.property
    have hb : b ^ p ^ n = algebraMap A B a := by
      apply Subtype.val_injective
      exact ha.symm
    apply IsIntegral.of_pow (expChar_pow_pos L p n)
    rw [hb]
    exact isIntegral_algebraMap
  have hinjB : Function.Injective (algebraMap A B) := by
    intro a b hab
    exact hinj (congrArg (fun z : B ↦ (z : L)) hab)
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hinjB
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
    ((algebraMap_isIntegral_iff (R := A) (A := B)).mpr hint)
  have : Surjective f := ⟨Algebra.IsIntegral.comap_surjective A B⟩
  have : UniversallyInjective f := by
    refine ((tfae_universallyInjective f).out 2 1).mp ?_
    intro Ω _ g₁ g₂ hg
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
    simp only [f, ← Spec.map_comp] at hg
    have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
    congr 1
    ext b
    obtain ⟨n, a, ha⟩ := b.property
    have hb : b ^ p ^ n = algebraMap A B a := by
      apply Subtype.val_injective
      exact ha.symm
    have hpowers : ((Spec.preimage g₁).hom b) ^ p ^ n =
        ((Spec.preimage g₂).hom b) ^ p ^ n := by
      rw [← map_pow, ← map_pow, hb]
      exact RingHom.congr_fun hc a
    rcases expChar_is_prime_or_one L p with hp | hp
    · have : ExpChar A p := (algebraMap A L).expChar hinj p
      have : CharP A p := by
        cases (inferInstance : ExpChar A p) with
        | zero => exact (hp.ne_one rfl).elim
        | prime => infer_instance
      have : CharP Ω p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
        have hzero : (p : A) = 0 := CharP.cast_eq_zero A p
        simpa only [map_natCast, map_zero] using
          congrArg ((Spec.preimage g₁).hom.comp (algebraMap A B)) hzero)
      have : ExpChar Ω p := ExpChar.prime hp
      exact iterateFrobenius_inj Ω p n hpowers
    · simpa [hp] using hpowers
  exact ⟨{ }⟩

private theorem evaluation_congr_inv (S : Scheme.{u}) {x y : S} (h : x = y)
    (a : Γ(S, ⊤)) :
    (S.residueFieldCongr h).inv (S.Γevaluation y a) = S.Γevaluation x a := by
  cases h
  rfl

/-- Spread a finite purely inseparable extension of the generic residue field to an
integral affine universal homeomorphism, retaining its specified field embedding.
Source: Stacks Project, Tag 0559, second proof, construction of A'.
Proof: write S = Spec A and identify kappa(eta) with Frac A. Choose finitely many field
generators b_i of k'/kappa(eta). For each choose a characteristic-power equation
b_i^q = a_i/d_i. Replace b_i by d_i*b_i, whose q-th power is a_i*d_i^(q-1) in A.
Let A' be the A-subalgebra of k' generated by these scaled elements. It is a domain,
integral and finite over A, and its fraction field is k'. Every element of A' has a
purely inseparable power in A: choose a common characteristic power for its finitely many
coefficients and generators. Thus Spec A' -> Spec A is integral and universally injective;
lying over makes it surjective, hence a universal homeomorphism. The point over eta is
its zero prime. Its residue field is Frac A', giving the displayed ring equivalence and
compatibility. In characteristic zero the extension is trivial and one can take S itself.
(blueprint: lem-sbc-purely-inseparable-generic-base-spread) -/
theorem exists_purely_inseparable_generic_base_spread
    {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (k' : Type u) [Field k'] [Algebra (S.residueField η) k']
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k'] :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S),
      IsAffine S' ∧ IsIntegral S' ∧ IsUniversalHomeomorphism q ∧
      ∃ (η' : S') (hq : q η' = η),
        IsGenericPoint η' Set.univ ∧
        ∃ e : S'.residueField η' ≃+* k',
          e.toRingHom.comp
            (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
              algebraMap (S.residueField η) k' := by
  let A := Γ(S, ⊤)
  let K := S.residueField η
  let : Algebra A K := (S.Γevaluation η).hom.toAlgebra
  have : IsFractionRing A K := fraction_at_generic η hη
  let : Algebra A k' := ((algebraMap K k').comp (S.Γevaluation η).hom).toAlgebra
  have : IsScalarTower A K k' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let p := ringExpChar K
  have : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap K k').injective p
  -- The conclusion only requires an integral model, so use all power roots over A.
  let B := Subalgebra.perfectClosure A k' p
  have hinj : Function.Injective (algebraMap A k') :=
    (algebraMap K k').injective.comp (IsFractionRing.injective A K)
  have : IsFractionRing B k' := perfectClosure_fractionRing A K k' p
  have : Algebra.IsUniversalHomeomorphism A B :=
    perfectClosure_universalHomeomorphism A k' hinj p
  let T := Spec (.of B)
  let q : T ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ S.isoSpec.inv
  have : IsUniversalHomeomorphism q := inferInstance
  let η' := genericPoint T
  have hη' : IsGenericPoint η' Set.univ := genericPoint_spec T
  have hq : q η' = η := by
    apply (hη'.image q.continuous).eq
    simpa only [Set.image_univ, Set.range_eq_univ.mpr q.surjective, closure_univ] using hη
  let : Algebra Γ(T, ⊤) k' :=
    ((algebraMap B k').comp (Scheme.ΓSpecIso (.of B)).hom.hom).toAlgebra
  have : IsFractionRing Γ(T, ⊤) k' :=
    IsFractionRing.of_ringEquiv_left (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv
      (fun _ ↦ rfl)
  let : Algebra Γ(T, ⊤) (T.residueField η') := (T.Γevaluation η').hom.toAlgebra
  have : IsFractionRing Γ(T, ⊤) (T.residueField η') := fraction_at_generic η' hη'
  let e := IsLocalization.algEquiv (nonZeroDivisors Γ(T, ⊤)) (T.residueField η') k'
  refine ⟨T, q, inferInstance, inferInstance, inferInstance, η', hq, hη',
    e.toRingEquiv, ?_⟩
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  have heval := evaluation_congr_inv S hq a
  change e (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom
    ((S.Γevaluation η).hom a)) = algebraMap K k' ((S.Γevaluation η).hom a)
  rw [CommRingCat.comp_apply, heval, Scheme.Γevaluation_naturality_apply]
  change e (algebraMap Γ(T, ⊤) (T.residueField η') (q.appTop a)) = _
  rw [e.commutes]
  change algebraMap B k' ((Scheme.ΓSpecIso (.of B)).hom (q.appTop a)) = _
  have happ : q.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom =
      CommRingCat.ofHom (algebraMap A B) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ S.isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso (.of B)).hom = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    have htop : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso A).hom = 𝟙 A := by
      rw [← Scheme.toSpecΓ_appTop]
      change S.isoSpec.inv.appTop ≫ S.isoSpec.hom.appTop = _
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
      rfl
    rw [← Category.assoc]
    change (S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso A).hom) ≫
      CommRingCat.ofHom (algebraMap A B) = _
    rw [htop, Category.id_comp]
  rw [← CommRingCat.comp_apply, happ]
  rfl

end AlgebraicGeometry
