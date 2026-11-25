/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.PrimitiveRootsCover
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.Mathlib.LinearAlgebra.Lagrange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Compatible primitive roots on one pro-étale cover
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite Polynomial
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The actual abelian root diagram before applying the free integral module functor. -/
noncomputable def tateRootsSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (fun n ↦ eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

private theorem exists_unit_pow_eq
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (ℓ : ℕ) (hℓ₀ : ℓ ≠ 0) (hℓ : IsUnit (ℓ : R)) (a : Rˣ) :
    ∃ b : Rˣ, b ^ ℓ = a := by
  let f : R[X] := X ^ ℓ - C (a : R)
  let S := AdjoinRoot f
  have : Algebra.Etale R S := AdjoinRoot.etale_X_pow_sub_C hℓ₀ hℓ a.isUnit
  have hdeg : f.degree ≠ 0 := by
    nontriviality R
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hℓ₀)]
    exact_mod_cast hℓ₀
  have : Module.FaithfullyFlat R S :=
    AdjoinRoot.faithfullyFlat_of_monic (monic_X_pow_sub_C _ hℓ₀) hdeg
  let p := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : Etale p := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective p :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing p
  let r : S →+* R := (Spec.preimage s).hom
  have hr : r.comp (algebraMap R S) = RingHom.id R := by
    have h : CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage s = 𝟙 _ := by
      apply Spec.map_injective
      simpa [p] using hs
    exact congrArg CommRingCat.Hom.hom h
  have hs : AdjoinRoot.root f ^ ℓ = algebraMap R S (a : R) := by
    change AdjoinRoot.root f ^ ℓ = AdjoinRoot.of f (a : R)
    have h := AdjoinRoot.eval₂_root f
    simpa [f, sub_eq_zero] using h
  have hb : r (AdjoinRoot.root f) ^ ℓ = (a : R) := by
    rw [← map_pow, hs]
    exact RingHom.congr_fun hr a
  have hu : IsUnit (r (AdjoinRoot.root f)) :=
    (isUnit_pow_iff hℓ₀).mp (hb ▸ a.isUnit)
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  simpa using hb

private theorem exists_first_primitive
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (ℓ : ℕ) (hℓ₀ : ℓ ≠ 0) (hℓ : IsUnit (ℓ : R)) :
    ∃ z : Rˣ, z ^ ℓ = 1 ∧
      ∀ i < ℓ, ∀ j < ℓ, i ≠ j → IsUnit ((z : R) ^ i - (z : R) ^ j) := by
  have : Etale (primitiveRootsCover R ℓ) := etale_primitiveRootsCover R ℓ hℓ₀ hℓ
  have : Surjective (primitiveRootsCover R ℓ) := ⟨surjective_primitiveRootsCover R ℓ hℓ⟩
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (primitiveRootsCover R ℓ)
  let r := (Spec.preimage s).hom
  let a := PrimitiveRootsAlgebra.zeta R ℓ
  have ha : IsUnit a := PrimitiveRootsAlgebra.isUnit_zeta R ℓ (Nat.pos_of_ne_zero hℓ₀)
  refine ⟨(ha.map r).unit, ?_, ?_⟩
  · apply Units.ext
    simpa [← map_pow] using congrArg r (PrimitiveRootsAlgebra.zeta_pow R ℓ)
  · intro i hi j hj hij
    simpa [← map_pow, ← map_sub] using
      (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow R ℓ hi hj hij).map r

private theorem isUnit_of_field_images
    (R : Type u) [CommRing R] (a : R)
    (h : ∀ (K : Type u) [Field K] (φ : R →+* K), φ a ≠ 0) : IsUnit a := by
  by_contra hunit
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    (Ideal.span_singleton_ne_top hunit)
  have := hm
  let := Ideal.Quotient.field m
  exact h (R ⧸ m) (Ideal.Quotient.mk m)
    ((Ideal.Quotient.eq_zero_iff_mem).mpr (hle (Ideal.subset_span (Set.mem_singleton a))))

private theorem exists_primitive_unit_tower
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : R)) :
    ∃ z : ℕ → Rˣ, z 0 = 1 ∧ (∀ n, z (n + 1) ^ ℓ = z n) ∧
      (∀ n, z n ^ (ℓ ^ n) = 1) ∧
      (∀ n i, i < ℓ ^ n → ∀ j, j < ℓ ^ n → i ≠ j →
        IsUnit ((z n : R) ^ i - (z n : R) ^ j)) := by
  classical
  have hp : ℓ.Prime := Fact.out
  obtain ⟨z₁, hz₁, hdiff⟩ := exists_first_primitive R ℓ hp.ne_zero hℓ
  have hroot := exists_unit_pow_eq R ℓ hp.ne_zero hℓ
  choose step hstep using hroot
  let w : ℕ → Rˣ := fun n ↦ step^[n] z₁
  have hw (n : ℕ) : w (n + 1) ^ ℓ = w n := by
    change step^[n + 1] z₁ ^ ℓ = step^[n] z₁
    rw [Function.iterate_succ_apply']
    exact hstep _
  have hw0 : w 0 = z₁ := rfl
  have hpow (n : ℕ) : w n ^ (ℓ ^ n) = z₁ := by
    induction n with
    | zero => simp [w]
    | succ n ih => rw [pow_succ', pow_mul, hw, ih]
  have hprim (n : ℕ) (K : Type u) [Field K] (φ : R →+* K) :
      IsPrimitiveRoot (φ (w n : R)) (ℓ ^ (n + 1)) := by
    have hn1 : φ (z₁ : R) ≠ 1 := by
      have hu := (hdiff 0 hp.pos 1 hp.one_lt (by omega)).map φ
      have : (1 : K) - φ (z₁ : R) ≠ 0 := by
        simpa only [map_sub, map_pow, pow_zero, pow_one, map_one] using hu.ne_zero
      exact (sub_ne_zero.mp this).symm
    apply IsPrimitiveRoot.iff_orderOf.mpr
    apply orderOf_eq_prime_pow
    · rw [← map_pow]
      have : (w n : R) ^ (ℓ ^ n) = (z₁ : R) := congrArg Units.val (hpow n)
      rwa [this]
    · rw [pow_succ, pow_mul, ← map_pow]
      have : (w n : R) ^ (ℓ ^ n) = (z₁ : R) := congrArg Units.val (hpow n)
      rw [this, ← map_pow]
      simpa using congrArg (fun a : Rˣ ↦ φ (a : R)) hz₁
  let z : ℕ → Rˣ
    | 0 => 1
    | n + 1 => w n
  refine ⟨z, rfl, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hz₁
    | succ n => exact hw n
  · intro n
    cases n with
    | zero => simp [z]
    | succ n =>
      change w n ^ (ℓ ^ (n + 1)) = 1
      rw [pow_succ, pow_mul, hpow, hz₁]
  · intro n i hi j hj hij
    cases n with
    | zero => simp only [pow_zero] at hi hj; omega
    | succ n =>
      apply isUnit_of_field_images
      intro K _ φ
      rw [map_sub, map_pow, map_pow, sub_ne_zero]
      exact fun h ↦ hij ((hprim n K φ).pow_inj hi hj h)

private noncomputable def rootZModHom {X : Scheme.{u}} (n : ℕ)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) ⟶
      (CommRingCat.rootsOfUnityFunctor n).obj Γ(X, ⊤) := by
  let r : rootsOfUnity n Γ(X, ⊤) := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζ⟩
  have hr : r ^ n = 1 := Subtype.ext hζ
  let f : ZMod n →+ Additive (rootsOfUnity n Γ(X, ⊤)) :=
    ZMod.lift n ⟨zmultiplesHom _ (Additive.ofMul r), by simp [← ofMul_pow, hr]⟩
  exact AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (f.comp AddEquiv.ulift.toAddMonoidHom))

private lemma rootZModHom_natCast {X : Scheme.{u}} (n : ℕ)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (a : ℕ) :
    (((rootZModHom n ζ hζ) (ULift.up (a : ZMod n))).down.toMul : Γ(X, ⊤)ˣ) = ζ ^ a := by
  let r : rootsOfUnity n Γ(X, ⊤) := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζ⟩
  have hr : r ^ n = 1 := Subtype.ext hζ
  let f : ZMod n →+ Additive (rootsOfUnity n Γ(X, ⊤)) :=
    ZMod.lift n ⟨zmultiplesHom _ (Additive.ofMul r), by simp [← ofMul_pow, hr]⟩
  change (f (a : ZMod n)).toMul.val = ζ ^ a
  dsimp only [f]
  rw [show ((a : ℕ) : ZMod n) = ((a : ℤ) : ZMod n) from (Int.cast_natCast a).symm,
    ZMod.lift_coe]
  simp [← ofMul_pow, r]

private noncomputable def zmodToRootsPresheaf (X : Scheme.{u}) (n : ℕ)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶
      rootsOfUnityPresheaf X n where
  app U := rootZModHom n ζ hζ ≫ (rootsOfUnityPresheaf X n).map
    ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).from U.unop).op
  naturality U V g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    congr 3
    exact (MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).hom_ext _ _

private lemma zmodToRootsPresheaf_app_natCast {X : Scheme.{u}} (n : ℕ)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (U : X.ProEtᵒᵖ) (a : ℕ) :
    ((zmodToRootsPresheaf X n ζ hζ).app U (ULift.up (a : ZMod n))).down.toMul.val.val =
      U.unop.hom.appTop (ζ : Γ(X, ⊤)) ^ a := by
  have h : ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).from U.unop).left =
      U.unop.hom := (Category.comp_id _).symm.trans
        (MorphismProperty.Over.w ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).from U.unop))
  change ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale X).from U.unop).left.appTop
    ((rootZModHom n ζ hζ) (ULift.up (a : ZMod n))).down.toMul.val.val = _
  rw [h, rootZModHom_natCast, Units.val_pow_eq_pow_val, map_pow]
  rfl

private lemma rootsPresheaf_map_val {X : Scheme.{u}} (n : ℕ) {U V : X.ProEt}
    (g : V ⟶ U) (x : (rootsOfUnityPresheaf X n).obj (op U)) :
    ((rootsOfUnityPresheaf X n).map g.op x).down.toMul.val.val =
      g.left.appTop x.down.toMul.val.val := rfl

private lemma isLocallyInjective_zmodToRootsPresheaf {X : Scheme.{u}} (n : ℕ) [NeZero n]
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    Presheaf.IsLocallyInjective (ProEt.topology X) (zmodToRootsPresheaf X n ζ hζ) where
  equalizerSieve_mem {U} a b hab := by
    by_cases hab' : a = b
    · subst hab'
      simp
    have : Subsingleton Γ(U.unop.left, ⊤) := by
      let ρ : Γ(X, ⊤) →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom
      have e := congrArg (fun z : (rootsOfUnityPresheaf X n).obj U ↦
        z.down.toMul.val.val) hab
      obtain ⟨i⟩ := a
      obtain ⟨j⟩ := b
      have hij : i.val ≠ j.val := fun hij ↦ hab' (congrArg ULift.up (ZMod.val_injective n hij))
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j,
        zmodToRootsPresheaf_app_natCast, zmodToRootsPresheaf_app_natCast] at e
      have e' : ρ ((ζ : Γ(X, ⊤)) ^ i.val - (ζ : Γ(X, ⊤)) ^ j.val) = 0 := by
        rw [map_sub, map_pow, map_pow]
        exact sub_eq_zero.2 e
      obtain ⟨c, hc⟩ := hζ' i.val (ZMod.val_lt i) j.val (ZMod.val_lt j) hij
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_one ρ, ← c.mul_inv, hc, map_mul, e', zero_mul]
    have := Scheme.isEmpty_of_subsingleton_Γ this
    refine GrothendieckTopology.superset_covering _ ?_ (ProEt.bot_mem_topology U.unop)
    rintro _ _ ⟨⟩

private lemma isLocallySurjective_zmodToRootsPresheaf {X : Scheme.{u}} (n : ℕ) [NeZero n]
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    Presheaf.IsLocallySurjective (ProEt.topology X) (zmodToRootsPresheaf X n ζ hζ) where
  imageSieve_mem {U} x := by
    classical
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    let ρ : Γ(X, ⊤) →+* Γ(U.left, ⊤) := U.hom.appTop.hom
    let z : Γ(X, ⊤) := ζ
    have hz : z ^ n = 1 := by simpa [z] using congrArg Units.val hζ
    let t : Γ(U.left, ⊤) := x.down.toMul.val.val
    have ht : t ^ n = 1 := by
      exact congrArg Units.val ((mem_rootsOfUnity _ _).mp x.down.toMul.property)
    let R := Finset.range n
    let y : R → Γ(U.left, ⊤) := fun r ↦ ∏ s ∈ R.erase r, (t - ρ (z ^ s))
    let D : R → U.left.Opens := fun r ↦ U.left.basicOpen (y r)
    let g : ∀ r : R, ProEt.ofOpenImmersion U (D r).ι ⟶ U :=
      fun r ↦ ProEt.ofOpenImmersionHom U (D r).ι
    apply ProEt.mem_topology_of_openImmersion (X := X) (U := U)
      (ι := ULift.{u} R) _ (fun r ↦ (D r.down).ι)
    · have hspan : Ideal.span (Set.range y) = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        have hsum := congrArg (Polynomial.eval₂ ρ t)
          (Polynomial.sum_inverse_mul_prod_erase_eq_one hn hζ')
        simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_one] at hsum
        rw [← hsum]
        exact Ideal.sum_mem _ fun r hr ↦
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
      have hcov := iSup_basicOpen_of_span_eq_top (X := U.left) ⊤ _ hspan
      intro p
      have hp : p ∈ (⨆ i ∈ Set.range y, U.left.basicOpen i) := by
        rw [hcov]; exact TopologicalSpace.Opens.mem_top p
      simp only [TopologicalSpace.Opens.mem_iSup] at hp
      obtain ⟨_, ⟨r, rfl⟩, hpr⟩ := hp
      refine ⟨ULift.up r, ?_⟩
      rw [Scheme.Opens.range_ι]
      exact hpr
    · rintro ⟨r⟩
      refine ⟨ULift.up ((r : ℕ) : ZMod n), ?_⟩
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      refine (zmodToRootsPresheaf_app_natCast n ζ hζ _ r).trans
        (Eq.trans ?_ (rootsPresheaf_map_val n (g r) x).symm)
      change ((D r).ι ≫ U.hom).appTop (ζ : Γ(X, ⊤)) ^ (r : ℕ) = (D r).ι.appTop t
      have hprod := congrArg (Polynomial.eval₂ ρ t)
        (Polynomial.X_pow_sub_one_eq_prod_of_isUnit_sub hn hz hζ')
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ht,
        sub_self, Polynomial.eval₂_finsetProd, Polynomial.eval₂_X, Polynomial.eval₂_C] at hprod
      rw [← Finset.prod_erase_mul _ _ r.2] at hprod
      have h0 := congrArg (D r).ι.appTop hprod.symm
      rw [map_mul, map_zero, (U.left.isUnit_ι_appTop_basicOpen (y r)).mul_right_eq_zero,
        map_sub, sub_eq_zero] at h0
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h0, map_pow, map_pow]
      rfl

private noncomputable def constantRootsIso {X : Scheme.{u}} (n : ℕ) [NeZero n]
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≅ rootsOfUnitySheaf X n := by
  have := isLocallyInjective_zmodToRootsPresheaf n ζ hζ hζ'
  have := isLocallySurjective_zmodToRootsPresheaf n ζ hζ hζ'
  have h := (ProEt.topology X).W_of_isLocallyBijective (zmodToRootsPresheaf X n ζ hζ)
  have : IsIso ((presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
      (zmodToRootsPresheaf X n ζ hζ)) := (GrothendieckTopology.W_iff _ _).mp h
  exact asIso ((presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
    (zmodToRootsPresheaf X n ζ hζ))

private noncomputable def rawRootsTransition (X : Scheme.{u}) (ℓ n : ℕ) :
    rootsOfUnityPresheaf X (ℓ ^ (n + 1)) ⟶ rootsOfUnityPresheaf X (ℓ ^ n) :=
  eqToHom (by rw [pow_succ']; rfl) ≫
    Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow (ℓ ^ n) ℓ)

private noncomputable def rawRootsSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ rootsOfUnityPresheaf X (ℓ ^ n))
    (rawRootsTransition X ℓ)

private noncomputable def rawResidues (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (integralResidueAbTransition.{u} ℓ) ⋙ Functor.const X.ProEtᵒᵖ

private noncomputable def rootsSheafificationIso (X : Scheme.{u}) (ℓ : ℕ) :
    rawRootsSystem X ℓ ⋙ presheafToSheaf (ProEt.topology X) Ab.{u + 1} ≅
      tateRootsSystem X ℓ := by
  let t : rawRootsSystem X ℓ ⋙ presheafToSheaf (ProEt.topology X) Ab.{u + 1} ⟶
      tateRootsSystem X ℓ := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp only [rawRootsSystem, tateRootsSystem, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
        simp [rawRootsTransition, rootsOfUnitySheafPow, Functor.map_comp, eqToHom_map])
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private lemma rootsEqToHom_val {X : Scheme.{u}} {a b : ℕ} (h : a = b)
    (U : X.ProEtᵒᵖ) (x : (rootsOfUnityPresheaf X a).obj U) :
    ((eqToHom (congrArg (rootsOfUnityPresheaf X) h)).app U x).down.toMul.val.val =
      x.down.toMul.val.val := by
  subst b
  rfl

private lemma rawRootsTransition_val (X : Scheme.{u}) (ℓ n : ℕ)
    (U : X.ProEtᵒᵖ) (x : (rootsOfUnityPresheaf X (ℓ ^ (n + 1))).obj U) :
    ((rawRootsTransition X ℓ n).app U x).down.toMul.val.val =
      x.down.toMul.val.val ^ ℓ := by
  change (((eqToHom (congrArg (rootsOfUnityPresheaf X) (pow_succ' ℓ n))).app U
    x).down.toMul.val.val) ^ ℓ = _
  rw [rootsEqToHom_val (pow_succ' ℓ n)]

private noncomputable def rawRootsBasis (Y : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (z : ℕ → Γ(Y, ⊤)ˣ) (hz : ∀ n, z n ^ (ℓ ^ n) = 1)
    (hstep : ∀ n, z (n + 1) ^ ℓ = z n) :
    rawResidues Y ℓ ⟶ rawRootsSystem Y ℓ :=
  NatTrans.ofOpSequence (fun n ↦ zmodToRootsPresheaf Y (ℓ ^ n) (z n) (hz n))
    (fun n ↦ by
      simp only [rawResidues, rawRootsSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      ext U a
      obtain ⟨a⟩ := a
      rw [← ZMod.natCast_zmod_val a]
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change ((zmodToRootsPresheaf Y (ℓ ^ n) (z n) (hz n)).app U
        ((integralResidueAbTransition ℓ n)
          (ULift.up (a.val : ZMod (ℓ ^ (n + 1)))))).down.toMul.val.val =
        (((rawRootsTransition Y ℓ n).app U
          ((zmodToRootsPresheaf Y (ℓ ^ (n + 1)) (z (n + 1)) (hz (n + 1))).app U
            (ULift.up (a.val : ZMod (ℓ ^ (n + 1)))))).down.toMul.val.val)
      rw [rawRootsTransition_val, zmodToRootsPresheaf_app_natCast]
      have hc : (integralResidueAbTransition.{u} ℓ n)
          (ULift.up (a.val : ZMod (ℓ ^ (n + 1)))) = ULift.up (a.val : ZMod (ℓ ^ n)) := by
        apply ULift.ext
        change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))
          (a.val : ZMod (ℓ ^ (n + 1))) = (a.val : ZMod (ℓ ^ n))
        exact map_natCast _ _
      rw [hc, zmodToRootsPresheaf_app_natCast, ← pow_mul, mul_comm a.val ℓ, pow_mul]
      have h := congrArg (fun t : Γ(Y, ⊤)ˣ ↦ U.unop.hom.appTop (t : Γ(Y, ⊤))) (hstep n)
      simpa only [Units.val_pow_eq_pow_val, map_pow] using congrArg (fun t ↦ t ^ a.val) h.symm)

private noncomputable def rootsBasisIso (Y : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (z : ℕ → Γ(Y, ⊤)ˣ) (hz : ∀ n, z n ^ (ℓ ^ n) = 1)
    (hstep : ∀ n, z (n + 1) ^ ℓ = z n)
    (hdiff : ∀ n i, i < ℓ ^ n → ∀ j, j < ℓ ^ n → i ≠ j →
      IsUnit ((z n : Γ(Y, ⊤)) ^ i - (z n : Γ(Y, ⊤)) ^ j)) :
    constantTateResidueSystem Y ℓ ≅ tateRootsSystem Y ℓ := by
  let S := presheafToSheaf (ProEt.topology Y) Ab.{u + 1}
  let t := Functor.whiskerRight (rawRootsBasis Y ℓ z hz hstep) S
  have : ∀ n, IsIso (t.app n) := fun n ↦ inferInstanceAs
    (IsIso (constantRootsIso (ℓ ^ n.unop) (z n.unop) (hz n.unop) (hdiff n.unop)).hom)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t ≪≫ rootsSheafificationIso Y ℓ

private noncomputable def rawRootsRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) (ℓ : ℕ) :
    rawRootsSystem X ℓ ⋙ (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (MorphismProperty.Over.map ⊤ hf).op ≅ rawRootsSystem Y ℓ := by
  let t : rawRootsSystem X ℓ ⋙ (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (MorphismProperty.Over.map ⊤ hf).op ⟶ rawRootsSystem Y ℓ :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [rawRootsSystem, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      simp only [rawRootsTransition, Functor.map_comp, eqToHom_map]
      rfl)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private noncomputable def rawResiduesRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) (ℓ : ℕ) :
    rawResidues X ℓ ⋙ (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (MorphismProperty.Over.map ⊤ hf).op ≅ rawResidues Y ℓ := by
  let t : rawResidues X ℓ ⋙ (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (MorphismProperty.Over.map ⊤ hf).op ⟶ rawResidues Y ℓ :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [rawResidues, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private noncomputable def restrictionSheafificationIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) :
    presheafToSheaf (ProEt.topology X) Ab.{u + 1} ⋙ upperStar Ab.{u + 1} f ≅
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (MorphismProperty.Over.map ⊤ hf).op ⋙
        presheafToSheaf (ProEt.topology Y) Ab.{u + 1} :=
  Functor.isoWhiskerLeft _ (upperStarIsoLocalizationRestriction Ab.{u + 1} f hf) ≪≫
    ((MorphismProperty.Over.map ⊤ hf).pushforwardContinuousSheafificationCompatibility
      Ab.{u + 1} (ProEt.topology Y) (ProEt.topology X)).symm

private noncomputable def rootsRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) (ℓ : ℕ) :
    tateRootsSystem X ℓ ⋙ upperStar Ab.{u + 1} f ≅ tateRootsSystem Y ℓ := by
  let S := presheafToSheaf (ProEt.topology X) Ab.{u + 1}
  let T := presheafToSheaf (ProEt.topology Y) Ab.{u + 1}
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
    (MorphismProperty.Over.map ⊤ hf).op
  exact Functor.isoWhiskerRight (rootsSheafificationIso X ℓ).symm _ ≪≫
    Functor.associator (rawRootsSystem X ℓ) S _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionSheafificationIso f hf) ≪≫
    (Functor.associator (rawRootsSystem X ℓ) W T).symm ≪≫
    Functor.isoWhiskerRight (rawRootsRestrictionIso f hf ℓ) T ≪≫
    rootsSheafificationIso Y ℓ

private noncomputable def residuesRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) (ℓ : ℕ) :
    constantTateResidueSystem X ℓ ⋙ upperStar Ab.{u + 1} f ≅
      constantTateResidueSystem Y ℓ := by
  let S := presheafToSheaf (ProEt.topology X) Ab.{u + 1}
  let T := presheafToSheaf (ProEt.topology Y) Ab.{u + 1}
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
    (MorphismProperty.Over.map ⊤ hf).op
  exact Functor.associator (rawResidues X ℓ) S _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionSheafificationIso f hf) ≪≫
    (Functor.associator (rawResidues X ℓ) W T).symm ≪≫
    Functor.isoWhiskerRight (rawResiduesRestrictionIso f hf ℓ) T

/-- Compatible primitive roots identify the abelian root and constant residue diagrams. -/
theorem exists_compatible_roots_diagram_basis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤))) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty
        (tateRootsSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i) ≅
        constantTateResidueSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i)) := by
  classical
  let A := X.affineOpenCover
  choose D hD hAlg hind hff hw using fun j : A.I₀ ↦ exists_isWContractibleRing (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let (j : A.I₀) : Algebra (A.X j) (D j) := hAlg j
  let p (j : A.I₀) := Spec.map (CommRingCat.ofHom (algebraMap (A.X j) (D j)))
  have hwp (j : A.I₀) : WeaklyEtale (p j) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).mpr (hind j))
  have hsp (j : A.I₀) : Surjective (p j) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (hff j))).2
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (p j) (Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (hwp j))
  let B := C.bind E
  refine ⟨B, ?_⟩
  rintro ⟨j, i⟩
  have := hw j
  have hunit : IsUnit (ℓ : D j) := by
    have h := (hℓ.map (B.f ⟨j, i⟩).appTop.hom).map
      (Scheme.ΓSpecIso (CommRingCat.of (D j))).hom.hom
    simpa only [map_natCast] using h
  obtain ⟨z, hz0, hstep, hpow, hdiff⟩ := exists_primitive_unit_tower (D j) ℓ hunit
  let ψ : D j →+* Γ(B.X ⟨j, i⟩, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (D j))).inv.hom
  let zY (n : ℕ) : Γ(B.X ⟨j, i⟩, ⊤)ˣ := Units.map ψ.toMonoidHom (z n)
  have hpowY (n : ℕ) : zY n ^ (ℓ ^ n) = 1 := by
    simpa only [map_pow, map_one] using congrArg (Units.map ψ.toMonoidHom) (hpow n)
  have hstepY (n : ℕ) : zY (n + 1) ^ ℓ = zY n := by
    simpa only [map_pow] using congrArg (Units.map ψ.toMonoidHom) (hstep n)
  have hdiffY (n a : ℕ) (ha : a < ℓ ^ n) (b : ℕ) (hb : b < ℓ ^ n) (hab : a ≠ b) :
      IsUnit ((zY n : Γ(B.X ⟨j, i⟩, ⊤)) ^ a - (zY n : Γ(B.X ⟨j, i⟩, ⊤)) ^ b) := by
    change IsUnit (ψ (z n : D j) ^ a - ψ (z n : D j) ^ b)
    rw [← map_pow, ← map_pow, ← map_sub]
    exact (hdiff n a ha b hb hab).map ψ
  have hf : WeaklyEtale (B.f ⟨j, i⟩) := Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) ⟨j, i⟩
  exact ⟨rootsRestrictionIso (B.f ⟨j, i⟩) hf ℓ ≪≫
    (rootsBasisIso _ ℓ zY hpowY hstepY hdiffY).symm ≪≫
    (residuesRestrictionIso (B.f ⟨j, i⟩) hf ℓ).symm⟩

end AlgebraicGeometry.ProEtale
