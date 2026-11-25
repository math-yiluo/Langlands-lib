/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Algebra.Homology.LocalizedExactPairContraction
import WeilConjectures.Algebra.Homology.MinimalComplex

/-! # Cancelling a residue-exact degree of a finite free complex

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
the direct matrix proof.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

open TensorProduct in
private noncomputable def tensorExtendEquiv (R : Type u) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{max u v} R) :
    TensorProduct R S N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : TensorProduct R S N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] TensorProduct R S N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.inductionOn with
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

private theorem cancel_supported_idempotent
    {R : Type u} [CommRing R] (M : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (p : M ⟶ M) (hp : p ≫ p = p) (H : Homotopy p 0)
    (hi : p.f i = 𝟙 (M.X i))
    (hout : ∀ j : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) → p.f j = 0)
    (hfinite : ∀ j : ℤ, Module.Finite R (M.X j))
    (hkfree : ∀ j : ℤ, Module.Free R (LinearMap.ker (p.f j).hom)) :
    ∃ Q : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ j : ℤ, Module.Free R (Q.X j)) ∧
      (∀ j : ℤ, Module.Finite R (Q.X j)) ∧
      Nonempty (HomotopyEquiv M Q) ∧ IsZero (Q.X i) ∧
      (∀ j : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) → Q.X j = M.X j) ∧
      (∀ j k : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) →
        k ∉ ({i - 1, i, i + 1} : Set ℤ) → HEq (Q.d j k) (M.d j k)) ∧
      (∀ j : ℤ, j = i - 1 ∨ j = i + 1 →
        ∃ (a : Q.X j ⟶ M.X j) (b : M.X j ⟶ Q.X j), a ≫ b = 𝟙 (Q.X j)) ∧
      (∀ j : ℤ, IsZero (M.X j) → IsZero (Q.X j)) := by
  classical
  let K := kerSubcomplex p
  let X : ℤ → ModuleCat.{max u v} R := fun j ↦
    if j ∈ ({i - 1, i, i + 1} : Set ℤ) then K.X j else M.X j
  let e₀ (j : ℤ) (hj : j ∉ ({i - 1, i, i + 1} : Set ℤ)) : M.X j ≅ K.X j :=
    (LinearEquiv.toModuleIso {
      toFun := fun x ↦ ⟨x, by change (p.f j).hom x = 0; rw [hout j hj]; rfl⟩
      invFun := fun x ↦ x.1
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } : M.X j ≅ K.X j)
  let e : ∀ j : ℤ, X j ≅ K.X j := fun j ↦
    if hj : j ∈ ({i - 1, i, i + 1} : Set ℤ) then eqToIso (ite_eq_left hj)
    else eqToIso (ite_eq_right hj) ≪≫ e₀ j hj
  let Q : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    { X := X
      d := fun j k ↦ (e j).hom ≫ K.d j k ≫ (e k).inv
      shape := by intros; simp_all
      d_comp_d' := by intros; simp [Category.assoc] }
  let E : Q ≅ K := HomologicalComplex.Hom.isoOfComponents e (by
    intros; simp [Q, Category.assoc])
  have hkfinite (j : ℤ) : Module.Finite R (K.X j) := by
    have := hfinite j
    exact Module.Finite.of_surjective ((kerSubcomplexπ p hp).f j).hom <| by
      intro x
      refine ⟨(kerSubcomplexι p).f j x, ?_⟩
      exact congrArg (fun f ↦ f.hom x)
        (HomologicalComplex.congr_hom (kerSubcomplexι_comp_kerSubcomplexπ p hp) j)
  refine ⟨Q, ?_, ?_, ⟨(homotopyEquivKerSubcomplex p hp H).trans
    (HomotopyEquiv.ofIso E.symm)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have : Module.Free R (K.X j) := hkfree j
    exact Module.Free.of_equiv (e j).symm.toLinearEquiv
  · intro j
    have := hkfinite j
    exact Module.Finite.equiv (e j).symm.toLinearEquiv
  · have hK : IsZero (K.X i) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (LinearMap.ker (p.f i).hom)
      rw [hi]
      change Subsingleton (LinearMap.ker (LinearMap.id : M.X i →ₗ[R] M.X i))
      rw [LinearMap.ker_id]
      infer_instance
    exact hK.of_iso (e i)
  · intro j hj
    exact dite_eq_right hj
  · intro j k hj hk
    apply (conj_eqToHom_iff_heq (Q.d j k) (M.d j k) (ite_eq_right hj) (ite_eq_right hk)).mp
    dsimp only [Q, e]
    simp only [dite_eq_right hj, dite_eq_right hk, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
      eqToIso.inv, Category.assoc]
    congr 1
  · intro j _
    refine ⟨(e j).hom ≫ (kerSubcomplexι p).f j,
      (kerSubcomplexπ p hp).f j ≫ (e j).inv, ?_⟩
    have h := HomologicalComplex.congr_hom
      (kerSubcomplexι_comp_kerSubcomplexπ p hp) j
    change (e j).hom ≫ (kerSubcomplexι p).f j ≫
      (kerSubcomplexπ p hp).f j ≫ (e j).inv = 𝟙 _
    rw [← Category.assoc ((kerSubcomplexι p).f j),
      show (kerSubcomplexι p).f j ≫ (kerSubcomplexπ p hp).f j = 𝟙 _ from h]
    simp
  · intro j hj
    have := ModuleCat.isZero_iff_subsingleton.mp hj
    have hK : IsZero (K.X j) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (LinearMap.ker (p.f j).hom)
      infer_instance
    exact hK.of_iso (e j)

set_option backward.isDefEq.respectTransparency false in
/-- A residue-exact degree can be removed after one principal localization.

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
the direct matrix proof.
(auxiliary; not a blueprint node)

Proof: Residue homology vanishing says that the two adjacent maps are exact.
Apply exists_localized_exact_pair_contraction to obtain a principal localization
and maps s,t with AsA=A, tBt=t, and sA+Bt=1. Form q=dh+hd, where h is s in
degree i and t in degree i+1, and zero elsewhere. Its only nonzero components
are As, the identity, and tB. The displayed equations make q idempotent, and
its defining formula makes it nullhomotopic. The proved kerSubcomplex API then
gives a homotopy equivalence with ker q. Its middle term is zero, its neighboring
terms are the two free kernels supplied by the pair lemma, and finiteness follows
from their split projections. Replace the kernel terms outside the three degrees
by the original terms through their canonical isomorphisms; conjugate the
kernel differential by these degreewise isomorphisms. The resulting complex has
literal equality of the untouched terms and heterogeneous equality of their
differentials. Kernel inclusions and split projections give the two retractions.
A submodule of a zero term is zero, proving the final support clause. -/
theorem exists_localized_homotopyEquiv_zero_degree
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (i : ℤ)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hfree : ∀ j : ℤ, Module.Free R (P.X j))
    (hfinite : ∀ j : ℤ, Module.Finite R (P.X j))
    (hresidue : IsZero
      (((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, max u v}
          ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)))
        (ComplexShape.up ℤ)).obj P).homology i)) :
    ∃ (f : R), f ∉ p ∧
      ∃ (Q : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ),
        (∀ j : ℤ, Module.Free (Localization.Away f) (Q.X j)) ∧
        (∀ j : ℤ, Module.Finite (Localization.Away f) (Q.X j)) ∧
        Nonempty (HomotopyEquiv
          ((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f)))
            (ComplexShape.up ℤ)).obj P) Q) ∧
        IsZero (Q.X i) ∧
        (∀ j : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) →
          Q.X j = (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).obj
            (P.X j)) ∧
        (∀ j k : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) →
          k ∉ ({i - 1, i, i + 1} : Set ℤ) →
          HEq (Q.d j k)
            ((ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).map
              (P.d j k))) ∧
        (∀ j : ℤ, j = i - 1 ∨ j = i + 1 →
          ∃ (a : Q.X j ⟶
              (ModuleCat.extendScalars.{u, u, max u v}
                (algebraMap R (Localization.Away f))).obj (P.X j))
            (b : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).obj
              (P.X j) ⟶ Q.X j), a ≫ b = 𝟙 (Q.X j)) ∧
        (∀ j : ℤ, IsZero (P.X j) → IsZero (Q.X j)) := by
  classical
  let ρ := (algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)
  let C := ((ModuleCat.extendScalars.{u, u, max u v} ρ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hexact : Function.Exact
      ((ModuleCat.extendScalars ρ).map (P.d (i - 1) i)).hom
      ((ModuleCat.extendScalars ρ).map (P.d i (i + 1))).hom := by
    have hx : C.ExactAt i := (C.exactAt_iff_isZero_homology i).mpr hresidue
    have hs : (C.sc' (i - 1) i (i + 1)).Exact :=
      (C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp hx
    exact LinearMap.exact_iff.mpr hs.moduleCat_range_eq_ker.symm
  obtain ⟨f, hf, s, t, hs, ht, hmid, hks, hkt⟩ :=
    ModuleCat.exists_localized_exact_pair_contraction p (P.X (i - 1)) (P.X i)
      (P.X (i + 1)) (P.d (i - 1) i) (P.d i (i + 1)) (P.d_comp_d _ _ _)
      (hfree _) (hfree _) (hfree _) (hfinite _) (hfinite _) (hfinite _) hexact
  let S := Localization.Away f
  let E := ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)
  let M := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hMfinite (j : ℤ) : Module.Finite S (M.X j) := by
    have := hfinite j
    exact Module.Finite.equiv (tensorExtendEquiv R S (P.X j))
  have hMfree (j : ℤ) : Module.Free S (M.X j) := by
    have := hfree j
    exact Module.Free.of_equiv (tensorExtendEquiv R S (P.X j))
  let sM : M.X i ⟶ M.X (i - 1) := s
  let tM : M.X (i + 1) ⟶ M.X i := t
  have hsM : M.d (i - 1) i ≫ sM ≫ M.d (i - 1) i = M.d (i - 1) i := hs
  have htM : tM ≫ M.d i (i + 1) ≫ tM = tM := ht
  have hmidM : sM ≫ M.d (i - 1) i + M.d i (i + 1) ≫ tM = 𝟙 (M.X i) := hmid
  have hshift : i - 1 + 1 = i := by omega
  let s' : M.X (i - 1 + 1) ⟶ M.X (i - 1) := eqToHom (congrArg M.X hshift) ≫ sM
  let p₀ := singleNullHomotopicMap M (i - 1) s'
  let p₁ := singleNullHomotopicMap M i tM
  let q := p₀ + p₁
  have h₀ : p₀.f (i - 1) = M.d (i - 1) i ≫ sM := by
    simpa [p₀, s', hshift] using singleNullHomotopicMap_f_self M (i - 1) s'
  have h₀' : p₀.f i = sM ≫ M.d (i - 1) i := by
    dsimp only [p₀, singleNullHomotopicMap]
    rw [Homotopy.nullHomotopicMap_f (k₂ := i - 1) (k₀ := i + 1) (by simp) rfl]
    simp [singleHomotopyHom, hshift, s', HomologicalComplex.XIsoOfEq]
  have h₁ : p₁.f i = M.d i (i + 1) ≫ tM :=
    singleNullHomotopicMap_f_self M i tM
  have h₁' : p₁.f (i + 1) = tM ≫ M.d i (i + 1) :=
    singleNullHomotopicMap_f_succ M i tM
  have hqm : q.f (i - 1) = M.d (i - 1) i ≫ sM := by
    change p₀.f (i - 1) + p₁.f (i - 1) = _
    rw [h₀, singleNullHomotopicMap_f_eq_zero M i tM (by omega) (by omega), add_zero]
  have hqi : q.f i = 𝟙 (M.X i) := by
    change p₀.f i + p₁.f i = _
    rw [h₀', h₁, hmidM]
  have hqp : q.f (i + 1) = tM ≫ M.d i (i + 1) := by
    change p₀.f (i + 1) + p₁.f (i + 1) = _
    rw [singleNullHomotopicMap_f_eq_zero M (i - 1) s' (by omega) (by omega), h₁',
      zero_add]
  have hqout (j : ℤ) (hj : j ∉ ({i - 1, i, i + 1} : Set ℤ)) : q.f j = 0 := by
    have hj' : j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1 := by simpa using hj
    change p₀.f j + p₁.f j = 0
    rw [singleNullHomotopicMap_f_eq_zero M (i - 1) s' hj'.1 (by omega),
      singleNullHomotopicMap_f_eq_zero M i tM hj'.2.1 hj'.2.2, add_zero]
  have hqid : q ≫ q = q := by
    ext j : 1
    rw [HomologicalComplex.comp_f]
    by_cases hm : j = i - 1
    · subst j
      rw [hqm]
      simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ sM) hsM
    by_cases hi : j = i
    · subst j
      rw [hqi, Category.id_comp]
    by_cases hp : j = i + 1
    · subst j
      rw [hqp]
      simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ M.d i (i + 1)) htM
    rw [hqout j (by simpa using And.intro hm (And.intro hi hp)), zero_comp]
  have hqker (j : ℤ) : Module.Free S (LinearMap.ker (q.f j).hom) := by
    by_cases hm : j = i - 1
    · subst j
      rw [hqm]
      exact hks
    by_cases hi : j = i
    · subst j
      rw [hqi]
      change Module.Free S (LinearMap.ker (LinearMap.id : M.X i →ₗ[S] M.X i))
      rw [LinearMap.ker_id]
      infer_instance
    by_cases hp : j = i + 1
    · subst j
      rw [hqp]
      exact hkt
    rw [hqout j (by simpa using And.intro hm (And.intro hi hp))]
    change Module.Free S (LinearMap.ker (0 : M.X j →ₗ[S] M.X j))
    rw [LinearMap.ker_zero]
    have := hMfree j
    exact Module.Free.of_equiv (Submodule.topEquiv : (⊤ : Submodule S (M.X j)) ≃ₗ[S] _).symm
  have H : Homotopy q 0 := by
    simpa only [add_zero] using
      (singleNullHomotopy M (i - 1) s').add (singleNullHomotopy M i tM)
  obtain ⟨Q, hQfree, hQfinite, eQ, hQi, hQX, hQd, hQsplit, hQzero⟩ :=
    cancel_supported_idempotent M i q hqid H hqi hqout hMfinite hqker
  refine ⟨f, hf, Q, hQfree, hQfinite, eQ, hQi, hQX, hQd, hQsplit, ?_⟩
  intro j hj
  exact hQzero j (E.map_isZero hj)

end CochainComplex
