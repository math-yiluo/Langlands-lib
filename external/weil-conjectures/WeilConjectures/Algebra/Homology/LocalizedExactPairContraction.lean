/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Algebra.Homology.MinimalComplex
import WeilConjectures.Algebra.Homology.PrincipalContractionSpreading

/-! # Local contractions of a residue-exact pair of finite free maps

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`;
the local minimal-complex proof uses the proved source library's
`CochainComplex.exists_homotopyEquiv_isMinimal` and Nakayama.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings
namespace CochainComplex
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

set_option backward.isDefEq.respectTransparency false in
private theorem map_zero_of_mem_ideal
    {R : Type u} [CommRing R] {K : Type u} [Field K] (φ : R →+* K)
    (X Y : ModuleCat.{max u v} R) (a : X ⟶ Y)
    (ha : ∀ x, a.hom x ∈ RingHom.ker φ • (⊤ : Submodule R Y)) :
    (ModuleCat.extendScalars φ).map a = 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [ModuleCat.ExtendScalars.map_tmul]
  change (1 : K) ⊗ₜ[R, φ] a.hom x = 0
  refine Submodule.smul_induction_on
    (p := fun y : Y ↦ ((1 : K) ⊗ₜ[R, φ] y : (ModuleCat.extendScalars φ).obj Y) = 0)
    (ha x) ?_ ?_
  · intro r hr y _
    rw [TensorProduct.tmul_smul]
    change (φ r * 1) ⊗ₜ[R, φ] y = 0
    rw [RingHom.mem_ker.mp hr, zero_mul, TensorProduct.zero_tmul]
  · intro x y hx hy
    rw [TensorProduct.tmul_add, hx, hy, add_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem minimal_term_zero_of_residue_homology
    {R : Type u} [CommRing R] [IsLocalRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : P.IsMinimal) (i : ℤ)
    (hfinite : Module.Finite R (P.X i))
    (hres : IsZero ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
      (.up ℤ)).obj P).homology i)) : IsZero (P.X i) := by
  let K := IsLocalRing.ResidueField R
  let E := ModuleCat.extendScalars.{u, u, max u v} (IsLocalRing.residue R)
  let C := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hz (j k : ℤ) : C.d j k = 0 := by
    apply map_zero_of_mem_ideal (IsLocalRing.residue R) (P.X j) (P.X k) (P.d j k)
    simpa only [IsLocalRing.ker_residue] using hP j k
  have hExact : (C.sc' (i - 1) i (i + 1)).Exact :=
    (C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp
      ((C.exactAt_iff_isZero_homology i).mpr hres)
  have hCzero : IsZero (C.X i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_iff_forall_eq 0 |>.mpr
    intro x
    obtain ⟨y, hy⟩ := ((C.sc' (i - 1) i (i + 1)).moduleCat_exact_iff.mp hExact) x (by
      change (C.d i (i + 1)) x = 0
      rw [hz]
      rfl)
    change (C.d (i - 1) i) y = x at hy
    rw [hz] at hy
    exact hy.symm
  have : Subsingleton (C.X i) := ModuleCat.isZero_iff_subsingleton.mp hCzero
  have : Subsingleton ((ModuleCat.extendScalars (algebraMap R K)).obj (P.X i)) := by
    simpa only [C, E, K, IsLocalRing.ResidueField.algebraMap_eq,
      Functor.mapHomologicalComplex_obj_X] using
      (ModuleCat.isZero_iff_subsingleton.mp hCzero)
  have := hfinite
  have ht : Subsingleton (TensorProduct R K (P.X i)) :=
    (tensorExtendEquiv R K (P.X i)).injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((IsLocalRing.subsingleton_tensorProduct (R := R)).mp ht)

set_option backward.isDefEq.respectTransparency false in
private theorem local_pair_contraction
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X Y Z : ModuleCat.{max u v} R) (a : X ⟶ Y) (b : Y ⟶ Z)
    (hab : a ≫ b = 0)
    (hX : Module.Free R X) (hY : Module.Free R Y) (hZ : Module.Free R Z)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y) (hfZ : Module.Finite R Z)
    (hexact : Function.Exact
      ((ModuleCat.extendScalars (IsLocalRing.residue R)).map a).hom
      ((ModuleCat.extendScalars (IsLocalRing.residue R)).map b).hom) :
    ∃ (s : Y ⟶ X) (t : Z ⟶ Y),
      a ≫ s ≫ a = a ∧ t ≫ b ≫ t = t ∧ s ≫ a + b ≫ t = 𝟙 Y := by
  classical
  let : (ModuleCat.extendScalars.{u, u, max u v} (IsLocalRing.residue R)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue R)).left_adjoint_additive
  have := hX
  have := hY
  have := hZ
  have := hfX
  have := hfY
  have := hfZ
  let T : ℤ → ModuleCat.{max u v} R := fun j ↦
    if j = -1 then X else if j = 0 then Y else if j = 1 then Z
    else ModuleCat.of R PUnit.{max u v + 1}
  let d : ∀ j : ℤ, T j ⟶ T (j + 1) := fun j ↦
    if hj : j = -1 then eqToHom (by simp [T, hj]) ≫ a ≫ eqToHom (by simp [T, hj])
    else if hj' : j = 0 then eqToHom (by simp [T, hj']) ≫ b ≫
      eqToHom (by simp [T, hj']) else 0
  have hd : ∀ j, d j ≫ d (j + 1) = 0 := by
    intro j
    by_cases hj : j = -1
    · subst j
      simpa [d] using hab
    by_cases hj' : j = 0
    · subst j
      simp [d]
    simp [d, hj, hj']
  let P : CochainComplex (ModuleCat.{max u v} R) ℤ := CochainComplex.of T d hd
  have hfree (j : ℤ) : Module.Free R (P.X j) := by
    change Module.Free R (T j)
    by_cases h₁ : j = -1
    · have h : T j = X := by simp [T, h₁]
      rw [h]
      exact hX
    by_cases h₂ : j = 0
    · have h : T j = Y := by simp only [T, ite_eq_right h₁, ite_eq_left h₂]
      rw [h]
      exact hY
    by_cases h₃ : j = 1
    · have h : T j = Z := by simp only [T, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
      rw [h]
      exact hZ
    have h : T j = ModuleCat.of R PUnit.{max u v + 1} := by
      simp only [T, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
    rw [h]
    infer_instance
  have hfinite (j : ℤ) : Module.Finite R (P.X j) := by
    change Module.Finite R (T j)
    by_cases h₁ : j = -1
    · have h : T j = X := by simp [T, h₁]
      rw [h]
      exact hfX
    by_cases h₂ : j = 0
    · have h : T j = Y := by simp only [T, ite_eq_right h₁, ite_eq_left h₂]
      rw [h]
      exact hfY
    by_cases h₃ : j = 1
    · have h : T j = Z := by simp only [T, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
      rw [h]
      exact hfZ
    have h : T j = ModuleCat.of R PUnit.{max u v + 1} := by
      simp only [T, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
    rw [h]
    infer_instance
  have hlow : P.IsStrictlyGE (-1) := by
    rw [P.isStrictlyGE_iff]
    intro j hj
    have h : T j = ModuleCat.of R PUnit.{max u v + 1} := by simp [T, show j ≠ -1 by omega,
      show j ≠ 0 by omega, show j ≠ 1 by omega]
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit.{max u v + 1})).of_iso
      (eqToIso h)
  have hhigh : P.IsStrictlyLE 1 := by
    rw [P.isStrictlyLE_iff]
    intro j hj
    have h : T j = ModuleCat.of R PUnit.{max u v + 1} := by simp [T, show j ≠ -1 by omega,
      show j ≠ 0 by omega, show j ≠ 1 by omega]
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit.{max u v + 1})).of_iso
      (eqToIso h)
  have hp0 : P.X 0 = Y := by simp [P, T]
  have hpm : P.X (-1) = X := by simp [P, T]
  have hpp : P.X 1 = Z := by simp [P, T]
  have hpa : P.d (-1) 0 = eqToHom hpm ≫ a ≫ eqToHom hp0.symm := by
    simp [P, d, T, CochainComplex.of.d]
  have hpb : P.d 0 1 = eqToHom hp0 ≫ b ≫ eqToHom hpp.symm := by
    simp [P, d, T, CochainComplex.of.d]
  have hres : IsZero ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
      (.up ℤ)).obj P).homology 0) := by
    let E := ModuleCat.extendScalars (IsLocalRing.residue R)
    let C := (E.mapHomologicalComplex (.up ℤ)).obj P
    rw [← C.exactAt_iff_isZero_homology]
    rw [C.exactAt_iff' (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    let S := ShortComplex.mk (E.map a) (E.map b) (by rw [← E.map_comp, hab, E.map_zero])
    let iso : (C.sc' (-1) 0 1) ≅ S := ShortComplex.isoMk
      (E.mapIso (eqToIso hpm)) (E.mapIso (eqToIso hp0)) (E.mapIso (eqToIso hpp))
      (by simp [C, S, E, hpa])
      (by simp [C, S, E, hpb])
    have hh : S.Exact := S.moduleCat_exact_iff_range_eq_ker.mpr
      (LinearMap.exact_iff.mp hexact).symm
    exact ((C.sc' (-1) 0 1).moduleCat_exact_iff_range_eq_ker.mp
      (ShortComplex.exact_of_iso iso.symm hh))
  obtain ⟨N, hN, hlN, huN, hfN, hfinN, ⟨e⟩⟩ :=
    exists_homotopyEquiv_isMinimal P (-1) 1
  have hresN : IsZero ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
      (.up ℤ)).obj N).homology 0) := by
    exact hres.of_iso
      (HomotopyEquiv.toHomologyIso
        ((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomotopyEquiv e) 0).symm
  have hNzero := minimal_term_zero_of_residue_homology N hN 0 (hfinN 0) hresN
  let H := e.homotopyHomInvId
  have he0 : (e.hom ≫ e.inv).f 0 = 0 := by
    rw [HomologicalComplex.comp_f, hNzero.eq_zero_of_tgt (e.hom.f 0), zero_comp]
  have heq : P.d 0 1 ≫ H.hom 1 0 + H.hom 0 (-1) ≫ P.d (-1) 0 = -𝟙 (P.X 0) := by
    have h := H.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at h
    rw [he0, HomologicalComplex.id_f] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let s : Y ⟶ X := eqToHom hp0.symm ≫ (-H.hom 0 (-1)) ≫ eqToHom hpm
  let t : Z ⟶ Y := eqToHom hpp.symm ≫ (-H.hom 1 0) ≫ eqToHom hp0
  have hmid : s ≫ a + b ≫ t = 𝟙 Y := by
    have hh : -(P.d 0 1 ≫ H.hom 1 0 + H.hom 0 (-1) ≫ P.d (-1) 0) =
        𝟙 (P.X 0) := by rw [heq, neg_neg]
    have h := congrArg (fun g ↦ eqToHom hp0.symm ≫ g ≫ eqToHom hp0) hh
    simpa [hpa, hpb, s, t, Category.assoc] using h
  have has : a ≫ s ≫ a = a := by
    have h := congrArg (fun f ↦ a ≫ f) hmid
    simpa [Preadditive.comp_add, Category.assoc, ← Category.assoc a b, hab] using h
  have hbt : b ≫ t ≫ b = b := by
    have h := congrArg (fun f ↦ f ≫ b) hmid
    simpa [Preadditive.add_comp, Category.assoc, hab] using h
  refine ⟨s, t ≫ b ≫ t, has, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [reassoc_of% hbt, reassoc_of% hbt]
  · simpa only [Category.assoc, reassoc_of% hbt] using hmid

private theorem exact_transport
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C')
    (hf : ∀ x, eB (f x) = f' (eA x))
    (hg : ∀ y, eC (g y) = g' (eB y))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y'
  obtain ⟨y, rfl⟩ := eB.surjective y'
  constructor
  · intro hy
    have hz : g y = 0 := eC.injective (by rw [map_zero, hg]; exact hy)
    obtain ⟨x, hx⟩ := (h y).mp hz
    exact ⟨eA x, by rw [← hf, hx]⟩
  · rintro ⟨x', hx⟩
    obtain ⟨x, rfl⟩ := eA.surjective x'
    rw [← hx, ← hf, ← hg, (h (f x)).mpr ⟨x, rfl⟩, map_zero]

private noncomputable def changeFieldEquiv
    {R K K' : Type u} [CommRing R] [Field K] [Field K']
    [Algebra R K] [Algebra R K'] (e : K ≃ₐ[R] K') (N : ModuleCat.{max u v} R) :
    ((ModuleCat.extendScalars (algebraMap R K)).obj N) ≃+
      ((ModuleCat.extendScalars (algebraMap R K')).obj N) :=
  (tensorExtendEquiv R K N).symm.toAddEquiv.trans
    ((TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R N)).toAddEquiv.trans
      (tensorExtendEquiv R K' N).toAddEquiv)

set_option backward.isDefEq.respectTransparency false in
private theorem changeFieldEquiv_naturality
    {R K K' : Type u} [CommRing R] [Field K] [Field K']
    [Algebra R K] [Algebra R K'] (e : K ≃ₐ[R] K')
    (X Y : ModuleCat.{max u v} R) (a : X ⟶ Y)
    (x : (ModuleCat.extendScalars (algebraMap R K)).obj X) :
    changeFieldEquiv e Y (((ModuleCat.extendScalars (algebraMap R K)).map a).hom x) =
      ((ModuleCat.extendScalars (algebraMap R K')).map a).hom (changeFieldEquiv e X x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem exact_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (X Y Z : ModuleCat.{max u v} R) (a : X ⟶ Y) (b : Y ⟶ Z)
    (hexact : Function.Exact
      ((ModuleCat.extendScalars.{u, u, max u v}
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).map a).hom
      ((ModuleCat.extendScalars.{u, u, max u v}
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).map b).hom) :
    let E := ModuleCat.extendScalars.{u, u, max u v}
      (algebraMap R (Localization.AtPrime p))
    let F := ModuleCat.extendScalars.{u, u, max u v}
      (IsLocalRing.residue (Localization.AtPrime p))
    Function.Exact (F.map (E.map a)).hom (F.map (E.map b)).hom := by
  let K := FractionRing (R ⧸ p)
  let K' := p.ResidueField
  let e : K ≃ₐ[R] K' :=
    (IsLocalization.algEquiv (nonZeroDivisors (R ⧸ p)) K K').restrictScalars R
  have h : Function.Exact
      ((ModuleCat.extendScalars (algebraMap R K')).map a).hom
      ((ModuleCat.extendScalars (algebraMap R K')).map b).hom :=
    exact_transport
      ((ModuleCat.extendScalars (algebraMap R K)).map a).hom
      ((ModuleCat.extendScalars (algebraMap R K)).map b).hom
      ((ModuleCat.extendScalars (algebraMap R K')).map a).hom
      ((ModuleCat.extendScalars (algebraMap R K')).map b).hom
      (changeFieldEquiv e X)
      (changeFieldEquiv e Y) (changeFieldEquiv e Z)
      (changeFieldEquiv_naturality e X Y a)
      (changeFieldEquiv_naturality e Y Z b) hexact
  let α := ModuleCat.extendScalarsComp (algebraMap R (Localization.AtPrime p))
    (IsLocalRing.residue (Localization.AtPrime p))
  have hφ : (IsLocalRing.residue (Localization.AtPrime p)).comp
      (algebraMap R (Localization.AtPrime p)) = algebraMap R K' := by
    ext r
    change IsLocalRing.residue _ (algebraMap R _ r) = algebraMap R _ r
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) K',
      IsLocalRing.ResidueField.algebraMap_eq]
  have h' : Function.Exact
      ((ModuleCat.extendScalars ((IsLocalRing.residue (Localization.AtPrime p)).comp
        (algebraMap R (Localization.AtPrime p)))).map a).hom
      ((ModuleCat.extendScalars ((IsLocalRing.residue (Localization.AtPrime p)).comp
        (algebraMap R (Localization.AtPrime p)))).map b).hom := by
    rw [hφ]
    exact h
  exact exact_transport
    ((ModuleCat.extendScalars ((IsLocalRing.residue (Localization.AtPrime p)).comp
      (algebraMap R (Localization.AtPrime p)))).map a).hom
    ((ModuleCat.extendScalars ((IsLocalRing.residue (Localization.AtPrime p)).comp
      (algebraMap R (Localization.AtPrime p)))).map b).hom
    _ _ (α.app X).toLinearEquiv.toAddEquiv
    (α.app Y).toLinearEquiv.toAddEquiv
    (α.app Z).toLinearEquiv.toAddEquiv
    (fun x ↦ congrArg (fun g ↦ g.hom x) (α.hom.naturality a))
    (fun x ↦ congrArg (fun g ↦ g.hom x) (α.hom.naturality b)) h'

end CochainComplex

namespace ModuleCat

/-- A residue-exact pair admits complementary split identity blocks on a principal open.

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`.
(auxiliary; not a blueprint node)

Proof: Localize at p and compare the residue field with FractionRing (R/p).
Place the two maps in a complex in degrees -1, 0, 1. The proved minimal-complex
theorem gives a bounded finite free minimal homotopy representative. Its residue
differentials vanish, so residue exactness at zero makes its middle term vanish
modulo the maximal ideal. Nakayama makes that term zero. The homotopy identity
in degree zero therefore supplies s and t with sA+Bt=1. The relation BA=0 implies
AsA=A and BtB=B; replacing t by tBt gives tBt=t while retaining sA+Bt=1.
Spread this finite splitting data and its complementary summands to a principal
neighborhood using exists_principal_contraction_of_atPrime. The zero-rank case
is included in the minimal-complex theorem and Nakayama, without choosing a pivot. -/
theorem exists_localized_exact_pair_contraction
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (X Y Z : ModuleCat.{max u v} R) (a : X ⟶ Y) (b : Y ⟶ Z)
    (hab : a ≫ b = 0)
    (hX : Module.Free R X) (hY : Module.Free R Y) (hZ : Module.Free R Z)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y) (hfZ : Module.Finite R Z)
    (hexact : Function.Exact
      ((extendScalars.{u, u, max u v}
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).map a).hom
      ((extendScalars.{u, u, max u v}
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).map b).hom) :
    ∃ f : R, f ∉ p ∧
      let E := extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))
      ∃ (s : E.obj Y ⟶ E.obj X) (t : E.obj Z ⟶ E.obj Y),
        E.map a ≫ s ≫ E.map a = E.map a ∧
        t ≫ E.map b ≫ t = t ∧
        s ≫ E.map a + E.map b ≫ t = 𝟙 (E.obj Y) ∧
        Module.Free (Localization.Away f) (LinearMap.ker (E.map a ≫ s).hom) ∧
        Module.Free (Localization.Away f) (LinearMap.ker (t ≫ E.map b).hom) := by
  have := hX
  have := hY
  have := hZ
  have := hfX
  have := hfY
  have := hfZ
  let L := Localization.AtPrime p
  let E := extendScalars.{u, u, max u v} (algebraMap R L)
  let : E.Additive := (extendRestrictScalarsAdj (algebraMap R L)).left_adjoint_additive
  have hXL : Module.Free L (E.obj X) :=
    Module.Free.of_equiv (CochainComplex.tensorExtendEquiv R L X)
  have hYL : Module.Free L (E.obj Y) :=
    Module.Free.of_equiv (CochainComplex.tensorExtendEquiv R L Y)
  have hZL : Module.Free L (E.obj Z) :=
    Module.Free.of_equiv (CochainComplex.tensorExtendEquiv R L Z)
  have hfXL : Module.Finite L (E.obj X) := Module.Finite.of_surjective
    (CochainComplex.tensorExtendEquiv R L X).toLinearMap
    (CochainComplex.tensorExtendEquiv R L X).surjective
  have hfYL : Module.Finite L (E.obj Y) := Module.Finite.of_surjective
    (CochainComplex.tensorExtendEquiv R L Y).toLinearMap
    (CochainComplex.tensorExtendEquiv R L Y).surjective
  have hfZL : Module.Finite L (E.obj Z) := Module.Finite.of_surjective
    (CochainComplex.tensorExtendEquiv R L Z).toLinearMap
    (CochainComplex.tensorExtendEquiv R L Z).surjective
  obtain ⟨s, t, _, _, hm⟩ := CochainComplex.local_pair_contraction
    (E.obj X) (E.obj Y) (E.obj Z) (E.map a) (E.map b)
    (by rw [← E.map_comp, hab, E.map_zero]) hXL hYL hZL hfXL hfYL hfZL
    (CochainComplex.exact_atPrime p X Y Z a b hexact)
  exact exists_principal_contraction_of_atPrime p X Y Z a b hab hX hY hZ hfX hfY hfZ s t hm

end ModuleCat
