/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Projection
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.CategoryTheory.SplitCategoryNullHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Cohomology models and retracts over a field

Source: Weil conjectures blueprint, main-20261015, chap-The-trace-formula,
theorem-trace-formula-euler-product, first sentence of prop-trf-karoubi-independence.proof.md;
Stacks Project Tags 09FN, 09FP, 05CF and 05RU
(blueprint: lem-trf-field-complex-cohomology-splitting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private local instance fieldProjective {F : Type u} [Field F] (M : ModuleCat.{u} F) :
    Projective M := by
  have := Module.projective_of_isSemisimpleRing F M
  infer_instance

private local instance fieldInjective {F : Type u} [Field F] (M : ModuleCat.{u} F) :
    Injective M := by
  have := Module.injective_of_isSemisimpleRing F M
  exact Module.injective_object_of_injective_module F M

private theorem homotopy_of_homology_eq {F : Type u} [Field F]
    {P Q : CochainComplex (ModuleCat.{u} F) ℤ} (f g : P ⟶ Q)
    (h : ∀ n, HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n) :
    Nonempty (Homotopy f g) := by
  obtain ⟨t⟩ := CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero (f - g)
    (fun n ↦ by rw [HomologicalComplex.homologyMap_sub, h n, sub_self])
  exact ⟨Homotopy.equivSubZero.symm t⟩

private local instance fieldKProjective {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ) : P.IsKProjective where
  nonempty_homotopy_zero {_L} f hL :=
    CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero f
      (fun n ↦ ((ShortComplex.exact_iff_isZero_homology _).mp (hL n)).eq_of_tgt _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem lift_homology {F : Type u} [Field F]
    (P Q : CochainComplex (ModuleCat.{u} F) ℤ)
    (φ : ∀ n, P.homology n ⟶ Q.homology n) :
    ∃ f : P ⟶ Q, ∀ n, HomologicalComplex.homologyMap f n = φ n := by
  let a (n : ℤ) := Projective.factorThru (𝟙 (Q.homology n)) (Q.homologyπ n)
  let b (n : ℤ) := Injective.factorThru (P.homologyπ n) (P.iCycles n)
  have ha (n : ℤ) : a n ≫ Q.homologyπ n = 𝟙 _ := by simp [a]
  have hb (n : ℤ) : P.iCycles n ≫ b n = P.homologyπ n := by simp [b]
  have hd (i j : ℤ) : P.d i j ≫ b j = 0 := by
    rw [← P.toCycles_i i j, Category.assoc, hb, P.toCycles_comp_homologyπ]
  let f : P ⟶ Q :=
    { f := fun n ↦ b n ≫ φ n ≫ a n ≫ Q.iCycles n
      comm' := by
        intro i j hij
        simp only [Category.assoc, Q.iCycles_d, comp_zero]
        rw [← Category.assoc, hd, zero_comp] }
  refine ⟨f, fun n ↦ ?_⟩
  rw [← cancel_epi (P.homologyπ n), HomologicalComplex.homologyπ_naturality]
  have hc : HomologicalComplex.cyclesMap f n = P.homologyπ n ≫ φ n ≫ a n := by
    rw [← cancel_mono (Q.iCycles n), HomologicalComplex.cyclesMap_i]
    simp [f, Category.assoc, reassoc_of% hb]
  rw [hc]
  simp [Category.assoc, ha]

set_option backward.isDefEq.respectTransparency false in
private theorem Q_map_surjective {F : Type u} [Field F]
    (P R : CochainComplex (ModuleCat.{u} F) ℤ) :
    Function.Surjective (Q.map : (P ⟶ R) → (Q.obj P ⟶ Q.obj R)) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj R)).surjective
    ((quotientCompQhIso (ModuleCat F)).hom.app P ≫ f ≫
      (quotientCompQhIso (ModuleCat F)).inv.app R)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  have hh := quotientCompQhIso_hom_naturality g
  rw [hg] at hh
  simpa using hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem derived_homology_bijective {F : Type u} [Field F]
    (P R : DerivedCategory (ModuleCat.{u} F)) :
    Function.Bijective (fun f : P ⟶ R ↦
      fun n : ℤ ↦ (homologyFunctor (ModuleCat F) n).map f) := by
  let P₀ := Q.objPreimage P
  let R₀ := Q.objPreimage R
  let a : Q.obj P₀ ≅ P := Q.objObjPreimageIso P
  let b : Q.obj R₀ ≅ R := Q.objObjPreimageIso R
  have hinj (P R : CochainComplex (ModuleCat.{u} F) ℤ) (f g : Q.obj P ⟶ Q.obj R)
      (h : ∀ n, (homologyFunctor (ModuleCat F) n).map f =
        (homologyFunctor (ModuleCat F) n).map g) : f = g := by
    obtain ⟨f, rfl⟩ := Q_map_surjective P R f
    obtain ⟨g, rfl⟩ := Q_map_surjective P R g
    have he (n : ℤ) : HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n := by
      have hh := congrArg (fun t ↦ (homologyFunctorFactors (ModuleCat F) n).inv.app P ≫
        t ≫ (homologyFunctorFactors (ModuleCat F) n).hom.app R) (h n)
      simpa using hh
    obtain ⟨ht⟩ := homotopy_of_homology_eq f g he
    exact HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy ht
  constructor
  · intro f g h
    apply (Iso.homCongr a.symm b.symm).injective
    apply hinj
    intro n
    simp only [Iso.homCongr_apply, Functor.map_comp]
    have hn : (homologyFunctor (ModuleCat F) n).map f =
        (homologyFunctor (ModuleCat F) n).map g := congrFun h n
    rw [hn]
  · intro φ
    let φ₀ (n : ℤ) : P₀.homology n ⟶ R₀.homology n :=
      (homologyFunctorFactors (ModuleCat F) n).inv.app P₀ ≫
        (homologyFunctor (ModuleCat F) n).map a.hom ≫ φ n ≫
        (homologyFunctor (ModuleCat F) n).map b.inv ≫
        (homologyFunctorFactors (ModuleCat F) n).hom.app R₀
    obtain ⟨f, hf⟩ := lift_homology P₀ R₀ φ₀
    refine ⟨a.inv ≫ Q.map f ≫ b.hom, funext fun n ↦ ?_⟩
    have hh := homologyFunctorFactors_hom_naturality f n
    have he : (homologyFunctor (ModuleCat F) n).map (Q.map f) =
        (homologyFunctor (ModuleCat F) n).map a.hom ≫ φ n ≫
          (homologyFunctor (ModuleCat F) n).map b.inv := by
      rw [← cancel_mono ((homologyFunctorFactors (ModuleCat F) n).hom.app R₀), hh, hf]
      simp [φ₀, Category.assoc]
    simp only [Functor.map_comp, he, Category.assoc]
    simp [← Functor.map_comp]

private def zeroComplex {F : Type u} [Field F] (A : ℤ → ModuleCat.{u} F) :
    CochainComplex (ModuleCat.{u} F) ℤ :=
  { X := A, d := fun _ _ ↦ 0 }

private noncomputable def zeroHomologyIso {F : Type u} [Field F]
    (A : ℤ → ModuleCat.{u} F) (n : ℤ) : (zeroComplex A).homology n ≅ A n :=
  ((zeroComplex A).isoHomologyπ (n - 1) n (by simp) rfl).symm ≪≫
    (zeroComplex A).iCyclesIso n (n + 1) (by simp) rfl

private noncomputable def derivedZeroIso {F : Type u} [Field F]
    (A : ℤ → ModuleCat.{u} F) (n : ℤ) :
    (homologyFunctor (ModuleCat F) n).obj (Q.obj (zeroComplex A)) ≅ A n :=
  (homologyFunctorFactors (ModuleCat F) n).app (zeroComplex A) ≪≫ zeroHomologyIso A n

private theorem model_iso {F : Type u} [Field F]
    (P : DerivedCategory (ModuleCat.{u} F)) :
    Nonempty (P ≅ Q.obj (zeroComplex (fun n ↦ (homologyFunctor (ModuleCat F) n).obj P))) := by
  let A := fun n ↦ (homologyFunctor (ModuleCat F) n).obj P
  obtain ⟨f, hf⟩ := (derived_homology_bijective (Q.obj (zeroComplex A)) P).surjective
    (fun n ↦ (derivedZeroIso A n).hom)
  have hfn (n : ℤ) : (homologyFunctor (ModuleCat F) n).map f =
      (derivedZeroIso A n).hom := congrFun hf n
  have : IsIso f := (DerivedCategory.isIso_iff (ModuleCat F) f).mpr
    (fun n ↦ by rw [hfn]; infer_instance)
  exact ⟨(asIso f).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_maps {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ) (n : ℤ)
    (V T : Submodule F (P.X n))
    (hdis : Disjoint (LinearMap.range (P.d (n - 1) n).hom) V)
    (hsup : LinearMap.range (P.d (n - 1) n).hom ⊔ V =
      LinearMap.ker (P.d n (n + 1)).hom)
    (hT : IsCompl (LinearMap.ker (P.d n (n + 1)).hom) T) :
    ∃ (a : P.homology n ⟶ P.X n) (b : P.X n ⟶ P.homology n),
      LinearMap.range a.hom = V ∧
      LinearMap.ker b.hom = LinearMap.range (P.d (n - 1) n).hom ⊔ T ∧
      a ≫ b = 𝟙 _ ∧ P.iCycles n ≫ b = P.homologyπ n ∧
      a ≫ P.d n (n + 1) = 0 ∧ P.d (n - 1) n ≫ b = 0 := by
  classical
  let B := LinearMap.range (P.d (n - 1) n).hom
  have hV : V ≤ LinearMap.ker (P.d n (n + 1)).hom := by
    rw [← hsup]
    exact le_sup_right
  have hc : IsCompl V (B ⊔ T) :=
    hdis.symm.isCompl_sup_right_of_isCompl_sup_left (by
      change IsCompl (V ⊔ B) T
      rw [sup_comm, hsup]
      exact hT)
  let b₀ := Injective.factorThru (P.homologyπ n) (P.iCycles n)
  have hb₀ : P.iCycles n ≫ b₀ = P.homologyπ n := by simp [b₀]
  have hd₀ : P.d (n - 1) n ≫ b₀ = 0 := by
    rw [← P.toCycles_i (n - 1) n, Category.assoc, hb₀, P.toCycles_comp_homologyπ]
  have hB (x : P.X n) (hx : x ∈ B) : b₀ x = 0 := by
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun t ↦ t y) hd₀
  let c : V →ₗ[F] P.homology n := b₀.hom.comp V.subtype
  let ι : ModuleCat.of F V ⟶ P.X n := ModuleCat.ofHom V.subtype
  have hι : ι ≫ P.d n (n + 1) = 0 := by
    ext x
    exact hV x.property
  let l := P.liftCycles ι (n + 1) (by simp) hι
  have hl : l ≫ P.iCycles n = ι := P.liftCycles_i _ _ _ _
  have hlπ : l ≫ P.homologyπ n = ModuleCat.ofHom c := by
    rw [← hb₀, ← Category.assoc, hl]
    rfl
  have cinj : Function.Injective c := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    have hx' : P.homologyπ n (l x) = 0 := by
      change c x = 0 at hx
      have hh : P.homologyπ n (l x) = c x :=
        congrArg (fun t : ModuleCat.of F V ⟶ P.homology n ↦ t x) hlπ
      exact hh.trans hx
    let S := ShortComplex.mk (P.toCycles (n - 1) n) (P.homologyπ n)
      (P.toCycles_comp_homologyπ (n - 1) n)
    have hS : S.Exact := S.exact_of_g_is_cokernel
      (P.homologyIsCokernel (n - 1) n (by simp))
    obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff.mp hS) (l x) hx'
    have hxy : P.d (n - 1) n y = (x : P.X n) := by
      change P.toCycles (n - 1) n y = l x at hy
      have hh := congrArg (P.iCycles n) hy
      change (P.toCycles (n - 1) n ≫ P.iCycles n) y = (l ≫ P.iCycles n) x at hh
      rw [P.toCycles_i, hl] at hh
      exact hh
    have hxB : (x : P.X n) ∈ B := ⟨y, hxy⟩
    have hxzero : (x : P.X n) = 0 := (Submodule.disjoint_def.mp hdis) _ hxB x.property
    exact Subtype.ext hxzero
  have csurj : Function.Surjective c := by
    intro x
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ n)).mp inferInstance x
    have hz : P.iCycles n z ∈ B ⊔ V := by
      rw [hsup]
      exact congrArg (fun t ↦ t z) (P.iCycles_d n (n + 1))
    obtain ⟨w, hw, v, hv, hz⟩ := Submodule.mem_sup.mp hz
    refine ⟨⟨v, hv⟩, ?_⟩
    have hh := congrArg (fun t ↦ t z) hb₀
    change b₀ (P.iCycles n z) = P.homologyπ n z at hh
    rw [← hz, map_add, hB w hw, zero_add] at hh
    exact hh
  let e := LinearEquiv.ofBijective c ⟨cinj, csurj⟩
  let a : P.homology n ⟶ P.X n := ModuleCat.ofHom (V.subtype.comp e.symm.toLinearMap)
  let b : P.X n ⟶ P.homology n :=
    ModuleCat.ofHom (c.comp (V.projectionOnto (B ⊔ T) hc))
  have ha : LinearMap.range a.hom = V := by
    simp [a, LinearMap.range_comp, LinearEquiv.range]
  have hb : LinearMap.ker b.hom = B ⊔ T := by
    ext x
    change c (V.projectionOnto (B ⊔ T) hc x) = 0 ↔ _
    rw [show c (V.projectionOnto (B ⊔ T) hc x) = 0 ↔
      V.projectionOnto (B ⊔ T) hc x = 0 from cinj.eq_iff' (map_zero c)]
    exact Submodule.projectionOnto_apply_eq_zero_iff hc
  have hab : a ≫ b = 𝟙 _ := by
    ext x
    change c (V.projectionOnto (B ⊔ T) hc (e.symm x : P.X n)) = x
    rw [Submodule.projectionOnto_apply_left]
    exact e.apply_symm_apply x
  have hnorm : P.iCycles n ≫ b = P.homologyπ n := by
    ext z
    have hz : P.iCycles n z ∈ B ⊔ V := by
      rw [hsup]
      exact congrArg (fun t ↦ t z) (P.iCycles_d n (n + 1))
    obtain ⟨w, hw, v, hv, hz⟩ := Submodule.mem_sup.mp hz
    have hpw : V.projectionOnto (B ⊔ T) hc w = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hc ((show B ≤ B ⊔ T from le_sup_left) hw)
    have hpv : V.projectionOnto (B ⊔ T) hc v = ⟨v, hv⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hc hv
    change c (V.projectionOnto (B ⊔ T) hc (P.iCycles n z)) = P.homologyπ n z
    rw [← hz, map_add, hpw, hpv, zero_add]
    have hh := congrArg (fun t ↦ t z) hb₀
    change b₀ (P.iCycles n z) = P.homologyπ n z at hh
    rw [← hz, map_add, hB w hw, zero_add] at hh
    exact hh
  refine ⟨a, b, ha, hb, hab, hnorm, ?_, ?_⟩
  · ext x
    exact hV (ha ▸ LinearMap.mem_range_self a.hom x)
  · rw [← P.toCycles_i (n - 1) n, Category.assoc, hnorm, P.toCycles_comp_homologyπ]

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_equiv {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ)
    (V T : ∀ n : ℤ, Submodule F (P.X n))
    (h : ∀ n, Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
      LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
        LinearMap.ker (P.d n (n + 1)).hom ∧
      IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n)) :
    ∃ E : HomotopyEquiv (zeroComplex (fun n ↦ P.homology n)) P,
      (∀ n, LinearMap.range (E.hom.f n).hom = V n) ∧
      (∀ n, LinearMap.ker (E.inv.f n).hom =
        LinearMap.range (P.d (n - 1) n).hom ⊔ T n) ∧
      (∀ n (x : P.cycles n), E.inv.f n (P.iCycles n x) = P.homologyπ n x) := by
  choose a b ha hb hab hn had hdb using
    (fun n ↦ normalized_maps P n (V n) (T n) (h n).1 (h n).2.1 (h n).2.2)
  let H := zeroComplex (fun n ↦ P.homology n)
  let α : H ⟶ P :=
    { f := a
      comm' := by
        intro i j hij
        obtain rfl : i + 1 = j := hij
        change a i ≫ P.d i (i + 1) = 0 ≫ a (i + 1)
        rw [zero_comp]
        exact had i }
  let β : P ⟶ H :=
    { f := b
      comm' := by
        intro i j hij
        change b i ≫ 0 = P.d i j ≫ b j
        rw [comp_zero, ← P.toCycles_i i j, Category.assoc, hn,
          P.toCycles_comp_homologyπ] }
  have hαβ : α ≫ β = 𝟙 H := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hab n
  have hβα (n : ℤ) : HomologicalComplex.homologyMap (β ≫ α) n =
      HomologicalComplex.homologyMap (𝟙 P) n := by
    rw [← cancel_epi (P.homologyπ n), HomologicalComplex.homologyπ_naturality,
      HomologicalComplex.homologyMap_id,
      Category.comp_id]
    have hc : HomologicalComplex.cyclesMap (β ≫ α) n = P.homologyπ n ≫
        P.liftCycles (a n) (n + 1) (by simp) (had n) := by
      rw [← cancel_mono (P.iCycles n), HomologicalComplex.cyclesMap_i]
      simp only [Category.assoc, P.liftCycles_i]
      change P.iCycles n ≫ b n ≫ a n = P.homologyπ n ≫ a n
      rw [← Category.assoc, hn]
    rw [hc, Category.assoc]
    have hl : P.liftCycles (a n) (n + 1) (by simp) (had n) ≫ P.homologyπ n = 𝟙 _ := by
      rw [← hn, ← Category.assoc, P.liftCycles_i, hab]
    rw [hl, Category.comp_id]
  obtain ⟨ht⟩ := homotopy_of_homology_eq (β ≫ α) (𝟙 P) hβα
  exact ⟨⟨α, β, Homotopy.ofEq hαβ, ht⟩, ha, hb,
    fun n x ↦ congrArg (fun t ↦ t x) (hn n)⟩

private theorem field_complements {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ) :
    ∃ V T : ∀ n : ℤ, Submodule F (P.X n), ∀ n,
      Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
      LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
        LinearMap.ker (P.d n (n + 1)).hom ∧
      IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n) := by
  have hz (n : ℤ) : LinearMap.range (P.d (n - 1) n).hom ≤
      LinearMap.ker (P.d n (n + 1)).hom := by
    rintro _ ⟨x, rfl⟩
    exact congrArg (fun t ↦ t x) (P.d_comp_d (n - 1) n (n + 1))
  choose V hV using fun n ↦ IsModularLattice.exists_disjoint_and_sup_eq (hz n)
  choose T hT using fun n ↦ (LinearMap.ker (P.d n (n + 1)).hom).exists_isCompl
  exact ⟨V, T, fun n ↦ ⟨(hV n).1, (hV n).2, hT n⟩⟩

private theorem finite_model {F : Type u} [Field F]
    (P : DerivedCategory (ModuleCat.{u} F)) (hP : pointFiniteDimensional F P) :
    (∃ (H : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ),
      (∀ n m, H.d n m = 0) ∧
      (∀ n, Nonempty (H.X n ≅ (homologyFunctor (ModuleCat F) n).obj P)) ∧
      H.IsStrictlyGE a ∧ H.IsStrictlyLE b ∧
      (∀ n, FiniteDimensional F (H.X n)) ∧ Nonempty (P ≅ Q.obj H)) ∧
    IsPerfectRingComplex P := by
  classical
  let H := zeroComplex (fun n ↦ (homologyFunctor (ModuleCat F) n).obj P)
  obtain ⟨s, hs⟩ := hP.1
  obtain ⟨a, ha⟩ := s.bddBelow
  obtain ⟨b, hb⟩ := s.bddAbove
  have hge : H.IsStrictlyGE a := (H.isStrictlyGE_iff a).mpr (fun n hn ↦
    hs n (fun hmem ↦ (not_le_of_gt hn) (ha hmem)))
  have hle : H.IsStrictlyLE b := (H.isStrictlyLE_iff b).mpr (fun n hn ↦
    hs n (fun hmem ↦ (not_le_of_gt hn) (hb hmem)))
  have hfd (n : ℤ) : FiniteDimensional F (H.X n) := hP.2 n
  have hiso : Nonempty (P ≅ Q.obj H) := model_iso P
  refine ⟨⟨H, a, b, fun _ _ ↦ rfl, fun _ ↦ ⟨Iso.refl _⟩, hge, hle, hfd, hiso⟩,
    H, a, b, hge, hle, ?_, hiso⟩
  intro n
  have := hfd n
  exact ⟨inferInstance, inferInstance⟩

private theorem compare_splittings {C : Type*} [Category* C]
    {P S S' : C} (e v : P ⟶ P) (hv : v ≫ e = e ≫ v)
    (i : S ⟶ P) (r : P ⟶ S) (i' : S' ⟶ P) (r' : P ⟶ S')
    (hir : i ≫ r = 𝟙 S) (hri : r ≫ i = e)
    (hir' : i' ≫ r' = 𝟙 S') (hri' : r' ≫ i' = e) :
    (i ≫ r') ≫ (i' ≫ r) = 𝟙 S ∧
    (i' ≫ r) ≫ (i ≫ r') = 𝟙 S' ∧
    (i ≫ v ≫ r) ≫ (i ≫ r') = (i ≫ r') ≫ (i' ≫ v ≫ r') := by
  have hi : i ≫ e = i := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
  have hi' : i' ≫ e = i' := by rw [← hri', ← Category.assoc, hir', Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · calc
      (i ≫ r') ≫ (i' ≫ r) = (i ≫ (r' ≫ i')) ≫ r := by simp [Category.assoc]
      _ = 𝟙 S := by rw [hri', hi, hir]
  · calc
      (i' ≫ r) ≫ (i ≫ r') = (i' ≫ (r ≫ i)) ≫ r' := by simp [Category.assoc]
      _ = 𝟙 S' := by rw [hri, hi', hir']
  · calc
      (i ≫ v ≫ r) ≫ (i ≫ r') = i ≫ (v ≫ (r ≫ i)) ≫ r' := by simp [Category.assoc]
      _ = i ≫ (e ≫ v) ≫ r' := by rw [hri, hv]
      _ = i ≫ v ≫ r' := by simp only [← Category.assoc, hi]
      _ = (i ≫ r') ≫ (i' ≫ v ≫ r') := by
        rw [Category.assoc, ← Category.assoc r' i', hri', ← Category.assoc i e, hi]

private theorem assemble_splitting {C : Type*} [Category* C] [Preadditive C]
    {P S N : C} [HasBinaryBiproduct S N] (e : P ⟶ P)
    (i : S ⟶ P) (r : P ⟶ S) (j : N ⟶ P) (s : P ⟶ N)
    (hir : i ≫ r = 𝟙 S) (hri : r ≫ i = e)
    (hjs : j ≫ s = 𝟙 N) (hsj : s ≫ j = 𝟙 P - e) :
    ∃ α : P ≅ S ⊞ N, α.hom = biprod.lift r s ∧ α.inv = biprod.desc i j ∧
      ∀ v : P ⟶ P, v ≫ e = e ≫ v →
        α.inv ≫ (e ≫ v) ≫ α.hom = biprod.map (i ≫ v ≫ r) 0 := by
  have hi : i ≫ e = i := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
  have hr : e ≫ r = r := by rw [← hri, Category.assoc, hir, Category.comp_id]
  have hj : j ≫ e = 0 := by
    have h : j ≫ (𝟙 P - e) = j := by
      rw [← hsj, ← Category.assoc, hjs, Category.id_comp]
    simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_self] using h
  have hs : e ≫ s = 0 := by
    have h : (𝟙 P - e) ≫ s = s := by
      rw [← hsj, Category.assoc, hjs, Category.comp_id]
    simpa only [Preadditive.sub_comp, Category.id_comp, sub_eq_self] using h
  have his : i ≫ s = 0 := by
    calc
      i ≫ s = i ≫ e ≫ s := by rw [← Category.assoc, hi]
      _ = 0 := by rw [hs, comp_zero]
  have hjr : j ≫ r = 0 := by
    calc
      j ≫ r = j ≫ e ≫ r := by rw [hr]
      _ = 0 := by rw [← Category.assoc, hj, zero_comp]
  let α : P ≅ S ⊞ N :=
    { hom := biprod.lift r s
      inv := biprod.desc i j
      hom_inv_id := by
        rw [biprod.lift_desc, hri, hsj]
        abel
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [Category.assoc, hir, hjs, his, hjr] }
  refine ⟨α, rfl, rfl, fun v hv ↦ ?_⟩
  have hvs : e ≫ v ≫ s = 0 := by
    rw [← Category.assoc, ← hv, Category.assoc, hs, comp_zero]
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · simpa [α, Category.assoc] using congrArg (fun t ↦ t ≫ v ≫ r) hi
  · simp [α, Category.assoc, hvs]
  · simp [α, ← Category.assoc, hj]
  · simp [α, Category.assoc, hvs]

private theorem linear_splitting {F : Type u} [Field F]
    (X : ModuleCat.{u} F) (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (i : ModuleCat.of F (LinearMap.range e.hom) ⟶ X)
      (r : X ⟶ ModuleCat.of F (LinearMap.range e.hom))
      (j : ModuleCat.of F (LinearMap.ker e.hom) ⟶ X)
      (s : X ⟶ ModuleCat.of F (LinearMap.ker e.hom)),
      i ≫ r = 𝟙 _ ∧ r ≫ i = e ∧ j ≫ s = 𝟙 _ ∧ s ≫ j = 𝟙 X - e := by
  have he' : IsIdempotentElem e.hom := ModuleCat.hom_ext_iff.mp he
  let U := LinearMap.range e.hom
  let V := LinearMap.ker e.hom
  let hc : IsCompl U V := LinearMap.IsIdempotentElem.isCompl he'
  refine ⟨ModuleCat.ofHom U.subtype, ModuleCat.ofHom (U.projectionOnto V hc),
    ModuleCat.ofHom V.subtype, ModuleCat.ofHom (V.projectionOnto U hc.symm),
    ?_, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    exact Submodule.projectionOnto_comp_subtype hc
  · apply ModuleCat.hom_ext
    exact (LinearMap.IsIdempotentElem.eq_projection he').symm
  · apply ModuleCat.hom_ext
    exact Submodule.projectionOnto_comp_subtype hc.symm
  · apply ModuleCat.hom_ext
    change V.projection U hc.symm = LinearMap.id - e.hom
    rw [Submodule.projection_eq_id_sub_projection hc,
      ← LinearMap.IsIdempotentElem.eq_projection he']

set_option backward.isDefEq.respectTransparency false in
private theorem derived_splitting {F : Type u} [Field F]
    (P : DerivedCategory (ModuleCat.{u} F)) (e : P ⟶ P) (he : e ≫ e = e) :
    ∃ S N : CochainComplex (ModuleCat.{u} F) ℤ,
      (∀ n m, S.d n m = 0 ∧ N.d n m = 0) ∧
      (∀ n, Nonempty (S.X n ≅ ModuleCat.of F
        (LinearMap.range ((homologyFunctor (ModuleCat F) n).map e).hom)) ∧
        Nonempty (N.X n ≅ ModuleCat.of F
        (LinearMap.ker ((homologyFunctor (ModuleCat F) n).map e).hom))) ∧
      ∃ (i : Q.obj S ⟶ P) (r : P ⟶ Q.obj S)
        (j : Q.obj N ⟶ P) (s : P ⟶ Q.obj N),
        i ≫ r = 𝟙 _ ∧ r ≫ i = e ∧ j ≫ s = 𝟙 _ ∧ s ≫ j = 𝟙 P - e ∧
        ∃ α : P ≅ Q.obj S ⊞ Q.obj N,
          α.hom = biprod.lift r s ∧ α.inv = biprod.desc i j ∧
          ∀ v : P ⟶ P, v ≫ e = e ≫ v →
            α.inv ≫ (e ≫ v) ≫ α.hom = biprod.map (i ≫ v ≫ r) 0 := by
  classical
  let A := fun n ↦ ModuleCat.of F (LinearMap.range ((homologyFunctor (ModuleCat F) n).map e).hom)
  let B := fun n ↦ ModuleCat.of F (LinearMap.ker ((homologyFunctor (ModuleCat F) n).map e).hom)
  let S := zeroComplex A
  let N := zeroComplex B
  have hE (n : ℤ) : (homologyFunctor (ModuleCat F) n).map e ≫
      (homologyFunctor (ModuleCat F) n).map e = (homologyFunctor (ModuleCat F) n).map e := by
    rw [← Functor.map_comp, he]
  choose i₀ r₀ j₀ s₀ hir₀ hri₀ hjs₀ hsj₀ using
    fun n ↦ linear_splitting ((homologyFunctor (ModuleCat F) n).obj P)
      ((homologyFunctor (ModuleCat F) n).map e) (hE n)
  let a := derivedZeroIso A
  let b := derivedZeroIso B
  obtain ⟨i, hi⟩ := (derived_homology_bijective (Q.obj S) P).surjective
    (fun n ↦ (a n).hom ≫ i₀ n)
  obtain ⟨r, hr⟩ := (derived_homology_bijective P (Q.obj S)).surjective
    (fun n ↦ r₀ n ≫ (a n).inv)
  obtain ⟨j, hj⟩ := (derived_homology_bijective (Q.obj N) P).surjective
    (fun n ↦ (b n).hom ≫ j₀ n)
  obtain ⟨s, hs⟩ := (derived_homology_bijective P (Q.obj N)).surjective
    (fun n ↦ s₀ n ≫ (b n).inv)
  have hi (n : ℤ) : (homologyFunctor (ModuleCat F) n).map i = (a n).hom ≫ i₀ n := congrFun hi n
  have hr (n : ℤ) : (homologyFunctor (ModuleCat F) n).map r = r₀ n ≫ (a n).inv := congrFun hr n
  have hj (n : ℤ) : (homologyFunctor (ModuleCat F) n).map j = (b n).hom ≫ j₀ n := congrFun hj n
  have hs (n : ℤ) : (homologyFunctor (ModuleCat F) n).map s = s₀ n ≫ (b n).inv := congrFun hs n
  have hir : i ≫ r = 𝟙 _ := by
    apply (derived_homology_bijective _ _).injective
    funext n
    change (homologyFunctor (ModuleCat F) n).map (i ≫ r) =
      (homologyFunctor (ModuleCat F) n).map (𝟙 _)
    simp [hi, hr, Category.assoc, reassoc_of% hir₀]
  have hri : r ≫ i = e := by
    apply (derived_homology_bijective _ _).injective
    funext n
    change (homologyFunctor (ModuleCat F) n).map (r ≫ i) = (homologyFunctor (ModuleCat F) n).map e
    simp [hi, hr, Category.assoc, hri₀]
  have hjs : j ≫ s = 𝟙 _ := by
    apply (derived_homology_bijective _ _).injective
    funext n
    change (homologyFunctor (ModuleCat F) n).map (j ≫ s) =
      (homologyFunctor (ModuleCat F) n).map (𝟙 _)
    simp [hj, hs, Category.assoc, reassoc_of% hjs₀]
  have hsj : s ≫ j = 𝟙 P - e := by
    apply (derived_homology_bijective _ _).injective
    funext n
    change (homologyFunctor (ModuleCat F) n).map (s ≫ j) =
      (homologyFunctor (ModuleCat F) n).map (𝟙 P - e)
    simp [hj, hs, Category.assoc, hsj₀]
  exact ⟨S, N, fun _ _ ↦ ⟨rfl, rfl⟩,
    fun _ ↦ ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩,
    i, r, j, s, hir, hri, hjs, hsj, assemble_splitting e i r j s hir hri hjs hsj⟩

/-- Complexes over a field have cohomology models, and finite cohomology models have
compatible image/kernel retracts.
Source: main-20261015, prop-trf-karoubi-independence.proof.md, first sentence;
Stacks Project Tags 09FN, 09FP, 05CF and 05RU
(blueprint: lem-trf-field-complex-cohomology-splitting).

Proof:
1. By vector-space projectivity (lem-weil-pbc-vector-space-projective), the maps
   from cycles onto cohomology and from terms onto boundaries have sections.
   Their images give complements V to boundaries in cycles and T to cycles in terms.
   The differential identifies T in degree n with boundaries in degree n+1.
2. For any such complements, include the chosen cohomology representatives V and
   project onto their cohomology classes. These are chain maps a and b with ba=1.
   Define h in degree n by the inverse differential on boundaries and zero on V+T.
   Then dh+hd=1-ab, giving the homotopy equivalence and the stated normalization.
3. Homotopic maps act equally on cohomology. The contractions show that any chain
   map f is homotopic to a_Q (b_Q f a_P) b_P: a homotopy is h_Q f+a_Q b_Q f h_P.
   Thus two maps with equal cohomology maps are homotopic.
4. For a quasi-isomorphism f, invert its degreewise cohomology maps and conjugate
   this inverse family by a and b. Step 3 makes the resulting map a homotopy inverse.
5. Quasi-isomorphisms are therefore already invertible in the homotopy category.
   The localization universal property (def-weil-abstract-derived-category) factors
   its identity through D(F). Applying that property again to natural transformations
   gives inverse equivalences between the homotopy category and D(F).
6. Maps between zero-differential complexes are arbitrary degreewise maps, and a
   homotopy between them forces equality. Steps 2 and 5 therefore give a bijection
   on Hom sets. The normalization in Step 2 identifies it with the canonical map
   induced by def-weil-derived-category-cohomology-functor.
7. For pointFiniteDimensional objects, the cohomology model is bounded and termwise
   finite-dimensional (def-weil-point-fd-complexes). Its terms are finitely generated
   (def-weil-finite-dimensional-subspace, def-weil-finitely-generated-module) and
   projective (lem-weil-pbc-vector-space-projective), so it is perfect by
   def-pc-perfect-ring-complex.
8. For an idempotent e, each cohomology space decomposes as image H(e) plus kernel
   H(e), via x ↦ (H(e)x, (1-H(e))x), with inverse addition. Both summands retain
   finite dimension and finite support.
9. Transport the inclusions and projections along the cohomology-model isomorphism.
   Step 6 proves their splitting identities. A commuting v preserves image and
   kernel, so ve has blocks rvi and zero; Step 6 gives the asserted equality in D(F).
10. For arbitrary splittings of the same e, the maps r'i and ri' compose to identities
    because ei=i, re=r, ei'=i' and r'e=r'. Using ve=ev in the same compositions
    gives the intertwining equation. These are formal category identities. -/
theorem field_complex_cohomology_splitting (F : Type u) [Field F] :
    (∀ P : CochainComplex (ModuleCat.{u} F) ℤ,
      (∃ V T : ∀ n : ℤ, Submodule F (P.X n),
        (∀ n : ℤ,
          Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
          LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
            LinearMap.ker (P.d n (n + 1)).hom ∧
          IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n))) ∧
      (∀ V T : ∀ n : ℤ, Submodule F (P.X n),
        (∀ n : ℤ,
          Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
          LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
            LinearMap.ker (P.d n (n + 1)).hom ∧
          IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n)) →
        ∃ E : HomotopyEquiv
            ({ X := fun n ↦ P.homology n, d := fun _ _ ↦ 0 } :
              CochainComplex (ModuleCat.{u} F) ℤ) P,
          (∀ n : ℤ, LinearMap.range (E.hom.f n).hom = V n) ∧
          (∀ n : ℤ, LinearMap.ker (E.inv.f n).hom =
            LinearMap.range (P.d (n - 1) n).hom ⊔ T n) ∧
          (∀ (n : ℤ) (x : P.cycles n), E.inv.f n (P.iCycles n x) = P.homologyπ n x))) ∧
    (∀ (P Q : CochainComplex (ModuleCat.{u} F) ℤ) (f : P ⟶ Q),
      QuasiIso f → ∃ E : HomotopyEquiv P Q, E.hom = f) ∧
    (∀ P Q : DerivedCategory (ModuleCat.{u} F),
      Function.Bijective (fun f : P ⟶ Q ↦
        fun n : ℤ ↦ (homologyFunctor (ModuleCat.{u} F) n).map f)) ∧
    (∀ P : DerivedCategory (ModuleCat.{u} F), pointFiniteDimensional F P →
      (∃ (H : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ),
        (∀ n m : ℤ, H.d n m = 0) ∧
        (∀ n : ℤ, Nonempty (H.X n ≅ (homologyFunctor (ModuleCat.{u} F) n).obj P)) ∧
        H.IsStrictlyGE a ∧ H.IsStrictlyLE b ∧
        (∀ n : ℤ, FiniteDimensional F (H.X n)) ∧ Nonempty (P ≅ Q.obj H)) ∧
      IsPerfectRingComplex P) ∧
    (∀ (P : DerivedCategory (ModuleCat.{u} F)) (_hP : pointFiniteDimensional F P)
        (e : P ⟶ P), e ≫ e = e →
      (∃ S N : CochainComplex (ModuleCat.{u} F) ℤ,
        (∀ n m : ℤ, S.d n m = 0 ∧ N.d n m = 0) ∧
        (∀ n : ℤ,
          Nonempty (S.X n ≅ ModuleCat.of F
            (LinearMap.range ((homologyFunctor (ModuleCat.{u} F) n).map e).hom)) ∧
          Nonempty (N.X n ≅ ModuleCat.of F
            (LinearMap.ker ((homologyFunctor (ModuleCat.{u} F) n).map e).hom))) ∧
        ∃ (i : Q.obj S ⟶ P) (r : P ⟶ Q.obj S)
            (j : Q.obj N ⟶ P) (s : P ⟶ Q.obj N),
          i ≫ r = 𝟙 (Q.obj S) ∧ r ≫ i = e ∧
          j ≫ s = 𝟙 (Q.obj N) ∧ s ≫ j = 𝟙 P - e ∧
          ∃ α : P ≅ Q.obj S ⊞ Q.obj N,
            α.hom = biprod.lift r s ∧ α.inv = biprod.desc i j ∧
            ∀ v : P ⟶ P, v ≫ e = e ≫ v →
              α.inv ≫ (e ≫ v) ≫ α.hom = biprod.map (i ≫ v ≫ r) 0) ∧
      (∀ (v : P ⟶ P) (_hv : v ≫ e = e ≫ v)
          (S S' : DerivedCategory (ModuleCat.{u} F))
          (i : S ⟶ P) (r : P ⟶ S) (i' : S' ⟶ P) (r' : P ⟶ S'),
        i ≫ r = 𝟙 S → r ≫ i = e → i' ≫ r' = 𝟙 S' → r' ≫ i' = e →
          (i ≫ r') ≫ (i' ≫ r) = 𝟙 S ∧
          (i' ≫ r) ≫ (i ≫ r') = 𝟙 S' ∧
          (i ≫ v ≫ r) ≫ (i ≫ r') = (i ≫ r') ≫ (i' ≫ v ≫ r'))) := by
  refine ⟨?_, ?_, derived_homology_bijective, finite_model, ?_⟩
  · intro P
    exact ⟨field_complements P, normalized_equiv P⟩
  · intro P R f hf
    exact (CochainComplex.IsKProjective.quasiIso_iff f).mp hf
  · intro P _hP e he
    exact ⟨derived_splitting P e he, fun v hv _ _ i r i' r' hir hri hir' hri' ↦
      compare_splittings e v hv i r i' r' hir hri hir' hri'⟩

end DerivedCategory
