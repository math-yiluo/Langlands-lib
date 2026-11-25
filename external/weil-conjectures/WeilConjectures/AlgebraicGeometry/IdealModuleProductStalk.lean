/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.IdealModuleMultiplicationStalkRange
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Stalks of ideal-module products, quotients, and powers

Source: literature/stacks-project/modules.tex, Lemmas 01AG and 01CB, as used in
Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The product `𝒥𝓕 ⊆ 𝓕` of a sheaf of ideals `ι : 𝒥 ⟶ 𝒪_X` and an `𝒪_X`-module `𝓕`:
the image of the multiplication map `𝒥 ⊗ 𝓕 ⟶ 𝒪_X ⊗ 𝓕 ≅ 𝓕`, `a ⊗ s ↦ a s`.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealModuleProduct {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : X.Modules :=
  letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  image (ι ▷ F ≫ (λ_ F).hom)

/-- The inclusion `𝒥𝓕 ⟶ 𝓕` of the product of a sheaf of ideals and a module.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealModuleProductι {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    idealModuleProduct ι F ⟶ F :=
  letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  image.ι (ι ▷ F ≫ (λ_ F).hom)

/-- The powers `𝒥ⁿ ⊆ 𝒪_X` of a sheaf of ideals, with their inclusions into `𝒪_X`:
`𝒥¹ = 𝒥` and `𝒥ⁿ⁺¹ = 𝒥 · 𝒥ⁿ ⊆ 𝒥ⁿ ⊆ 𝒪_X`; the value at `0` is `𝒪_X` and is not used.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealSheafPower {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ℕ → Σ P : X.Modules, P ⟶ SheafOfModules.unit X.ringCatSheaf
  | 0 => ⟨SheafOfModules.unit X.ringCatSheaf, 𝟙 _⟩
  | 1 => ⟨J, ι⟩
  | n + 2 => ⟨idealModuleProduct ι (idealSheafPower ι (n + 1)).1,
      idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫ (idealSheafPower ι (n + 1)).2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_iso (X : Scheme.{u}) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
  let D := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : Γ(X, U ⊓ V) :=
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
  exact hg

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_mono {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (x : X) :
    Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f).hom := by
  have h := (RingedSpace.module_stalk_exact X.toRingedSpace f).1
  have hm : Mono ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f) := by
    apply h
    intro U
    have : Mono f.val := (SheafOfModules.forget _).map_mono f
    exact (ModuleCat.mono_iff_injective (f.val.app (Opposite.op U))).mp inferInstance
  exact (ModuleCat.mono_iff_injective _).mp hm

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_quotient {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (P : Submodule (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj N))
    (hP : LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f).hom
      = P) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ φ : (S.obj N ⧸ P) ≃ₗ[X.presheaf.stalk x] S.obj (cokernel f),
      ∀ m : S.obj N, φ (Submodule.Quotient.mk m) = (S.map (cokernel.π f)).hom m := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨hepi, hexact⟩ := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x
  have hker : LinearMap.ker (S.map (cokernel.π f)).hom = P :=
    hexact.moduleCat_range_eq_ker.symm.trans hP
  have hsurj := (ModuleCat.epi_iff_surjective (S.map (cokernel.π f))).mp hepi
  let q : S.obj N →ₗ[X.presheaf.stalk x] S.obj (cokernel f) :=
    (S.map (cokernel.π f)).hom
  let e := (Submodule.quotEquivOfEq P (LinearMap.ker q) hker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)
  refine ⟨e, fun m ↦ ?_⟩
  exact q.quotKerEquivOfSurjective_apply_mk hsurj m


set_option backward.isDefEq.respectTransparency false in
/-- Stalks of ideal sheaves, of products `𝒥𝓕`, of quotients `𝓕/𝒥𝓕` and of powers.
Let `ι : 𝒥 ⟶ 𝒪_X` be a sheaf of ideals, `𝓕` an `𝒪_X`-module and `x ∈ X`; `e` is the
identification of the stalk of `𝒪_X` with `𝒪_{X,x}` (germs to germs) and `I` the image of
`𝒥_x` in `𝒪_{X,x}`. Then `𝒥_x ⟶ 𝒪_{X,x}` and `(𝒥𝓕)_x ⟶ 𝓕_x` are injective,
`(𝒥𝓕)_x = I 𝓕_x`, the stalk of `𝓕 ⟶ 𝓕/𝒥𝓕` induces `𝓕_x / I 𝓕_x ≅ (𝓕/𝒥𝓕)_x`, and for
`n ≥ 1`: `(𝒥ⁿ)_x = Iⁿ`, `(𝒥ⁿ𝓕)_x = Iⁿ 𝓕_x` and `𝓕_x / Iⁿ 𝓕_x ≅ (𝓕/𝒥ⁿ𝓕)_x`.
Source: Stacks Project, Modules, Lemmas 01AG and 01CB; Cohomology of Schemes,
proof of Lemma 0CYV (blueprint: lem-weil-pbc-ideal-module-product-stalk).

Proof: the stalk functor is exact (Modules, Lemma 01AG), so it preserves monomorphisms,
images and cokernels; this gives the injectivity of `𝒥_x ⟶ 𝒪_{X,x}` and of
`(𝒥𝓕)_x ⟶ 𝓕_x`, and `(𝓕/𝒥𝓕)_x = 𝓕_x/(𝒥𝓕)_x`. By Lemma 01CB the stalk of
`𝒥 ⊗ 𝓕 ⟶ 𝓕` is the multiplication `𝒥_x ⊗ 𝓕_x ⟶ 𝓕_x`, whose image is `𝒥_x 𝓕_x`;
this is (2), and (3) follows. For (4) induct on `n`: `(𝒥ⁿ⁺¹)_x = 𝒥_x (𝒥ⁿ)_x =
I · Iⁿ = Iⁿ⁺¹` by (2) applied to `𝓕 = 𝒥ⁿ`, and the remaining two claims are (2) and (3)
for the ideal `𝒥ⁿ`. -/
theorem ideal_module_product_stalk {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] (F : X.Modules) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r) ∧
      let I : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map ι ≫ e.hom).hom
      Function.Injective (S.map ι).hom ∧
      Function.Injective (S.map (idealModuleProductι ι F)).hom ∧
      LinearMap.range (S.map (idealModuleProductι ι F)).hom = I • ⊤ ∧
      (∃ φ : (S.obj F ⧸ I • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F))) ≃ₗ[
          X.presheaf.stalk x] S.obj (cokernel (idealModuleProductι ι F)),
        ∀ m : S.obj F, φ (Submodule.Quotient.mk m) =
          (S.map (cokernel.π (idealModuleProductι ι F))).hom m) ∧
      ∀ n : ℕ, 1 ≤ n →
        let Jn := idealSheafPower ι n
        LinearMap.range (S.map Jn.2 ≫ e.hom).hom = I ^ n ∧
        LinearMap.range (S.map (idealModuleProductι Jn.2 F)).hom = I ^ n • ⊤ ∧
        ∃ φ : (S.obj F ⧸ I ^ n • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F))) ≃ₗ[
            X.presheaf.stalk x] S.obj (cokernel (idealModuleProductι Jn.2 F)),
          ∀ m : S.obj F, φ (Submodule.Quotient.mk m) =
            (S.map (cokernel.π (idealModuleProductι Jn.2 F))).hom m := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨e, he⟩ := unit_stalk_iso X x
  let I : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map ι ≫ e.hom).hom
  have hrange {K : X.Modules} (j : K ⟶ SheafOfModules.unit X.ringCatSheaf)
      (M : X.Modules) : LinearMap.range (S.map (idealModuleProductι j M)).hom =
        (LinearMap.range (S.map j ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) • ⊤ := by
    exact ideal_multiplication_stalk_range j M x e he
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have hprod (M : X.Modules) : Mono (idealModuleProductι ι M) := by
    dsimp [idealModuleProductι]
    infer_instance
  have hpowers : ∀ n : ℕ, 1 ≤ n →
      LinearMap.range (S.map (idealSheafPower ι n).2 ≫ e.hom).hom = I ^ n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    induction k with
    | zero => simp [idealSheafPower, I]
    | succ k ih =>
      rw [show 1 + (k + 1) = k + 2 by omega]
      change LinearMap.range
        (S.map (idealModuleProductι ι (idealSheafPower ι (k + 1)).1 ≫
          (idealSheafPower ι (k + 1)).2) ≫ e.hom).hom = _
      rw [S.map_comp, Category.assoc, ModuleCat.hom_comp, LinearMap.range_comp]
      have ih' : LinearMap.range (S.map (idealSheafPower ι (k + 1)).2 ≫ e.hom).hom =
          I ^ (k + 1) := by
        rw [Nat.add_comm 1 k] at ih
        exact ih
      rw [hrange, Submodule.map_smul'', Submodule.map_top, ih', Ideal.smul_eq_mul]
      change I * I ^ (k + 1) = I ^ (k + 2)
      rw [mul_comm, ← pow_succ]
  refine ⟨e, he, stalk_mono ι x, stalk_mono (idealModuleProductι ι F) x,
    hrange ι F, stalk_quotient (idealModuleProductι ι F) x _ (hrange ι F), ?_⟩
  intro n hn
  have hp := hpowers n hn
  have hr := hrange (idealSheafPower ι n).2 F
  rw [hp] at hr
  exact ⟨hp, hr, stalk_quotient (idealModuleProductι (idealSheafPower ι n).2 F) x _ hr⟩

end

end AlgebraicGeometry.Scheme
