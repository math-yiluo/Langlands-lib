/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FrobeniusChangeOfRings
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The Frobenius unit followed by multiplication

Let `F` be a Frobenius system for a morphism `φ : R ⟶ S` of sheaves of commutative rings, with
unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n` (`SheafOfModules.FrobeniusSystem.unitHom`). Composing the unit with the
multiplication map `S ⊗_R N ⟶ N`, `s ⊗ n ↦ s n`, gives multiplication by the section
`∑ᵢ bᵢ cᵢ` (`SheafOfModules.FrobeniusSystem.unitHom_comp_val_app`).

We also record that for the Frobenius dual basis `b'` of a basis `b` with respect to a Frobenius
form `t`, `t (∑ᵢ bᵢ b'ᵢ)` is the rank (`ModuleCat.CoextendScalars.apply_sum_mul_frobeniusDual`),
and define multiplication by a compatible family of sections (`SheafOfModules.smulSections`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace ModuleCat.CoextendScalars

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι R S) (φ : S →ₗ[R] R)
  (hφ : Function.Bijective fun s : S ↦ φ ∘ₗ LinearMap.mulLeft R s)

/-- The Frobenius form takes the value `rank` on `∑ᵢ bᵢ b'ᵢ`, where `b'` is the Frobenius dual
basis of `b`. -/
lemma apply_sum_mul_frobeniusDual :
    φ (∑ i, b i * frobeniusDual b φ hφ i) = Fintype.card ι := by
  classical
  simp only [map_sum, mul_comm (b _), apply_frobeniusDual_mul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- For a Frobenius form over a ring of characteristic zero and a nonempty basis, the element
`∑ᵢ bᵢ b'ᵢ` is nonzero. -/
lemma sum_mul_frobeniusDual_ne_zero [CharZero R] [Nonempty ι] :
    ∑ i, b i * frobeniusDual b φ hφ i ≠ 0 := by
  intro h
  have h' := apply_sum_mul_frobeniusDual b φ hφ
  rw [h, map_zero] at h'
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 h'.symm)

end ModuleCat.CoextendScalars

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Multiples of a morphism of sheaves of modules act as multiples on sections. -/
lemma nsmul_val_app {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (n : ℕ) (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) : (n • f).val.app U x = n • f.val.app U x := by
  induction n with
  | zero =>
    rw [zero_smul, zero_smul]
    rfl
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul, add_val, PresheafOfModules.add_app, ← ih]
    rfl

section SMulSections

variable {R : Sheaf J CommRingCat.{u}} (s : ∀ U : Cᵒᵖ, (𝓡 R).obj.obj U)
  (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), (𝓡 R).obj.map f (s U) = s V)

/-- Multiplication by a family of sections of a sheaf of commutative rings which is compatible
with restrictions, as an endomorphism of the identity functor of sheaves of modules. -/
def smulSections : 𝟭 (SheafOfModules.{u} (𝓡 R)) ⟶ 𝟭 (SheafOfModules.{u} (𝓡 R)) where
  app M :=
    { val :=
        { app U :=
            letI : CommRing ((𝓡 R).obj.obj U) := inferInstanceAs (CommRing (R.obj.obj U))
            ModuleCat.ofHom
              { toFun x := s U • x
                map_add' := smul_add _
                map_smul' r x := smul_comm _ r x }
          naturality {U V} f := by
            ext x
            change s V • M.val.map f x =
              M.val.map f (s U • x)
            rw [M.val.map_smul, hs f] } }
  naturality M N g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((g.val.app U).hom.map_smul (s U) x).symm

@[simp]
lemma smulSections_app_val_app (M : SheafOfModules.{u} (𝓡 R)) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((smulSections s hs).app M).val.app U x = s U • x :=
  rfl

end SMulSections

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} {φ : R ⟶ S} {d : ℕ}

namespace FrobeniusSystem

/-- The Frobenius unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n` followed by a multiplication map
`S ⊗_R N ⟶ N` (a map sending `1 ⊗ n` to `n`) is multiplication by `∑ᵢ bᵢ cᵢ`. -/
lemma unitHom_comp_val_app (F : FrobeniusSystem φ d) (N : SheafOfModules.{u} (𝓡 S))
    (g : changeOfRings φ ((restrictScalars (𝓻 φ)).obj N) ⟶ N)
    (hg : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      g.val.app U ((toChangeOfRings ((restrictScalars (𝓻 φ)).obj N)).app U
        (ModuleCat.FrobeniusData.tmulRes (φ.hom.app U).hom (N.val.obj U) 1 x)) = x)
    (U : Cᵒᵖ) (x : N.val.obj U) :
    (F.unitHom N ≫ g).val.app U x =
      (∑ i, (F.data U).basis i * (F.data U).dual i : (𝓡 S).obj.obj U) • x := by
  change g.val.app U ((toChangeOfRings _).app U ((F.data U).unitApp _ x)) = _
  let : CommRing ((𝓡 S).obj.obj U) := inferInstanceAs (CommRing (S.obj.obj U))
  erw [ModuleCat.FrobeniusData.unitApp_apply, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := ModuleCat.FrobeniusData.smul_tmulRes (f := (φ.hom.app U).hom) (N.val.obj U)
    ((F.data U).basis i) 1 (@id ((𝓡 S).obj.obj U) ((F.data U).dual i) • x)
  rw [mul_one] at h
  erw [← h, ((toChangeOfRings ((restrictScalars (𝓻 φ)).obj N)).app U).hom.map_smul,
    (g.val.app U).hom.map_smul, hg, mul_smul]
  rfl

/-- The Frobenius counit `s ⊗ m ↦ t(s) m` on the image of a sectionwise pure tensor. -/
lemma counitHom_val_app_toChangeOfRings (F : FrobeniusSystem φ d) {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (F.counitHom e M).val.app U ((toChangeOfRings M).app U
      (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) s m)) =
      (F.data U).trace s • m := by
  exact congrArg (fun f ↦ (f.app U).hom
    (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) s m))
    (F.map_toChangeOfRings_comp_counitHom_val e M)

/-- A map `g : M ⟶ Res (S ⊗_R M)` sending `m` to `1 ⊗ m`, followed by multiplication by
sections `s` and `t` and the Frobenius counit, is multiplication by `t(t * s)`. -/
lemma unit_smul_smul_counitHom_val_app (F : FrobeniusSystem φ d) {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (g : M ⟶ (restrictScalars (𝓻 φ)).obj (changeOfRings φ M))
    (hg : ∀ (U : Cᵒᵖ) (m : M.val.obj U), g.val.app U m = (toChangeOfRings M).app U
      (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) 1 m))
    (s : ∀ U : Cᵒᵖ, (𝓡 S).obj.obj U) (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), (𝓡 S).obj.map f (s U) = s V)
    (t : ∀ U : Cᵒᵖ, (𝓡 S).obj.obj U) (ht : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), (𝓡 S).obj.map f (t U) = t V)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (g ≫ (restrictScalars (𝓻 φ)).map ((smulSections s hs).app _) ≫
      (restrictScalars (𝓻 φ)).map ((smulSections t ht).app _) ≫ F.counitHom e M).val.app U m =
      (F.data U).trace (t U * s U) • m := by
  change (F.counitHom e M).val.app U (@HSMul.hSMul ((𝓡 S).obj.obj U)
    ((changeOfRings φ M).val.obj U) _ _ (t U) (@HSMul.hSMul ((𝓡 S).obj.obj U)
      ((changeOfRings φ M).val.obj U) _ _ (s U) (g.val.app U m))) = _
  rw [hg]
  erw [← ((toChangeOfRings M).app U).hom.map_smul, ← ((toChangeOfRings M).app U).hom.map_smul]
  let : CommRing ((𝓡 S).obj.obj U) := inferInstanceAs (CommRing (S.obj.obj U))
  erw [ModuleCat.FrobeniusData.smul_tmulExt]
  refine (F.counitHom_val_app_toChangeOfRings e M U _ m).trans ?_
  simp

/-- The Frobenius coordinates reconstruct: for `g : M ⟶ Res (S ⊗_R M)` sending `m` to `1 ⊗ m`,
`∑ⱼ bⱼ • g (t(cⱼ -))` is the identity of `Res (S ⊗_R M)`, i.e. `s ⊗ m = ∑ⱼ bⱼ ⊗ t(cⱼ s) m`. -/
lemma sum_smul_counitHom_unit_smul (F : FrobeniusSystem φ d) {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (g : M ⟶ (restrictScalars (𝓻 φ)).obj (changeOfRings φ M))
    (hg : ∀ (U : Cᵒᵖ) (m : M.val.obj U), g.val.app U m = (toChangeOfRings M).app U
      (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) 1 m)) :
    ∑ j, (restrictScalars (𝓻 φ)).map ((smulSections (fun U ↦ (F.data U).dual j)
        (fun f ↦ F.dual_naturality j f)).app _) ≫ F.counitHom e M ≫ g ≫
      (restrictScalars (𝓻 φ)).map ((smulSections (fun U ↦ (F.data U).basis j)
        (fun f ↦ F.basis_naturality j f)).app _) = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have := isIso_toChangeOfRings e M
  have : IsIso ((toChangeOfRings (φ := φ) M).app U) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation (𝓡 S).obj U).map
      (toChangeOfRings (φ := φ) M)))
  obtain ⟨z, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso ((toChangeOfRings (φ := φ) M).app U)).2 y
  let : CommRing ((𝓡 S).obj.obj U) := inferInstanceAs (CommRing (S.obj.obj U))
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    have hterm (j : Fin d) : ((restrictScalars (𝓻 φ)).map ((smulSections
        (fun U ↦ (F.data U).dual j) (fun f ↦ F.dual_naturality j f)).app _) ≫
          F.counitHom e M ≫ g ≫ (restrictScalars (𝓻 φ)).map ((smulSections
            (fun U ↦ (F.data U).basis j) (fun f ↦ F.basis_naturality j f)).app _)).val.app U
          ((toChangeOfRings M).app U
            (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) s m)) =
        (toChangeOfRings M).app U (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom
          (M.val.obj U) ((φ.hom.app U) ((F.data U).trace
            ((F.data U).dual j * @id (S.obj.obj U) s)) * ((F.data U).basis j * 1)) m) := by
      change @HSMul.hSMul ((𝓡 S).obj.obj U) ((changeOfRings φ M).val.obj U) _ _
        ((F.data U).basis j) (g.val.app U ((F.counitHom e M).val.app U
          (@HSMul.hSMul ((𝓡 S).obj.obj U) ((changeOfRings φ M).val.obj U) _ _
            ((F.data U).dual j) ((toChangeOfRings M).app U
              (ModuleCat.FrobeniusData.tmulExt (φ.hom.app U).hom (M.val.obj U) s m))))) = _
      erw [← ((toChangeOfRings M).app U).hom.map_smul, ModuleCat.FrobeniusData.smul_tmulExt,
        F.counitHom_val_app_toChangeOfRings e M U, (g.val.app U).hom.map_smul, hg]
      rw [mul_left_comm,
        ← ModuleCat.FrobeniusData.smul_tmulExt, ← ModuleCat.FrobeniusData.smul_tmulExt]
      erw [((toChangeOfRings M).app U).hom.map_smul, ((toChangeOfRings M).app U).hom.map_smul]
      rfl
    erw [sum_val_app_apply, Finset.sum_congr rfl fun j _ ↦ hterm j, ← map_sum,
      ← ModuleCat.FrobeniusData.tmulExt_sum_left]
    simp only [mul_one, mul_comm ((F.data U).dual _)]
    erw [(F.data U).sum_trace_mul_dual]
    rfl

end FrobeniusSystem

end SheafOfModules
