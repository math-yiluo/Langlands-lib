/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.FrobeniusExtendScalars
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension

/-!
# Frobenius reciprocity for finite free change of rings of sheaves of modules

Let `φ : R ⟶ S` be a morphism of sheaves of commutative rings. A *Frobenius system* for `φ`
(`SheafOfModules.FrobeniusSystem`) is a family of Frobenius data
(`ModuleCat.FrobeniusData`) for the ring maps `R(V) ⟶ S(V)` which is compatible with
restrictions: an `R`-linear trace `t : S → R` and two finite families `(bᵢ)`, `(cᵢ)` of
sections of `S` with `x = ∑ᵢ t(x cᵢ) bᵢ = ∑ᵢ t(x bᵢ) cᵢ`.

If `S` is moreover finite free over `R`, restriction of scalars along `φ` is left adjoint to the
change of rings `S ⊗_R -` (`SheafOfModules.FrobeniusSystem.adjunction`): the unit is
`n ↦ ∑ᵢ bᵢ ⊗ cᵢ n` and the counit is `s ⊗ m ↦ t(s) m`, computed on sections since the sectionwise
tensor product is already a sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}

/-- A Frobenius system for a morphism `φ : R ⟶ S` of sheaves of commutative rings: Frobenius
data for every ring map `R(V) ⟶ S(V)`, compatible with restrictions. -/
structure FrobeniusSystem (φ : R ⟶ S) (d : ℕ) where
  /-- The Frobenius data on sections. -/
  data (V : Cᵒᵖ) : ModuleCat.FrobeniusData (φ.hom.app V).hom d
  trace_naturality {V W : Cᵒᵖ} (f : V ⟶ W) (x : S.obj.obj V) :
    R.obj.map f ((data V).trace x) = (data W).trace (S.obj.map f x)
  basis_naturality (i : Fin d) {V W : Cᵒᵖ} (f : V ⟶ W) :
    S.obj.map f ((data V).basis i) = (data W).basis i
  dual_naturality (i : Fin d) {V W : Cᵒᵖ} (f : V ⟶ W) :
    S.obj.map f ((data V).dual i) = (data W).dual i

section OfBasis

variable {φ : R ⟶ S} {d : ℕ} {A' B' : Type w} [CommRing A'] [CommRing B'] [Algebra A' B']
  (b : Module.Basis (Fin d) A' B') (t₀ : B' →ₗ[A'] A')
  (ht₀ : Function.Bijective fun s : B' ↦ t₀ ∘ₗ LinearMap.mulLeft A' s)
  (κA : ∀ V : Cᵒᵖ, A' →+* R.obj.obj V) (κB : ∀ V : Cᵒᵖ, B' →+* S.obj.obj V)
  (hκA : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : A'), R.obj.map f (κA V a) = κA W a)
  (hκB : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : B'), S.obj.map f (κB V a) = κB W a)
  (hκ : ∀ (V : Cᵒᵖ) (a : A'), φ.hom.app V (κA V a) = κB V (algebraMap A' B' a))
  (hbij : ∀ V : Cᵒᵖ, Function.Bijective fun r : Fin d → R.obj.obj V ↦
    ∑ i, φ.hom.app V (r i) * κB V (b i))

include hκB in
lemma coords_naturality {V W : Cᵒᵖ} (f : V ⟶ W) (x : S.obj.obj V) :
    ModuleCat.FrobeniusData.coords b (κB W) (hbij W) (S.obj.map f x) =
      fun i ↦ R.obj.map f (ModuleCat.FrobeniusData.coords b (κB V) (hbij V) x i) := by
  refine ModuleCat.FrobeniusData.coords_eq b (κB W) (hbij W) ?_
  conv_rhs => rw [← ModuleCat.FrobeniusData.sum_coords b (κB V) (hbij V) x]
  simp only [map_sum, map_mul, hκB]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

/-- The Frobenius system obtained by base change of a basis `b` and a Frobenius form `t₀` of a
finite free algebra `A' → B'`, along compatible ring maps `κA : A' → R`, `κB : B' → S` such that
the sections `κB (b i)` form a basis of `S` over `R`. -/
def FrobeniusSystem.ofBasis : FrobeniusSystem φ d where
  data V := ModuleCat.FrobeniusData.ofBasis b (κA V) (κB V) (hκ V) (hbij V) t₀ ht₀
  trace_naturality {V W} f x := by
    change R.obj.map f (ModuleCat.FrobeniusData.ofBasisTrace b (κA V) (κB V) (hbij V) t₀ x) =
      ModuleCat.FrobeniusData.ofBasisTrace b (κA W) (κB W) (hbij W) t₀ (S.obj.map f x)
    simp only [ModuleCat.FrobeniusData.ofBasisTrace, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [coords_naturality b κB hκB hbij f x, map_sum]
    simp only [map_mul, hκA]
  basis_naturality i _ _ f := hκB f (b i)
  dual_naturality i _ _ f := hκB f _

end OfBasis

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

namespace FrobeniusSystem

variable {φ : R ⟶ S} {d : ℕ} (F : FrobeniusSystem φ d)

/-- The unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n`, before sheafification. -/
def unitPresheaf (N : SheafOfModules.{u} (𝓡 S)) :
    N.val ⟶ changeOfRingsPresheaf φ ((restrictScalars (𝓻 φ)).obj N) where
  app V := (F.data V).unitApp (N.val.obj V)
  naturality {V W} f := by
    ext n
    change (F.data W).unitApp _ (N.val.map f n) =
      changeOfRingsMap φ ((restrictScalars (𝓻 φ)).obj N) f ((F.data V).unitApp _ n)
    erw [(F.data W).unitApp_apply, (F.data V).unitApp_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Eq.trans ?_ (changeMap_tmul φ ((restrictScalars (𝓻 φ)).obj N) f _ _).symm
    erw [F.basis_naturality]
    congr 1
    exact ((N.val.map_smul f _ n).trans
      (congrArg (· • N.val.map f n) (F.dual_naturality i f))).symm

/-- The counit `s ⊗ m ↦ t(s) m`, before sheafification. -/
def counitPresheaf (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf φ M) ⟶ M.val where
  app V := (F.data V).counitApp (M.val.obj V)
  naturality {V W} f := by
    ext z
    change (F.data W).counitApp _ (changeOfRingsMap φ M f z) =
      M.val.map f ((F.data V).counitApp _ z)
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => erw [map_add, map_add, hz, hz', map_add, map_add]
    | tmul s m =>
      refine (congrArg _ (changeMap_tmul φ M f s m)).trans ?_
      exact (congrArg (· • (show M.val.obj W from M.val.map f m))
        (F.trace_naturality f s)).symm.trans
        (M.val.map_smul f _ m).symm
end FrobeniusSystem

/-- The sheafification unit from sectionwise change of rings to change of rings. -/
def toChangeOfRings {φ : R ⟶ S} (M : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsPresheaf φ M ⟶ (changeOfRings φ M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app _

/-- If `S` is finite free over `R`, the sectionwise change of rings is already a sheaf. -/
lemma isIso_toChangeOfRings {φ : R ⟶ S} {d : ℕ}
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) : IsIso (toChangeOfRings (φ := φ) M) := by
  have := SheafOfModules.tensorUnit_isIso φ d e M
  unfold SheafOfModules.tensorUnit at this
  exact this

/-- Sectionwise change of rings of a morphism of sheaves of modules. -/
def changeOfRingsPresheafMap (φ : R ⟶ S) {M N : SheafOfModules.{u} (𝓡 R)} (h : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N where
  app V := (ModuleCat.extendScalars (φ.hom.app V).hom).map (h.val.app V)
  naturality := changeOfRingsHom_naturality φ M h

lemma toChangeOfRings_naturality {φ : R ⟶ S} {M N : SheafOfModules.{u} (𝓡 R)} (h : M ⟶ N) :
    toChangeOfRings M ≫ (changeOfRingsHom φ M h).val =
      changeOfRingsPresheafMap φ h ≫ toChangeOfRings N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.naturality
    (changeOfRingsPresheafMap φ h)).symm

/-- Change of rings `S ⊗_R -` along `φ`, as a functor. -/
def changeOfRingsFunctor (φ : R ⟶ S) : SheafOfModules.{u} (𝓡 R) ⥤ SheafOfModules.{u} (𝓡 S) where
  obj := changeOfRings φ
  map {M _} h := changeOfRingsHom φ M h
  map_id M := by
    refine (congrArg (PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map ?_).trans
      ((PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map_id _)
    ext V : 1
    exact (ModuleCat.extendScalars _).map_id _
  map_comp {M _ _} g h := by
    refine (congrArg (PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map ?_).trans
      ((PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map_comp _ _)
    ext V : 1
    exact (ModuleCat.extendScalars _).map_comp _ _

namespace FrobeniusSystem

variable {φ : R ⟶ S} {d : ℕ} (F : FrobeniusSystem φ d)

/-- The unit `n ↦ ∑ᵢ bᵢ ⊗ cᵢ n`. -/
def unitHom (N : SheafOfModules.{u} (𝓡 S)) :
    N ⟶ changeOfRings φ ((restrictScalars (𝓻 φ)).obj N) :=
  ⟨F.unitPresheaf N ≫ toChangeOfRings _⟩

/-- The counit `s ⊗ m ↦ t(s) m`, using that the sectionwise tensor product is a sheaf. -/
def counitHom {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (restrictScalars (𝓻 φ)).obj (changeOfRings φ M) ⟶ M :=
  haveI := isIso_toChangeOfRings e M
  ⟨(PresheafOfModules.restrictScalars (𝓻 φ).hom).map (inv (toChangeOfRings M)) ≫
    F.counitPresheaf M⟩

lemma map_toChangeOfRings_comp_counitHom_val {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (toChangeOfRings M) ≫
      (F.counitHom e M).val = F.counitPresheaf M := by
  have := isIso_toChangeOfRings e M
  change _ ≫ (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (inv (toChangeOfRings M)) ≫ _ = _
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]


/-- **Frobenius reciprocity**: for a Frobenius system on a finite free morphism `φ` of sheaves of
commutative rings, restriction of scalars along `φ` is left adjoint to change of rings. -/
def adjunction {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S))) :
    restrictScalars (𝓻 φ) ⊣ changeOfRingsFunctor φ :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := F.unitHom
          naturality N N' g := by
            apply SheafOfModules.hom_ext
            change g.val ≫ F.unitPresheaf N' ≫ toChangeOfRings _ =
              (F.unitPresheaf N ≫ toChangeOfRings _) ≫
                (changeOfRingsHom φ _ ((restrictScalars (𝓻 φ)).map g)).val
            rw [Category.assoc, toChangeOfRings_naturality, ← Category.assoc, ← Category.assoc]
            congr 1
            ext V : 1
            exact (F.data V).unitApp_naturality (g.val.app V) }
      counit :=
        { app := F.counitHom e
          naturality M M' h := by
            apply SheafOfModules.hom_ext
            have := isIso_toChangeOfRings e M
            apply (cancel_epi ((PresheafOfModules.restrictScalars (𝓻 φ).hom).map
              (toChangeOfRings M))).1
            change _ ≫ (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
                (changeOfRingsHom φ M h).val ≫ (F.counitHom e M').val =
              _ ≫ (F.counitHom e M).val ≫ h.val
            rw [← Functor.map_comp_assoc, toChangeOfRings_naturality, Functor.map_comp_assoc,
              map_toChangeOfRings_comp_counitHom_val, ← Category.assoc,
              map_toChangeOfRings_comp_counitHom_val]
            ext V : 1
            exact (F.data V).counitApp_naturality (h.val.app V) }
      left_triangle := by
        ext N : 2
        dsimp
        rw [Category.id_comp]
        apply SheafOfModules.hom_ext
        change (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
            (F.unitPresheaf N ≫ toChangeOfRings _) ≫ (F.counitHom e _).val = 𝟙 _
        rw [Functor.map_comp_assoc, map_toChangeOfRings_comp_counitHom_val]
        ext V : 1
        exact (F.data V).restrictScalars_map_unitApp_comp_counitApp (N.val.obj V)
      right_triangle := by
        ext M : 2
        dsimp
        rw [Category.id_comp]
        apply SheafOfModules.hom_ext
        have := isIso_toChangeOfRings e M
        apply (cancel_epi (toChangeOfRings M)).1
        change toChangeOfRings M ≫ (F.unitPresheaf _ ≫ toChangeOfRings _) ≫
            (changeOfRingsHom φ _ (F.counitHom e M)).val = toChangeOfRings M ≫ 𝟙 _
        rw [Category.assoc, toChangeOfRings_naturality, Category.comp_id, ← Category.assoc,
          ← Category.assoc]
        refine Eq.trans ?_ (Category.id_comp _)
        congr 1
        ext V : 1
        have h := congrArg (fun g ↦ g.app V) (F.map_toChangeOfRings_comp_counitHom_val e M)
        change (toChangeOfRings M).app V ≫ (F.data V).unitApp _ ≫
          (ModuleCat.extendScalars _).map ((F.counitHom e M).val.app V) = 𝟙 _
        rw [← Category.assoc, (F.data V).unitApp_naturality, Category.assoc,
          ← Functor.map_comp]
        exact (congrArg (fun g ↦ (F.data V).unitApp _ ≫ (ModuleCat.extendScalars _).map g) h).trans
          ((F.data V).unitApp_comp_extendScalars_map_counitApp (M.val.obj V)) }

/-- Frobenius reciprocity for any functor which is, objectwise and on morphisms, change of rings
along `φ`. -/
theorem nonempty_adjunction (F : FrobeniusSystem φ d) {d' : ℕ}
    (e : (∏ᶜ fun _ : Fin d' ↦ unit (𝓡 R)) ≅ (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (G : SheafOfModules.{u} (𝓡 R) ⥤ SheafOfModules.{u} (𝓡 S))
    (hobj : ∀ M, G.obj M = changeOfRings φ M)
    (hmap : ∀ {M N : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ N),
      G.map f = eqToHom (hobj M) ≫ changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    Nonempty (restrictScalars (𝓻 φ) ⊣ G) :=
  ⟨(F.adjunction e).ofNatIsoRight
    (NatIso.ofComponents (fun M ↦ eqToIso (hobj M).symm) fun f ↦ by
      simp [hmap, changeOfRingsFunctor])⟩

end FrobeniusSystem

end SheafOfModules
