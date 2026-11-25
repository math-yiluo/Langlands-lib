/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Module.ZMod

/-!
# Abelian sheaves killed by `N` are modules over the constant sheaf `ℤ/N`

Let `J` be a Grothendieck topology on a category `C` and `N ≥ 1`. Write `(ℤ/N)_C` for the
constant sheaf of rings with value `ℤ/N` (`CategoryTheory.Sheaf.constantZModSheaf`), the
sheafification of the constant presheaf of rings, and `η : ℤ/N ⟶ (ℤ/N)_C` for the unit
(`CategoryTheory.Sheaf.constantZModUnit`).

Every sheaf of `(ℤ/N)_C`-modules is killed by `N`, and a constant section `η(a)` acts on it as
multiplication by any integer representative of `a`. Conversely an abelian sheaf `F` killed by
`N` carries a structure of sheaf of `(ℤ/N)_C`-modules, unique up to unique isomorphism, and
every morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules is `(ℤ/N)_C`-linear: the
forgetful functor `SheafOfModules (ℤ/N)_C ⥤ Sheaf J AddCommGrpCat` is fully faithful with
essential image the sheaves killed by `N` (Stacks 03CY).

## Main definitions

- `CategoryTheory.Sheaf.constantZModSheaf`: the constant sheaf of rings `(ℤ/N)_C`.
- `CategoryTheory.Sheaf.constantZModUnit`: the unit `ℤ/N ⟶ (ℤ/N)_C` of the sheafification.

## Main statements

- `CategoryTheory.Sheaf.constantZModUnit_smul`: `η(a)` acts as multiplication by `a.val`.
- `CategoryTheory.Sheaf.nsmul_eq_zero_of_constantZMod`: sheaves of `(ℤ/N)_C`-modules are killed
  by `N`.
- `CategoryTheory.Sheaf.full_toSheaf_constantZMod`: morphisms of abelian sheaves are linear.
- `CategoryTheory.Sheaf.exists_constantZModModule_iff`: the essential image of the forgetful
  functor is the sheaves killed by `N`.
- `CategoryTheory.Sheaf.torsionSheaf_constantModule`: blueprint
  `definition-tate-twists`.

## Implementation notes

The proof follows the étale special case
`AlgebraicGeometry.Etale.constantRing_moduleSheaf_equivalence`:
over the constant *presheaf* of rings `ℤ/N` the restriction maps of a presheaf of modules are
`ℤ/N`-linear, so presheaves of modules over it are presheaves of `ℤ/N`-modules, and Mathlib's
restriction of scalars along the locally bijective unit `η` is fully faithful on sheaves of
modules (`PresheafOfModules.sheafification`).
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (N : ℕ)
  [HasWeakSheafify J RingCat.{w}]

/-- The constant presheaf of rings with value `ℤ/N`. -/
abbrev constantZModPresheaf : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{w} (ZMod N)))

/-- The constant sheaf of rings `(ℤ/N)_C`: the sheafification of the constant presheaf of
rings with value `ℤ/N`. -/
noncomputable abbrev constantZModSheaf : Sheaf J RingCat.{w} :=
  (constantSheaf J RingCat.{w}).obj (RingCat.of (ULift.{w} (ZMod N)))

/-- The unit `ℤ/N ⟶ (ℤ/N)_C` of the sheafification of the constant presheaf of rings. -/
noncomputable abbrev constantZModUnit : constantZModPresheaf N ⟶ (constantZModSheaf J N).obj :=
  toSheafify J (constantZModPresheaf N)

variable {J N}

/-- A constant section `η(a)` of `(ℤ/N)_C`, `a ∈ ℤ/N`, acts on a sheaf of `(ℤ/N)_C`-modules as
multiplication by the integer representative `a.val` of `a` (or any other one, since the sheaf
is killed by `N`: `CategoryTheory.Sheaf.nsmul_eq_zero_of_constantZMod`). -/
lemma constantZModUnit_smul [NeZero N] (M : SheafOfModules.{w} (constantZModSheaf J N))
    {U : Cᵒᵖ} (a : ZMod N) (x : M.val.obj U) :
    (constantZModUnit J N).app U ⟨a⟩ • x = a.val • x := by
  have : (⟨a⟩ : ULift.{w} (ZMod N)) = (a.val : ULift.{w} (ZMod N)) :=
    ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
  rw [this, map_natCast, Nat.cast_smul_eq_nsmul]

/-- A sheaf of `(ℤ/N)_C`-modules is killed by `N`. -/
lemma nsmul_eq_zero_of_constantZMod (M : SheafOfModules.{w} (constantZModSheaf J N))
    {U : Cᵒᵖ} (x : M.val.obj U) : N • x = 0 := by
  have h : (N : ULift.{w} (ZMod N)) = 0 :=
    ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_self]; rfl)
  have h' : ((constantZModUnit J N).app U).hom (N : ULift.{w} (ZMod N)) =
      (N : (constantZModSheaf J N).obj.obj U) := map_natCast _ N
  rw [← Nat.cast_smul_eq_nsmul (R := (constantZModSheaf J N).obj.obj U), ← h', h, map_zero,
    zero_smul]

variable [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The morphism of presheaves of modules over the constant presheaf `ℤ/N` underlying a
morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules: additive maps between
`ℤ/N`-modules are `ℤ/N`-linear. -/
noncomputable def restrictScalarsHomOfToSheaf [NeZero N]
    {M M' : SheafOfModules.{w} (constantZModSheaf J N)}
    (φ : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj M') :
    (PresheafOfModules.restrictScalars (constantZModUnit J N)).obj M.val ⟶
      (PresheafOfModules.restrictScalars (constantZModUnit J N)).obj M'.val :=
  PresheafOfModules.homMk φ.hom fun U r m ↦ by
    obtain ⟨a⟩ := r
    have key : ∀ y : M.val.obj U, φ.hom.app U ((constantZModUnit J N).app U ⟨a⟩ • y) =
        (constantZModUnit J N).app U ⟨a⟩ • (show M'.val.obj U from φ.hom.app U y) := fun y ↦ by
      rw [constantZModUnit_smul, constantZModUnit_smul]
      exact map_nsmul (φ.hom.app U).hom _ _
    exact key m

/-- Every morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules is
`(ℤ/N)_C`-linear: the forgetful functor to abelian sheaves is full. -/
instance full_toSheaf_constantZMod [NeZero N] :
    (SheafOfModules.toSheaf.{w} (constantZModSheaf J N)).Full where
  map_surjective {M M'} φ := by
    obtain ⟨χ, hχ⟩ := (SheafOfModules.forget.{w} (constantZModSheaf J N) ⋙
      PresheafOfModules.restrictScalars (constantZModUnit J N)).map_surjective
        (restrictScalarsHomOfToSheaf φ)
    exact ⟨χ, ObjectProperty.hom_ext _ (congrArg (PresheafOfModules.toPresheaf _).map hχ)⟩

/-- The forgetful functor from sheaves of `(ℤ/N)_C`-modules to abelian sheaves is fully
faithful. -/
noncomputable def fullyFaithfulToSheafConstantZMod [NeZero N] :
    (SheafOfModules.toSheaf.{w} (constantZModSheaf J N)).FullyFaithful :=
  .ofFullyFaithful _

/-- The `ℤ/N`-module structures on the sections of an abelian presheaf killed by `N`. -/
abbrev moduleOfNsmul (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj U), N • x = 0)
    (U : Cᵒᵖ) : Module ((constantZModPresheaf.{w} (C := C) N).obj U) (F.obj U) :=
  letI : Module (ZMod N) (F.obj U) := AddCommGroup.zmodModule (hF U)
  inferInstanceAs (Module (ULift.{w} (ZMod N)) (F.obj U))

/-- An abelian presheaf killed by `N`, as a presheaf of modules over the constant presheaf of
rings `ℤ/N`. -/
noncomputable def presheafOfModulesOfNsmul (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj U), N • x = 0) :
    PresheafOfModules.{w} (constantZModPresheaf.{w} (C := C) N) :=
  letI := moduleOfNsmul F hF
  PresheafOfModules.ofPresheaf F fun U V f r m ↦ by
    let : Module (ZMod N) (F.obj U) := AddCommGroup.zmodModule (hF U)
    let : Module (ZMod N) (F.obj V) := AddCommGroup.zmodModule (hF V)
    exact (AddMonoidHom.toZModLinearMap N (F.map f).hom).map_smul r.down m

/-- The sheaf of `(ℤ/N)_C`-modules on an abelian sheaf `F` killed by `N`: the sheafification
of the presheaf of `ℤ/N`-modules `F`. -/
noncomputable def constantZModModuleOfNsmul (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    SheafOfModules.{w} (constantZModSheaf J N) :=
  (PresheafOfModules.sheafification.{w} (constantZModUnit J N)).obj
    (presheafOfModulesOfNsmul F.obj hF)

/-- The underlying abelian sheaf of `CategoryTheory.Sheaf.constantZModModuleOfNsmul F hF` is
`F`: the sheafification of the sheaf `F` is `F`. -/
noncomputable def toSheafConstantZModModuleOfNsmulIso (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    (SheafOfModules.toSheaf _).obj (constantZModModuleOfNsmul F hF) ≅ F :=
  (PresheafOfModules.sheafificationCompToSheaf (constantZModUnit J N)).app
    (presheafOfModulesOfNsmul F.obj hF) ≪≫ (sheafificationIso F).symm

/-- The essential image of the forgetful functor from sheaves of `(ℤ/N)_C`-modules to abelian
sheaves consists of the sheaves killed by `N`. -/
theorem exists_constantZModModule_iff (F : Sheaf J AddCommGrpCat.{w}) :
    (∃ M : SheafOfModules.{w} (constantZModSheaf J N),
      Nonempty ((SheafOfModules.toSheaf _).obj M ≅ F)) ↔
      ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0 := by
  refine ⟨fun ⟨M, ⟨e⟩⟩ U x ↦ ?_, fun hF ↦ ⟨_, ⟨toSheafConstantZModModuleOfNsmulIso F hF⟩⟩⟩
  obtain ⟨y, rfl⟩ : ∃ y, e.hom.hom.app U y = x :=
    ⟨e.inv.hom.app U x, by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
      rfl⟩
  rw [← map_nsmul]
  exact (congrArg (e.hom.hom.app U)
    (nsmul_eq_zero_of_constantZMod M (show M.val.obj U from y))).trans (map_zero _)

/-- Blueprint `definition-tate-twists`: An abelian sheaf killed by N is a module
over the constant sheaf Z/N.

Let `J` be a site, `N ≥ 1` and `F` an abelian sheaf killed by `N`. Then:

1. `F` carries a structure of sheaf of `(ℤ/N)_C`-modules with underlying abelian sheaf `F`
   (an isomorphism `e : M ≅ F` of abelian sheaves), on which the image `η(a)` of a class
   `a ∈ ℤ/N` acts as multiplication by the representative `a.val` of `a`; it is unique: two such
   structures `(M, e)`, `(M', e')` are isomorphic by an isomorphism of sheaves of
   `(ℤ/N)_C`-modules whose underlying morphism is `e ≫ e'⁻¹`;
2. every morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules is
   `(ℤ/N)_C`-linear.

The action `η(a) • x = a.val • x` holds in every sheaf of `(ℤ/N)_C`-modules
(`CategoryTheory.Sheaf.constantZModUnit_smul`), so the uniqueness of (1) is uniqueness of the
module structure. Together with `CategoryTheory.Sheaf.exists_constantZModModule_iff`, (2) says
that the sheaves of `(ℤ/N)_C`-modules are exactly the abelian sheaves killed by `N`, with the
same morphisms. -/
theorem torsionSheaf_constantModule [NeZero N] (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    (∃ (M : SheafOfModules.{w} (constantZModSheaf J N))
        (_ : (SheafOfModules.toSheaf _).obj M ≅ F),
        ∀ (U : Cᵒᵖ) (a : ZMod N) (x : M.val.obj U),
          (constantZModUnit J N).app U ⟨a⟩ • x = a.val • x) ∧
    (∀ (M M' : SheafOfModules.{w} (constantZModSheaf J N))
        (e : (SheafOfModules.toSheaf _).obj M ≅ F) (e' : (SheafOfModules.toSheaf _).obj M' ≅ F),
        ∃ E : M ≅ M', (SheafOfModules.toSheaf _).map E.hom = e.hom ≫ e'.inv) ∧
    (∀ (M M' : SheafOfModules.{w} (constantZModSheaf J N))
        (φ : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj M'),
        ∃ ψ : M ⟶ M', (SheafOfModules.toSheaf _).map ψ = φ) :=
  ⟨⟨_, toSheafConstantZModModuleOfNsmulIso F hF, fun _ a x ↦ constantZModUnit_smul _ a x⟩,
    fun _ _ e e' ↦ ⟨fullyFaithfulToSheafConstantZMod.preimageIso (e ≪≫ e'.symm),
      fullyFaithfulToSheafConstantZMod.map_preimage _⟩,
    fun _ _ φ ↦ (SheafOfModules.toSheaf _).map_surjective φ⟩

end CategoryTheory.Sheaf
