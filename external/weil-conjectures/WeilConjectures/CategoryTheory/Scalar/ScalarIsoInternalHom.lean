/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Internal Hom under an isomorphism of coefficient rings

Source: Stacks Project, Tags 03D7 and 08J7
(blueprint: lem-weil-pbc-scalar-iso-internal-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

private theorem scalarFull {C : Type c} [Category.{v} C]
    {R S : Cᵒᵖ ⥤ RingCat.{r}} (c : R ≅ S) :
    (PresheafOfModules.restrictScalars.{r} c.hom).Full := by
  constructor
  intro M N α
  let β : M ⟶ N := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf R).map α) (by
      intro X s x
      obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (c.hom.app X)).2 s
      exact (α.app X).hom.map_smul a x)
  exact ⟨β, by ext X x; rfl⟩

private def scalarHomMap {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R S : Sheaf J CommRingCat.{max c v r}) (c : S ≅ R)
    (M N : NativeModules.{max c v r, c, v} R) :
    let a := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).mapIso c
    let F := SheafOfModules.restrictScalars.{max c v r} a.hom
    F.obj (SheafOfModules.homObj (R := R) M N) ⟶
      SheafOfModules.homObj (R := S) (F.obj M) (F.obj N) := by
  let a := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).mapIso c
  let F := SheafOfModules.restrictScalars.{max c v r} a.hom
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro X
    exact ModuleCat.ofHom
      (X := (F.obj (SheafOfModules.homObj (R := R) M N)).val.obj X)
      (Y := (SheafOfModules.homObj (R := S) (F.obj M) (F.obj N)).val.obj X)
      { toFun := fun φ ↦ (PresheafOfModules.restrictScalars
          (((J.overPullback RingCat.{max c v r} X.unop).mapIso a).hom.hom)).map φ
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro s φ
          apply PresheafOfModules.hom_ext
          intro V
          ext x
          change R.obj.map V.unop.hom.op (c.hom.hom.app X s) • (φ.app V x) =
            c.hom.hom.app (op V.unop.left) (S.obj.map V.unop.hom.op s) • (φ.app V x)
          exact congrArg (fun t ↦ t • (φ.app V x))
            (ConcreteCategory.congr_hom (c.hom.hom.naturality V.unop.hom.op) s).symm }
  · intro X Y f
    ext φ : 2
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl

-- The scalar comparison checks linearity and two-variable naturality on every slice.
/-- Scalar restriction along a coefficient isomorphism preserves ordinary internal
Hom, naturally in both module arguments.
Source: Stacks Project, Tags 03D7 and 08J7
(blueprint: lem-weil-pbc-scalar-iso-internal-hom).

Proof: on a slice, restrict the scalars of a local module homomorphism. Since the
coefficient map is invertible this operation is bijective: a homomorphism linear
for the restricted action is linear for every scalar, by surjectivity of the
coefficient isomorphism. The map is linear for the scalar action on Hom and
commutes with restriction to smaller slices. It is therefore an isomorphism of
module sheaves. Both precomposition and postcomposition retain the same local
maps under scalar restriction, proving two-variable naturality. -/
theorem scalarIso_internalHom {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} (R S : Sheaf J CommRingCat.{max c v r}) (c : S ≅ R) :
    let a := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).mapIso c
    let F := SheafOfModules.restrictScalars.{max c v r} a.hom
    ∃ γ : ∀ M N : NativeModules.{max c v r, c, v} R,
      F.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (F.obj M) (F.obj N),
      ∀ {M M' N N' : NativeModules.{max c v r, c, v} R} (f : M' ⟶ M) (g : N ⟶ N'),
        F.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
          (γ M N).hom ≫ SheafOfModules.homObjMap (R := S) (F.map f) (F.map g) := by
  let a := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).mapIso c
  let F := SheafOfModules.restrictScalars.{max c v r} a.hom
  have hi (M N : NativeModules.{max c v r, c, v} R) :
      IsIso (scalarHomMap.{c, v, r} R S c M N) := by
    let ψ := scalarHomMap.{c, v, r} R S c M N
    have hX (X : Cᵒᵖ) : IsIso (ψ.val.app X) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      let b := ((J.overPullback RingCat.{max c v r} X.unop).mapIso a)
      let e := (sheafToPresheaf (J.over X.unop) RingCat.{max c v r}).mapIso b
      let H := PresheafOfModules.restrictScalars.{max c v r} e.hom
      have : H.Full := scalarFull e
      let M₀ := (PresheafOfModules.restrictOver R.obj X.unop).obj M.val
      let N₀ := (PresheafOfModules.restrictOver R.obj X.unop).obj N.val
      change Function.Bijective (fun f : M₀ ⟶ N₀ ↦ H.map f)
      exact ⟨H.map_injective, fun f ↦ H.map_surjective f⟩
    let e : (F.obj (SheafOfModules.homObj (R := R) M N)).val ≅
        (SheafOfModules.homObj (R := S) (F.obj M) (F.obj N)).val :=
      PresheafOfModules.isoMk (fun X ↦ @asIso _ _ _ _ (ψ.val.app X) (hX X))
        (by intro X Y f; exact ψ.val.naturality f)
    have : IsIso ((SheafOfModules.forget.{max c v r}
        (NativeRings.{max c v r, c, v} S)).map ψ) := by
      change IsIso e.hom
      infer_instance
    exact isIso_of_reflects_iso ψ
      (SheafOfModules.forget.{max c v r} (NativeRings.{max c v r, c, v} S))
  refine ⟨fun M N ↦ @asIso _ _ _ _ (scalarHomMap.{c, v, r} R S c M N) (hi M N), ?_⟩
  intro M M' N N' f g
  apply SheafOfModules.hom_ext
  ext X φ : 3
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  rfl

end CategoryTheory.NativeRestriction
