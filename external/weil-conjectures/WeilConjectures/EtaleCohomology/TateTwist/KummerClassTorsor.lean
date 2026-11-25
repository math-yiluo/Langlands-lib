/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerCoverPoints
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass

/-!
# The torsor form of the Kummer class

Let `u` be a unit on a scheme `X` and `n ≥ 1`. The Kummer class `κ(u)`
(`AlgebraicGeometry.Etale.kummerClassOf`) is the connecting morphism of the extension

`0 ⟶ μₙ ⟶ E_u ⟶ ℤ ⟶ 0`,  `E_u = 𝔾ₘ ×_{𝔾ₘ} ℤ`,

the pullback of the Kummer sequence along `u : ℤ ⟶ 𝔾ₘ`
(`AlgebraicGeometry.Scheme.kummerExtension`), with coefficients extended to `Λ`. Under the
standard identification of extensions of `ℤ` by `μₙ` with `μₙ`-torsors, an extension corresponds
to the torsor given by the preimage of the section `1` of `ℤ`. For `E_u` this preimage is the
sheaf of `n`-th roots of `u`, which is represented by the Kummer cover
`𝒯_u = Spec 𝒪_X[T₀]/(T₀ⁿ - u)` (`AlgebraicGeometry.Scheme.kummerCover`): over every étale
`U ⟶ X`, the sections of `E_u` lying over `1` are the `X`-morphisms `U ⟶ 𝒯_u`
(`AlgebraicGeometry.Scheme.kummerExtensionFiberEquiv`). This is the torsor form of the Kummer
class of blueprint `def-pur-affine-line-datum`: `κ(u)` is the class of the `μₙ`-torsor `𝒯_u`.

## Main definitions

- `AlgebraicGeometry.Scheme.kummerExtension`: the extension `E_u`.
- `AlgebraicGeometry.Scheme.constantSheafIntOne`: the section `1` of `ℤ` over `U`.
- `AlgebraicGeometry.Scheme.kummerExtensionFiberEquiv`: the sections of `E_u` over `1` are the
  points of `𝒯_u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (n : ℕ) (u : Γ(X, ⊤)ˣ)

/-- The extension `E_u = 𝔾ₘ ×_{𝔾ₘ} ℤ` of `ℤ` by `μₙ`: the pullback of the Kummer sequence along
`u : ℤ ⟶ 𝔾ₘ`, whose sections over `U` are the pairs `(x, k)` of a unit `x` on `U` and a locally
constant integer `k` with `xⁿ = uᵏ`. Its connecting morphism is the Kummer class of `u`. -/
noncomputable abbrev kummerExtension : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((X.kummerSequence n).pullback (unitToGmSheaf u)).X₂

/-- The projection `E_u ⟶ ℤ`. -/
noncomputable abbrev kummerExtensionToInt : kummerExtension n u ⟶ X.constantSheafInt :=
  ((X.kummerSequence n).pullback (unitToGmSheaf u)).g

variable (U : X.Etale)

/-- The constant section `1` of `ℤ` over an étale `U ⟶ X`: the restriction of the image of `1`
under the unit `ℤ ⟶ Γ(X, ℤ)` of the constant sheaf adjunction. -/
noncomputable def constantSheafIntOne : X.constantSheafInt.obj.obj (op U) :=
  X.constantSheafInt.obj.map (terminal.from U).op
    (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))).hom (ULift.up 1))

/-- The unit `u` sends the constant section `1` over `U` to the restriction `u|_U` of `u`. -/
lemma unitToGmSheaf_app_constantSheafIntOne :
    (unitToGmSheaf u).hom.app (op U) (constantSheafIntOne U) =
      ULift.up (Additive.ofMul (Units.map U.hom.appTop.hom.toMonoidHom u)) := by
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  have h₁ : (unitToGmSheaf u).hom.app (op (⊤_ X.Etale))
      ((adj.unit.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))).hom (ULift.up 1)) =
        gmSection u := by
    have h := ConcreteCategory.congr_hom (adj.homEquiv_unit _ _ (unitToGmSheaf u)).symm (ULift.up 1)
    rw [unitToGmSheaf, Equiv.apply_symm_apply] at h
    refine h.trans ?_
    have := zmodToGmSections_natCast 0 u (pow_zero u) 1
    simpa using this
  have h₂ := ConcreteCategory.congr_hom ((unitToGmSheaf u).hom.naturality (terminal.from U).op)
    ((adj.unit.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))).hom (ULift.up 1))
  simp only [ConcreteCategory.comp_apply] at h₂
  rw [constantSheafIntOne, h₂, h₁]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change (terminal.from U).left.appTop ((⊤_ X.Etale).hom.appTop (u : Γ(X, ⊤))) =
    U.hom.appTop (u : Γ(X, ⊤))
  have hw : (terminal.from U).left ≫ (⊤_ X.Etale).hom = U.hom :=
    MorphismProperty.Over.w (terminal.from U)
  rw [← hw, Scheme.Hom.comp_appTop]
  rfl

/-- The sections of `E_u` over `U` are the pairs `(x, k)` of sections of `𝔾ₘ` and `ℤ` with
`n • x = u(k)`. -/
noncomputable def kummerExtensionSectionsEquiv :
    (kummerExtension n u).obj.obj (op U) ≃
      {p : X.gmSheaf.obj.obj (op U) × X.constantSheafInt.obj.obj (op U) //
        n • p.1 = (unitToGmSheaf u).hom.app (op U) p.2} :=
  let ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)
  ((CategoryTheory.forget AddCommGrpCat).mapIso (PreservesPullback.iso ev (n • 𝟙 X.gmSheaf)
    (unitToGmSheaf u))).toEquiv.trans
    ((Concrete.pullbackEquiv (ev.map (n • 𝟙 X.gmSheaf)) (ev.map (unitToGmSheaf u))).trans
      (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl))

lemma kummerExtensionSectionsEquiv_snd (e : (kummerExtension n u).obj.obj (op U)) :
    (kummerExtensionSectionsEquiv n u U e).1.2 = (kummerExtensionToInt n u).hom.app (op U) e := by
  let ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)
  have key (x : ToType (pullback (ev.map (n • 𝟙 X.gmSheaf)) (ev.map (unitToGmSheaf u)))) :
      (Concrete.pullbackEquiv (ev.map (n • 𝟙 X.gmSheaf)) (ev.map (unitToGmSheaf u)) x).1.2 =
        pullback.snd (ev.map (n • 𝟙 X.gmSheaf)) (ev.map (unitToGmSheaf u)) x := by
    obtain ⟨x₁, x₂, h, rfl⟩ := Concrete.pullbackMk_surjective _ _ x
    rw [Concrete.pullbackMk_snd]
    simp [Concrete.pullbackMk]
  refine (key _).trans ?_
  exact ConcreteCategory.congr_hom
    (PreservesPullback.iso_hom_snd ev (n • 𝟙 X.gmSheaf) (unitToGmSheaf u)) e

/-- The sections of `𝔾ₘ` over `U` are the units of `Γ(U, 𝒪_U)`. -/
def gmSheafSectionsEquiv : X.gmSheaf.obj.obj (op U) ≃ Γ(U.left, ⊤)ˣ where
  toFun x := Additive.toMul x.down
  invFun v := ULift.up (Additive.ofMul v)
  left_inv _ := rfl
  right_inv _ := rfl

lemma gmSheafSectionsEquiv_nsmul (x : X.gmSheaf.obj.obj (op U)) :
    gmSheafSectionsEquiv U (n • x) = gmSheafSectionsEquiv U x ^ n :=
  rfl

variable [NeZero n]

/-- The units `v` of a ring with `vⁿ = a` for a unit `a` are the elements `w` with `wⁿ = a`. -/
noncomputable def unitsPowEqEquiv {R : Type*} [CommRing R] (a : Rˣ) :
    {v : Rˣ // v ^ n = a} ≃ {w : R // w ^ n = a} where
  toFun v := ⟨v.1, by rw [← Units.val_pow_eq_pow_val, v.2]⟩
  invFun w := ⟨((isUnit_pow_iff (NeZero.ne n)).1 (w.2 ▸ a.isUnit)).unit,
    Units.ext (by simpa using w.2)⟩
  left_inv v := Subtype.ext (Units.ext rfl)
  right_inv w := rfl

/-- Blueprint `def-pur-affine-line-datum` (torsor form): the Kummer class `κ(u)` is the class of
the `μₙ`-torsor `𝒯_u = Spec 𝒪_X[T₀]/(T₀ⁿ - u)`.

The Kummer class of `u` is the connecting morphism of the extension
`0 ⟶ μₙ ⟶ E_u ⟶ ℤ ⟶ 0` (`AlgebraicGeometry.Scheme.kummerExtension`, the pullback of the Kummer
sequence along `u : ℤ ⟶ 𝔾ₘ`, see `AlgebraicGeometry.Etale.kummerClassOf`), and the `μₙ`-torsor
attached to an extension of `ℤ` by `μₙ` is the preimage of the section `1` of `ℤ`. Over every
étale `U ⟶ X`, the sections of `E_u` lying over `1` are the pairs `(x, 1)` with `xⁿ = u|_U`,
that is, the `X`-morphisms `U ⟶ 𝒯_u`
(`AlgebraicGeometry.Scheme.kummerCoverHomEquiv`): the preimage of `1` in `E_u` is the sheaf
represented by `𝒯_u`. -/
noncomputable def kummerExtensionFiberEquiv :
    {e : (kummerExtension n u).obj.obj (op U) //
        (kummerExtensionToInt n u).hom.app (op U) e = constantSheafIntOne U} ≃
      {g : U.left ⟶ X.kummerCover n (u : Γ(X, ⊤)) // g ≫ X.kummerCoverπ n u = U.hom} :=
  (Equiv.subtypeEquiv (kummerExtensionSectionsEquiv n u U)
      fun e ↦ by rw [kummerExtensionSectionsEquiv_snd]).trans <|
  ({ toFun p := ⟨p.1.1.1, by rw [p.1.2, p.2, unitToGmSheaf_app_constantSheafIntOne]⟩
     invFun x := ⟨⟨(x.1, constantSheafIntOne U), by
        rw [x.2, unitToGmSheaf_app_constantSheafIntOne]⟩, rfl⟩
     left_inv p := by
       obtain ⟨⟨⟨x, k⟩, hxk⟩, hk⟩ := p
       dsimp only at hk
       subst hk
       rfl
     right_inv x := rfl } :
    {p : {p : X.gmSheaf.obj.obj (op U) × X.constantSheafInt.obj.obj (op U) //
        n • p.1 = (unitToGmSheaf u).hom.app (op U) p.2} // p.1.2 = constantSheafIntOne U} ≃
      {x : X.gmSheaf.obj.obj (op U) //
        n • x = ULift.up (Additive.ofMul (Units.map U.hom.appTop.hom.toMonoidHom u))}).trans <|
  (Equiv.subtypeEquiv (gmSheafSectionsEquiv U) fun x ↦ by
    rw [← gmSheafSectionsEquiv_nsmul, ← (gmSheafSectionsEquiv U).eq_symm_apply]
    rfl).trans <|
  (unitsPowEqEquiv n (Units.map U.hom.appTop.hom.toMonoidHom u)).trans <|
  (kummerCoverHomEquiv n (u : Γ(X, ⊤)) U.hom).symm

end AlgebraicGeometry.Scheme
