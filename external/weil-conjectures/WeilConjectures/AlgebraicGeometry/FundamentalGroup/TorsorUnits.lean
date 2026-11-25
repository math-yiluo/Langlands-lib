/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Units on the total space of a torsor

Let `t` be an `M`-torsor over a scheme `Y`, with total space `π : P ⟶ Y`. The pushforward
`π_* 𝔾ₘ` of the units of `P` (`AlgebraicGeometry.Scheme.EtaleTorsor.pushforwardGm`) is an étale
sheaf on `Y` with an action of `M` by translation (`pushforwardGmTranslate`), and the units of `Y`
map into it by pullback of functions (`pushforwardGmUnit`), landing in the invariants.

Over an étale `Y`-scheme `U` with a section `σ : U ⟶ P` of the torsor, the torsor is trivial:
the sections `sₐ = (𝟙, σ ≫ (-a) +ᵥ -) : U ⟶ U ×_Y P` exhibit `U ×_Y P` as `∐_{a ∈ M} U`
(`AlgebraicGeometry.Scheme.EtaleTorsor.isIso_sigmaDesc_localSection`). Consequently the
functions on `U ×_Y P` are the families `M → Γ(U, 𝒪_U)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.bijective_localSection_appTop`), translation by `b`
corresponds to the shift of families, and functions pulled back from `U` to constant families.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.pushforwardGm`: the sheaf `π_* 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.pushforwardGmTranslate`: translation by `a ∈ M`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.pushforwardGmUnit`: the map `𝔾ₘ ⟶ π_* 𝔾ₘ`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.isIso_sigmaDesc_localSection`: a torsor with a section
  is trivial.
- `AlgebraicGeometry.Scheme.EtaleTorsor.bijective_localSection_appTop`: functions on a trivial
  torsor are families of functions on the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-! ### Global sections of a finite coproduct -/

/-- The global sections of a finite coproduct of schemes are the families of global sections of
the summands: `x ↦ (ιᵢ^* x)ᵢ` is bijective. A global section of `X` is a morphism
`X ⟶ Spec ℤ[T]`, and morphisms out of a coproduct are families of morphisms. -/
lemma Scheme.bijective_appTop_sigmaι {ι : Type*} [Finite ι] (X : ι → Scheme.{u}) :
    Function.Bijective (fun x : Γ(∐ X, ⊤) ↦ fun i ↦ (Sigma.ι X i).appTop x) := by
  let B : CommRingCat.{u} := CommRingCat.of (Polynomial (ULift.{u} ℤ))
  have ev_ext {R : CommRingCat.{u}} (φ ψ : B ⟶ R) (h : φ Polynomial.X = ψ Polynomial.X) :
      φ = ψ := by
    apply CommRingCat.hom_ext
    refine Polynomial.ringHom_ext (fun a ↦ ?_) h
    exact RingHom.congr_fun (RingHom.ext_int
      (φ.hom.comp (Polynomial.C.comp ULift.ringEquiv.symm.toRingHom))
      (ψ.hom.comp (Polynomial.C.comp ULift.ringEquiv.symm.toRingHom))) a.down
  let ev {R : CommRingCat.{u}} (r : R) : B ⟶ R :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom ((Int.castRingHom R).comp
      ULift.ringEquiv.toRingHom) r)
  have ev_X {R : CommRingCat.{u}} (r : R) : ev r Polynomial.X = r := Polynomial.eval₂_X _ _
  have ev_comp {R S : CommRingCat.{u}} (r : R) (φ : R ⟶ S) : ev r ≫ φ = ev (φ r) :=
    ev_ext _ _ (by rw [CommRingCat.comp_apply, ev_X, ev_X])
  let adj := ΓSpec.adjunction.{u}
  let mor {Z : Scheme.{u}} (z : Γ(Z, ⊤)) : Z ⟶ Scheme.Spec.obj (op B) :=
    adj.homEquiv Z (op B) (ev z).op
  have mor_comp {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (z : Γ(Z, ⊤)) :
      g ≫ mor z = mor (g.appTop z) := by
    simp only [mor, ← Adjunction.homEquiv_naturality_left]
    congr 1
    change (g.appTop).op ≫ (ev z).op = (ev (g.appTop z)).op
    rw [← op_comp, ev_comp]
  have mor_inj {Z : Scheme.{u}} (z z' : Γ(Z, ⊤)) (h : mor z = mor z') : z = z' := by
    have h' : ev z = ev z' := Quiver.Hom.op_inj ((adj.homEquiv Z (op B)).injective h)
    rw [← ev_X z, ← ev_X z', h']
  refine ⟨fun x y hxy ↦ mor_inj x y (Sigma.hom_ext _ _ fun i ↦ ?_), fun c ↦ ?_⟩
  · rw [mor_comp, mor_comp]
    exact congrArg mor (congrFun hxy i)
  · let ψ : B ⟶ Γ(∐ X, ⊤) :=
      ((adj.homEquiv _ (op B)).symm (Sigma.desc fun i ↦ mor (c i))).unop
    have h1 : mor (ψ Polynomial.X) = Sigma.desc fun i ↦ mor (c i) := by
      have hψ : ψ = ev (ψ Polynomial.X) := ev_ext _ _ (by rw [ev_X])
      change adj.homEquiv _ (op B) (ev (ψ Polynomial.X)).op = _
      rw [← hψ]
      exact (adj.homEquiv _ (op B)).apply_symm_apply _
    refine ⟨ψ Polynomial.X, funext fun i ↦ mor_inj _ _ ?_⟩
    dsimp only
    rw [← mor_comp, h1, Sigma.ι_comp_desc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullbacks of a finite coproduct decomposition form a coproduct decomposition: if
`∐ₐ Zₐ ⟶ X` is an isomorphism then so is `∐ₐ (Y ×_X Zₐ) ⟶ Y`. This is
`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst` for schemes, with an index type in an
arbitrary universe. -/
lemma Scheme.isIso_sigmaDesc_pullbackFst {α : Type*} [Finite α] {X : Scheme.{u}}
    {Z : α → Scheme.{u}} (π : (a : α) → Z a ⟶ X) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc fun a ↦ pullback.fst f (π a)) := by
  let c := Cofan.mk _ (fun a ↦ pullback.fst f (π a))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

/-! ### Restriction of units along morphisms -/

namespace Scheme

variable {X Z Z' Z'' : Scheme.{u}} (g : Z ⟶ X) (h : Z' ⟶ Z) (g' : Z' ⟶ X) (hh : h ≫ g = g')

lemma lowerStarGmSheafMap_comp (h' : Z'' ⟶ Z') (g'' : Z'' ⟶ X) (hh' : h' ≫ g' = g'') :
    lowerStarGmSheafMap g h g' hh ≫ lowerStarGmSheafMap g' h' g'' hh' =
      lowerStarGmSheafMap g (h' ≫ h) g'' (by rw [Category.assoc, hh, hh']) := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp]
  congr 1
  rw [← Scheme.Hom.comp_appTop]
  congr 1
  apply pullback.hom_ext <;> simp

lemma lowerStarGmSheafMap_id : lowerStarGmSheafMap g (𝟙 Z) g (Category.id_comp g) = 𝟙 _ := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ = 𝟙 _
  rw [← CommRingCat.unitsAddCommGrpULift.map_id]
  congr 1
  refine (congrArg Scheme.Hom.appTop ?_).trans Scheme.Hom.id_appTop
  apply pullback.hom_ext <;> simp

/-- The value of `lowerStarGmSheafMap` on a section, as a function. -/
lemma lowerStarGmSheafMap_app_val {V : X.Etale}
    (x : ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj Z.gmSheaf).obj.obj (op V)) :
    ((Additive.toMul ((lowerStarGmSheafMap g h g' hh).hom.app (op V) x).down :
        Γ(pullback V.hom g', ⊤)ˣ) : Γ(pullback V.hom g', ⊤)) =
      (pullback.map V.hom g' V.hom g (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).appTop
        ((Additive.toMul x.down : Γ(pullback V.hom g, ⊤)ˣ) : Γ(pullback V.hom g, ⊤)) :=
  rfl

/-- The value of `gmSheafToLowerStarGmSheaf` on a section, as a function. -/
lemma gmSheafToLowerStarGmSheaf_app_val {V : X.Etale} (x : X.gmSheaf.obj.obj (op V)) :
    ((Additive.toMul ((gmSheafToLowerStarGmSheaf g).hom.app (op V) x).down :
        Γ(pullback V.hom g, ⊤)ˣ) : Γ(pullback V.hom g, ⊤)) =
      (pullback.fst V.hom g).appTop
        ((Additive.toMul x.down : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) :=
  rfl


end Scheme

namespace Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}} (t : EtaleTorsor M Y)

/-! ### The sheaf `π_* 𝔾ₘ` and its translations -/

/-- The étale sheaf `π_* 𝔾ₘ` on `Y` of units on the total space of the torsor: its sections over
an étale `U ⟶ Y` are the units of `Γ(U ×_Y P, 𝒪)`. -/
noncomputable abbrev pushforwardGm : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} t.π).obj t.P.gmSheaf

/-- Translation by `a ∈ M` on `π_* 𝔾ₘ`: pullback of units along `𝟙 × (a +ᵥ -)`. -/
noncomputable def pushforwardGmTranslate (a : M) : t.pushforwardGm ⟶ t.pushforwardGm :=
  lowerStarGmSheafMap t.π (t.vadd a) t.π (t.vadd_π a)

/-- The map `𝔾ₘ ⟶ π_* 𝔾ₘ` pulling back units from the base. -/
noncomputable def pushforwardGmUnit : Y.gmSheaf ⟶ t.pushforwardGm :=
  gmSheafToLowerStarGmSheaf t.π

@[simp]
lemma pushforwardGmTranslate_zero : t.pushforwardGmTranslate 0 = 𝟙 _ := by
  rw [pushforwardGmTranslate]
  convert lowerStarGmSheafMap_id t.π using 2
  exact t.zero_vadd

lemma pushforwardGmTranslate_add (a b : M) :
    t.pushforwardGmTranslate (a + b) =
      t.pushforwardGmTranslate b ≫ t.pushforwardGmTranslate a := by
  rw [pushforwardGmTranslate, pushforwardGmTranslate, pushforwardGmTranslate,
    lowerStarGmSheafMap_comp]
  congr 1
  exact t.add_vadd a b

lemma pushforwardGmTranslate_comm (a b : M) :
    t.pushforwardGmTranslate a ≫ t.pushforwardGmTranslate b =
      t.pushforwardGmTranslate b ≫ t.pushforwardGmTranslate a := by
  rw [← pushforwardGmTranslate_add, ← pushforwardGmTranslate_add, add_comm]

@[reassoc (attr := simp)]
lemma pushforwardGmUnit_comp_translate (a : M) :
    t.pushforwardGmUnit ≫ t.pushforwardGmTranslate a = t.pushforwardGmUnit :=
  gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap _ _ _ _

/-! ### A torsor with a section is trivial -/

section Local

variable {U : Scheme.{u}} (f : U ⟶ Y) (σ : U ⟶ t.P) (hσ : σ ≫ t.π = f)

/-- For a section `σ : U ⟶ P` of the torsor over `f : U ⟶ Y`, the section
`sₐ = (𝟙, σ ≫ (-a) +ᵥ -) : U ⟶ U ×_Y P` of the base change of the torsor. -/
noncomputable def localSection (a : M) : U ⟶ pullback f t.π :=
  pullback.lift (𝟙 U) (σ ≫ t.vadd (-a)) (by rw [Category.id_comp, Category.assoc, t.vadd_π, hσ])

@[reassoc (attr := simp)]
lemma localSection_fst (a : M) : t.localSection f σ hσ a ≫ pullback.fst f t.π = 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma localSection_snd (a : M) :
    t.localSection f σ hσ a ≫ pullback.snd f t.π = σ ≫ t.vadd (-a) :=
  pullback.lift_snd _ _ _

/-- Translating `sₐ` by `b` gives `s_{a - b}`. -/
@[reassoc]
lemma localSection_comp_map (a b : M) :
    t.localSection f σ hσ a ≫ pullback.map f t.π f t.π (𝟙 _) (t.vadd b) (𝟙 _)
      (by simp) (by simp [t.vadd_π]) = t.localSection f σ hσ (a - b) := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, pullback.lift_snd, localSection_snd_assoc, localSection_snd]
    rw [← t.add_vadd, neg_sub, sub_eq_neg_add]

/-- A torsor with a section `σ` is trivial: the sections `sₐ` exhibit `U ×_Y P` as the coproduct
`∐_{a ∈ M} U`. The square
```
  U ───sₐ───▶ U ×_Y P
  │              │ (σ ∘ pr₁, pr₂)
σ ≫ (-a)        ▼
  P ──(a, 𝟙)──▶ P ×_Y P
```
is cartesian, and the bottom maps form the coproduct decomposition of `P ×_Y P` defining the
torsor. -/
lemma isIso_sigmaDesc_localSection :
    IsIso (Sigma.desc fun a : M ↦ t.localSection f σ hσ a) := by
  have := t.isIso_sigmaDesc
  let j : pullback f t.π ⟶ pullback t.π t.π :=
    pullback.lift (pullback.fst f t.π ≫ σ) (pullback.snd f t.π)
      (by rw [Category.assoc, hσ, pullback.condition])
  let ρ (a : M) : t.P ⟶ pullback t.π t.π :=
    pullback.lift (f := t.π) (g := t.π) (t.vadd a) (𝟙 t.P) (by simp [t.vadd_π])
  have hv (a : M) : t.vadd a ≫ t.vadd (-a) = 𝟙 _ := by
    rw [← t.add_vadd, add_neg_cancel, t.zero_vadd]
  have hsq (a : M) : IsPullback (t.localSection f σ hσ a) (σ ≫ t.vadd (-a)) j (ρ a) := by
    -- for a cone `(w, y)`: `w ≫ pr₁ ≫ σ = y ≫ (a +ᵥ -)` and `w ≫ pr₂ = y`
    have key (T : Scheme.{u}) (w : T ⟶ pullback f t.π) (y : T ⟶ t.P) (h : w ≫ j = y ≫ ρ a) :
        w ≫ pullback.fst f t.π ≫ σ ≫ t.vadd (-a) = y ∧
          w ≫ pullback.fst f t.π ≫ σ ≫ t.vadd (-a) = w ≫ pullback.snd f t.π := by
      have h₁ := congrArg (· ≫ pullback.fst t.π t.π) h
      have h₂ := congrArg (· ≫ pullback.snd t.π t.π) h
      simp only [Category.assoc, j, ρ, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id] at h₁ h₂
      have h₃ : w ≫ pullback.fst f t.π ≫ σ ≫ t.vadd (-a) = y := by
        calc _ = (w ≫ pullback.fst f t.π ≫ σ) ≫ t.vadd (-a) := by simp only [Category.assoc]
          _ = y := by rw [h₁, Category.assoc, hv, Category.comp_id]
      exact ⟨h₃, h₃.trans h₂.symm⟩
    refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst ≫ pullback.fst f t.π) ?_ ?_ ?_⟩⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, j, ρ, pullback.lift_fst, localSection_fst_assoc]
        rw [← t.add_vadd, neg_add_cancel, t.zero_vadd, Category.comp_id]
      · simp [j, ρ]
    · intro s
      refine pullback.hom_ext (by simp) ?_
      simp only [Category.assoc, localSection_snd]
      exact (key _ _ _ s.condition).2
    · intro s
      simpa only [Category.assoc] using (key _ _ _ s.condition).1
    · intro s m hm _
      rw [← hm, Category.assoc, localSection_fst, Category.comp_id]
  have h1 := Scheme.isIso_sigmaDesc_pullbackFst ρ j this
  have e : (Sigma.desc fun a : M ↦ t.localSection f σ hσ a) =
      Limits.Sigma.map (fun a ↦ (hsq a).isoPullback.hom) ≫
        Sigma.desc fun a ↦ pullback.fst j (ρ a) := by
    refine Sigma.hom_ext _ _ fun a ↦ ?_
    simp
  rw [e]
  infer_instance

/-- The functions on `U ×_Y P` are the families of functions on `U`: `x ↦ (sₐ^* x)ₐ` is
bijective. -/
lemma bijective_localSection_appTop :
    Function.Bijective (fun x : Γ(pullback f t.π, ⊤) ↦
      fun a : M ↦ (t.localSection f σ hσ a).appTop x) := by
  have := t.isIso_sigmaDesc_localSection f σ hσ
  have h := (Scheme.bijective_appTop_sigmaι (fun _ : M ↦ U)).comp
    (ConcreteCategory.bijective_of_isIso
      (Sigma.desc fun a : M ↦ t.localSection f σ hσ a).appTop)
  convert h using 1
  funext x a
  simp only [Function.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Sigma.ι_comp_desc]

end Local

/-! ### The dictionary between sections of `π_* 𝔾ₘ` and families of units -/

section Dictionary

variable {U : Y.Etale} (σ : U.left ⟶ t.P) (hσ : σ ≫ t.π = U.hom)

/-- The unit on `U ×_Y P` underlying a section of `π_* 𝔾ₘ` over `U`. -/
noncomputable def pushforwardGmUnits (x : t.pushforwardGm.obj.obj (op U)) :
    Γ(pullback U.hom t.π, ⊤)ˣ :=
  Additive.toMul x.down

lemma pushforwardGmUnits_add (x y : t.pushforwardGm.obj.obj (op U)) :
    t.pushforwardGmUnits (x + y) = t.pushforwardGmUnits x * t.pushforwardGmUnits y :=
  rfl


lemma injective_pushforwardGmUnits :
    Function.Injective (t.pushforwardGmUnits (U := U)) :=
  fun _ _ h ↦ ULift.ext (Additive.toMul.injective h)

lemma pushforwardGmUnits_translate (b : M) (x : t.pushforwardGm.obj.obj (op U)) :
    (t.pushforwardGmUnits ((t.pushforwardGmTranslate b).hom.app (op U) x) :
        Γ(pullback U.hom t.π, ⊤)) =
      (pullback.map U.hom t.π U.hom t.π (𝟙 _) (t.vadd b) (𝟙 _) (by simp)
        (by simp [t.vadd_π])).appTop (t.pushforwardGmUnits x) :=
  rfl

lemma pushforwardGmUnits_unit (c : Y.gmSheaf.obj.obj (op U)) :
    (t.pushforwardGmUnits (t.pushforwardGmUnit.hom.app (op U) c) :
        Γ(pullback U.hom t.π, ⊤)) =
      (pullback.fst U.hom t.π).appTop ((Additive.toMul c.down : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)) :=
  rfl

/-- The component at `a ∈ M` of a section of `π_* 𝔾ₘ` over `U`, in the trivialisation given by a
section `σ` of the torsor: the pullback of the unit along `sₐ : U ⟶ U ×_Y P`. -/
noncomputable def localUnits (a : M) :
    t.pushforwardGm.obj.obj (op U) →+ Additive Γ(U.left, ⊤)ˣ where
  toFun x := Additive.ofMul
    (Units.map (t.localSection U.hom σ hσ a).appTop.hom.toMonoidHom (t.pushforwardGmUnits x))
  map_zero' := by
    change Additive.ofMul (Units.map _ 1) = 0
    rw [map_one]
    rfl
  map_add' x y := by
    change Additive.ofMul (Units.map _ (t.pushforwardGmUnits x * t.pushforwardGmUnits y)) = _
    rw [map_mul]
    rfl

lemma localUnits_val (a : M) (x : t.pushforwardGm.obj.obj (op U)) :
    ((Additive.toMul (t.localUnits σ hσ a x) : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)) =
      (t.localSection U.hom σ hσ a).appTop (t.pushforwardGmUnits x) :=
  rfl

/-- Translation by `b` shifts the components by `-b`. -/
lemma localUnits_translate (a b : M) (x : t.pushforwardGm.obj.obj (op U)) :
    t.localUnits σ hσ a ((t.pushforwardGmTranslate b).hom.app (op U) x) =
      t.localUnits σ hσ (a - b) x := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [localUnits_val, localUnits_val, pushforwardGmUnits_translate, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, localSection_comp_map]

/-- Units pulled back from the base have constant components. -/
lemma localUnits_unit (a : M) (c : Y.gmSheaf.obj.obj (op U)) :
    t.localUnits σ hσ a (t.pushforwardGmUnit.hom.app (op U) c) = c.down := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [localUnits_val, pushforwardGmUnits_unit, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, localSection_fst, Scheme.Hom.id_appTop]
  rfl

/-- In the trivialisation given by a section of the torsor, a section of `π_* 𝔾ₘ` is determined
by its components. -/
lemma localUnits_injective {x y : t.pushforwardGm.obj.obj (op U)}
    (h : ∀ a, t.localUnits σ hσ a x = t.localUnits σ hσ a y) : x = y := by
  apply t.injective_pushforwardGmUnits
  apply Units.ext
  refine (t.bijective_localSection_appTop U.hom σ hσ).1 (funext fun a ↦ ?_)
  have := congrArg (fun z ↦ ((Additive.toMul z : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))) (h a)
  exact this

/-- In the trivialisation given by a section of the torsor, every family of units is the family of
components of a section of `π_* 𝔾ₘ`. -/
lemma exists_localUnits (F : M → Additive Γ(U.left, ⊤)ˣ) :
    ∃ x : t.pushforwardGm.obj.obj (op U), ∀ a, t.localUnits σ hσ a x = F a := by
  obtain ⟨r, hr⟩ := (t.bijective_localSection_appTop U.hom σ hσ).2
    (fun a ↦ ((Additive.toMul (F a) : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)))
  obtain ⟨r', hr'⟩ := (t.bijective_localSection_appTop U.hom σ hσ).2
    (fun a ↦ (((Additive.toMul (F a))⁻¹ : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)))
  have hrr' : r * r' = 1 := (t.bijective_localSection_appTop U.hom σ hσ).1 (funext fun a ↦ by
    have h1 := congrFun hr a
    have h2 := congrFun hr' a
    simp only at h1 h2 ⊢
    rw [map_mul, h1, h2, Units.mul_inv, map_one])
  let u : Γ(pullback U.hom t.π, ⊤)ˣ := ⟨r, r', hrr', by rw [mul_comm, hrr']⟩
  refine ⟨ULift.up (Additive.ofMul u), fun a ↦ Additive.toMul.injective (Units.ext ?_)⟩
  exact congrFun hr a

end Dictionary

end Scheme.EtaleTorsor

end AlgebraicGeometry
