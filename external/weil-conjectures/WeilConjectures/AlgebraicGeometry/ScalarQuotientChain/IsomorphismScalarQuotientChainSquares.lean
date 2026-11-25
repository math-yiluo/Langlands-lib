/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Balanced scalar comparisons and coefficient tower squares

The positive level m is indexed by n = m - 1. All tensors are the existing
sheafified balanced scalar extension, with the scalar first. Termwise extension
is the degreewise model of the direct-sum total tensor with coefficients in degree zero.
Inverse image uses its canonical corresponding-object model. The auxiliary structures
only collect the coefficient data and equations appearing in the hypotheses.

## References

* Stacks Project, Tag 03EK, section-tensor-product
* Stacks 03EK and 03EL
* Stacks 03D2, 09A5 and 00WX
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe t r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme CategoryTheory.CochainPullback

namespace AlgebraicGeometry.ProEtale.ScalarQuotientChain

/-- Coefficients in any universe containing the small site's objects. -/
abbrev Coeff (W : Scheme.{t}) :=
  Sheaf (ProEt.topology W) CommRingCat.{max r (t + 1)}

/-- Forget only commutativity, retaining the given ring sheaf. -/
abbrev forgetRing (W : Scheme.{t}) :=
  sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})

/-- The existing complex category, with all site and coefficient sizes explicit. -/
abbrev moduleComplex (W : Scheme.{t}) (R : Coeff.{t, r} W) :=
  CochainComplex (ringedSiteModules.{max r (t + 1)} ((forgetRing W).obj R)) ℤ

/-- Specialization of the existing scalar-extension functor to the given pro-etale site. -/
abbrev scalarExtend (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :
    moduleComplex W A ⥤ moduleComplex W B :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a).mapHomologicalComplex (.up ℤ)

/-- Specialization of existing scalar restriction on complexes. -/
abbrev scalarRestrict (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :=
  CochainPullback.restrictComplex.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a

/-- The existing scalar-extension pure tensor with its site explicitly supplied. -/
abbrev pure (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B)
    (M : ringedSiteModules.{max r (t + 1)} ((forgetRing W).obj A))
    (U : W.ProEtᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :=
  extensionTmul.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a M U s x

/-- The two towers, coefficient projections and commuting squares of the hypotheses.
Level n denotes the positive level n+1; no map is required to be surjective or flat. -/
structure Tower (W : Scheme.{t}) where
  R : Coeff.{t, r} W
  S : Coeff.{t, r} W
  A : ℕ → Coeff.{t, r} W
  B : ℕ → Coeff.{t, r} W
  j : R ⟶ S
  i : ∀ n : ℕ, A n ⟶ B n
  piA : ∀ n : ℕ, R ⟶ A n
  piB : ∀ n : ℕ, S ⟶ B n
  qA : ∀ n : ℕ, A (Nat.succ n) ⟶ A n
  qB : ∀ n : ℕ, B (Nat.succ n) ⟶ B n
  transition_i : ∀ n : ℕ, i (Nat.succ n) ≫ qB n = qA n ≫ i n
  projection_A : ∀ n : ℕ, piA (Nat.succ n) ≫ qA n = piA n
  projection_B : ∀ n : ℕ, piB (Nat.succ n) ≫ qB n = piB n
  projection_i : ∀ n : ℕ, j ≫ piB n = piA n ≫ i n

/-- The recorded corresponding-object inverse image on commutative ring sheaves. -/
abbrev inverseRing {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}

/-- The four specified coefficient isomorphisms and all their compatibilities. -/
structure Transport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (DX : Tower.{t, r} X) (DY : Tower.{t, r} Y) where
  cR : (inverseRing g).obj DY.R ≅ DX.R
  cS : (inverseRing g).obj DY.S ≅ DX.S
  cA : ∀ n : ℕ, (inverseRing g).obj (DY.A n) ≅ DX.A n
  cB : ∀ n : ℕ, (inverseRing g).obj (DY.B n) ≅ DX.B n
  j_comm : (inverseRing g).map DY.j ≫ cS.hom = cR.hom ≫ DX.j
  i_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.i n) ≫ (cB n).hom = (cA n).hom ≫ DX.i n
  piA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piA n) ≫ (cA n).hom = cR.hom ≫ DX.piA n
  piB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piB n) ≫ (cB n).hom = cS.hom ≫ DX.piB n
  qA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qA n) ≫ (cA n).hom = (cA (Nat.succ n)).hom ≫ DX.qA n
  qB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qB n) ≫ (cB n).hom = (cB (Nat.succ n)).hom ≫ DX.qB n

/-- The existing inverse image with its action transported through c inverse. -/
abbrev inverseModules {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) :
    ringedSiteModules.{max r (t + 1)} ((forgetRing Y).obj RY) ⥤
      ringedSiteModules.{max r (t + 1)} ((forgetRing X).obj RX) :=
  isoSectionwiseModuleInverseImage.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

variable {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  {DX : Tower.{t, r} X} {DY : Tower.{t, r} Y} (d : Transport g DX DY)

/-- The upper left functor P ↦ G_R(P) tensor S_X. -/
abbrev left : moduleComplex Y DY.R ⥤ moduleComplex X DX.S := (inverseModules g d.cR ⋙
  extensionFunctor.{max r (t + 1), t + 1, t} DX.j).mapHomologicalComplex (.up ℤ)

/-- The upper right functor P ↦ G_S(P tensor S_Y). -/
abbrev right : moduleComplex Y DY.R ⥤ moduleComplex X DX.S :=
  (extensionFunctor.{max r (t + 1), t + 1, t} DY.j ⋙
  inverseModules g d.cS).mapHomologicalComplex (.up ℤ)

/-- The finite source, retaining its B_X,n-linear structure. -/
abbrev finiteLeft (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n) ⋙
    inverseModules g (d.cA n) ⋙ extensionFunctor.{max r (t + 1), t + 1, t}
      (DX.i n)).mapHomologicalComplex (.up ℤ)

/-- The finite target, retaining its B_X,n-linear structure. -/
abbrev finiteRight (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
    inverseModules g (d.cB n)).mapHomologicalComplex (.up ℤ)

/-- The finite source with its S_X-action restricted along piB. -/
abbrev restrictedLeft (n : ℕ) :=
  finiteLeft g d n ⋙ scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)

/-- A local tensor F(p tensor s) in the specified finite target. -/
def finitePure (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((finiteRight g d n).obj P).X k).val.obj (op U) :=
  pure Y (DY.j ≫ DY.piB n) (P.X k)
    (op ((proEtaleIsoPostcompose g).obj U)) s p

set_option backward.isDefEq.respectTransparency true

section AdjointTransport

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
  [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
  {L₁ : A₁ ⥤ B₁} {V₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {V₂ : B₂ ⥤ A₂}
  (a₁ : L₁ ⊣ V₁) (a₂ : L₂ ⊣ V₂)
  (G : A₁ ⥤ A₂) (H : B₁ ⥤ B₂) (δ : V₁ ⋙ G ≅ H ⋙ V₂)

private def adjointTransport : G ⋙ L₂ ⟶ L₁ ⋙ H where
  app M := (a₂.homEquiv _ _).symm
    (G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M))
  naturality {M N} f := by
    apply (a₂.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [a₂.homEquiv_naturality_left, a₂.homEquiv_naturality_right]
    simp only [Functor.comp_obj, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← G.map_comp,
      show f ≫ a₁.unit.app N = a₁.unit.app M ≫ V₁.map (L₁.map f) from
        a₁.unit.naturality f, G.map_comp,
      Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ G.map (a₁.unit.app M) ≫ z) (δ.hom.naturality (L₁.map f))

private theorem adjointTransport_transpose (M : A₁) :
    a₂.homEquiv _ _ ((adjointTransport a₁ a₂ G H δ).app M) =
      G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M) :=
  (a₂.homEquiv _ _).apply_symm_apply _

private theorem isIso_of_precomp_on_image [H.EssSurj]
    {P Q : B₂} (f : P ⟶ Q)
    (hf : ∀ N : B₁, Function.Bijective (fun k : Q ⟶ H.obj N ↦ f ≫ k)) : IsIso f := by
  let e := H.objObjPreimageIso P
  obtain ⟨i, hi⟩ := (hf (H.objPreimage P)).2 e.inv
  let j := i ≫ e.hom
  have hj : f ≫ j = 𝟙 P := by simp [j, ← Category.assoc, hi]
  have hj' : j ≫ f = 𝟙 Q := by
    let e' := H.objObjPreimageIso Q
    apply (cancel_mono e'.inv).1
    apply (hf (H.objPreimage Q)).1
    simp only [← Category.assoc, hj, Category.id_comp]
  exact ⟨⟨j, hj, hj'⟩⟩

private theorem adjointTransport_isIso [G.Full] [G.Faithful]
    [H.Full] [H.Faithful] [H.EssSurj] :
    IsIso (adjointTransport a₁ a₂ G H δ) := by
  have hi (M : A₁) : IsIso ((adjointTransport a₁ a₂ G H δ).app M) := by
    apply isIso_of_precomp_on_image H
    intro N
    let E : (H.obj (L₁.obj M) ⟶ H.obj N) ≃
        (G.obj M ⟶ V₂.obj (H.obj N)) :=
      (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm |>.trans (a₁.homEquiv M N) |>.trans
        (Functor.FullyFaithful.ofFullyFaithful G).homEquiv |>.trans
          (Iso.homCongr (Iso.refl _) (δ.app N))
    have he (k : H.obj (L₁.obj M) ⟶ H.obj N) :
        a₂.homEquiv _ _ ((adjointTransport a₁ a₂ G H δ).app M ≫ k) = E k := by
      obtain ⟨l, rfl⟩ := H.map_surjective k
      rw [a₂.homEquiv_naturality_right, adjointTransport_transpose]
      have hpre : (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm
          (H.map l) = l := (Functor.FullyFaithful.ofFullyFaithful H).preimage_map l
      dsimp only [E, Equiv.trans_apply]
      rw [hpre]
      simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
      change (G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M)) ≫
        V₂.map (H.map l) = G.map (a₁.homEquiv _ _ l) ≫ δ.hom.app N
      have hn := δ.hom.naturality l
      dsimp only [Functor.comp_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc,
        ← G.map_comp, Adjunction.homEquiv_unit]
    constructor
    · intro k l hkl
      apply E.injective
      exact (he k).symm.trans ((congrArg (a₂.homEquiv _ _) hkl).trans (he l))
    · intro k
      obtain ⟨l, hl⟩ := E.surjective (a₂.homEquiv _ _ k)
      refine ⟨l, (a₂.homEquiv _ _).injective ?_⟩
      rw [he, hl]
  exact NatIso.isIso_of_isIso_app _

attribute [local irreducible] adjointTransport

end AdjointTransport

section ScalarAdjunctions

universe uC vC w
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R S T : Sheaf J CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency false in
private theorem pure_smul (a : R ⟶ S) (M : CochainPullback.Modules.{w, uC, vC} R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    extensionTmul a M U s x = s • extensionTmul a M U 1 x := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf a M)).app U
  change η (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
    s • η ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)
  have ht : (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
      s • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) := by
    change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
      (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
    rw [mul_one]
  exact (congrArg η ht).trans (η.hom.map_smul s _)

private theorem transpose_pure (a : R ⟶ S) (M : CochainPullback.Modules.{w, uC, vC} R)
    (N : CochainPullback.Modules.{w, uC, vC} S)
    (f : (extensionFunctor.{w, uC, vC} a).obj M ⟶ N) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    f.val.app U (extensionTmul a M U s x) =
      s • (show N.val.obj U from ((extensionAdjunction a).homEquiv M N f).val.app U x) := by
  rw [pure_smul, map_smul, Adjunction.homEquiv_unit]
  change _ = s • f.val.app U (((extensionAdjunction a).unit.app M).val.app U x)
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique a)).1 M U x
  change ((extensionAdjunction a).unit.app M).val.app U x = _ at hu
  rw [hu]

private def restrictionComp (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) :
    restrictionFunctor.{w, uC, vC, w} c ⋙ restrictionFunctor.{w, uC, vC, w} a ≅
      restrictionFunctor.{w, uC, vC, w} b :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (c.hom.app U).hom
        (b.hom.app U).hom (congrArg (fun f ↦ (f.hom.app U).hom) h)
        (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

private def extensionComp (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) :
    extensionFunctor.{w, uC, vC} a ⋙ extensionFunctor.{w, uC, vC} c ≅
      extensionFunctor.{w, uC, vC} b :=
  Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction c)).ofNatIsoRight
      (restrictionComp a c b h)) (extensionAdjunction b)

private theorem extensionComp_pure (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) (M : CochainPullback.Modules.{w, uC, vC} R) (U : Cᵒᵖ)
    (z : T.obj.obj U) (s : S.obj.obj U) (x : M.val.obj U) :
    ((extensionComp a c b h).hom.app M).val.app U
      (extensionTmul c ((extensionFunctor.{w, uC, vC} a).obj M) U z (extensionTmul a M U s x)) =
      extensionTmul b M U (z * c.hom.app U s) x := by
  let f := (extensionComp a c b h).hom.app M
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((extensionAdjunction a).comp (extensionAdjunction c)).ofNatIsoRight
      (restrictionComp a c b h)) (extensionAdjunction b) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  have hx := congrArg (fun k ↦ k.val.app U x) hh
  change (((extensionAdjunction a).homEquiv M _
    ((extensionAdjunction c).homEquiv _ _ f)).val.app U x) =
      ((extensionAdjunction b).unit.app M).val.app U x at hx
  change f.val.app U _ = _
  erw [transpose_pure c _ _ f U z (extensionTmul a M U s x)]
  erw [transpose_pure a M _ ((extensionAdjunction c).homEquiv _ _ f) U s x, hx]
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique b)).1 M U x
  change ((extensionAdjunction b).unit.app M).val.app U x = _ at hu
  rw [hu]
  change z • (c.hom.app U s • extensionTmul b M U 1 x) = _
  rw [pure_smul b M U (z * c.hom.app U s) x, mul_smul]

omit [EssentiallySmall.{w} C] in
attribute [local irreducible] extensionComp restrictionComp

end ScalarAdjunctions

section SiteTransport

variable {RY SY : Coeff.{t, r} Y} {RX SX : Coeff.{t, r} X}

set_option backward.isDefEq.respectTransparency false in
private theorem sectionwiseModules_equivalence
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : (isoSectionwiseModuleInverseImage g c).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max r (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  exact EM.isEquivalence_functor

set_option backward.isDefEq.respectTransparency false in
private theorem inverseModules_isEquivalence
    (c : (inverseRing g).obj RY ≅ RX) :
    (inverseModules g c).IsEquivalence :=
  sectionwiseModules_equivalence.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

private theorem inverse_square (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    inv ((forgetRing X).map cR.hom) ≫
        ((proEtaleIsoPostcompose g).sheafPushforwardContinuous RingCat
          (ProEt.topology X) (ProEt.topology Y)).map ((forgetRing Y).map aY) =
      (forgetRing X).map aX ≫ inv ((forgetRing X).map cS.hom) := by
  have hh : cR.inv ≫ (inverseRing g).map aY = aX ≫ cS.inv := by
    apply (cR.inv_comp_eq).2
    rw [← Category.assoc, ← h]
    simp
  rw [← Functor.map_inv, ← Functor.map_inv]
  have hr : inv cR.hom = cR.inv := IsIso.inv_eq_of_hom_inv_id cR.hom_inv_id
  have hs : inv cS.hom = cS.inv := IsIso.inv_eq_of_hom_inv_id cS.hom_inv_id
  rw [hr, hs]
  ext U x
  have hx := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) hh)
  exact hx x

set_option backward.isDefEq.respectTransparency false in
private def transportRestriction (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aY ⋙ inverseModules g cR ≅
      inverseModules g cS ⋙ restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aX :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (X₁ := (((restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aY) ⋙
        inverseModules g cR).obj M).val.obj U)
      (X₂ := ((inverseModules g cS ⋙
        restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aX).obj M).val.obj U)
      { __ := AddEquiv.refl _
        map_smul' a x := by
          have he := inverse_square g aY aX cR cS h
          have hx := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) he) a
          exact congrArg
            (fun z ↦ z • (show M.val.obj
              (op ((proEtaleIsoPostcompose g).obj U.unop)) from x)) hx })
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private def transportIso (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    inverseModules g cR ⋙ extensionFunctor.{max r (t + 1), t + 1, t} aX ≅
      extensionFunctor.{max r (t + 1), t + 1, t} aY ⋙ inverseModules g cS := by
  have := inverseModules_isEquivalence g cR
  have := inverseModules_isEquivalence g cS
  let f := adjointTransport (extensionAdjunction aY) (extensionAdjunction aX)
    (inverseModules g cR) (inverseModules g cS) (transportRestriction g aY aX cR cS h)
  have : IsIso f := adjointTransport_isIso _ _ _ _ _
  exact asIso f

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] transportIso transportRestriction

end SiteTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def finiteModuleIso (n : ℕ) :
    extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n) ⋙ inverseModules g (d.cA n) ⋙
        extensionFunctor.{max r (t + 1), t + 1, t} (DX.i n) ≅
      extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙ inverseModules g (d.cB n) :=
  Functor.isoWhiskerLeft (extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n))
      (transportIso g (DY.i n) (DX.i n) (d.cA n) (d.cB n) (d.i_comm n)) ≪≫
    Functor.isoWhiskerRight
      (extensionComp (DY.piA n) (DY.i n) (DY.j ≫ DY.piB n) (DY.projection_i n))
      (inverseModules g (d.cB n))

attribute [local irreducible] finiteModuleIso

private def finiteIso (n : ℕ) : finiteLeft g d n ≅ finiteRight g d n :=
  NatIso.mapHomologicalComplex (finiteModuleIso g d n) (.up ℤ)

attribute [local irreducible] finiteIso

private def restrictedArrow
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (L : A ⥤ B) (M : B ⥤ C) (N : C ⥤ F)
    (L' : A ⥤ D) (M' : D ⥤ E) (N' : E ⥤ F) (K : E ⥤ C)
    (a : L ⋙ M ⟶ L' ⋙ M' ⋙ K) (e : K ⋙ N ≅ N') :
    L ⋙ M ⋙ N ⟶ L' ⋙ M' ⋙ N' :=
  Functor.whiskerRight a N ≫ Functor.whiskerLeft (L' ⋙ M') e.hom

attribute [local irreducible] finitePure

end AlgebraicGeometry.ProEtale.ScalarQuotientChain
