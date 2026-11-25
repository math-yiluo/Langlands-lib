/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.AffineModelStalkTransportLinear
import Mathlib.RingTheory.Localization.BaseChange

/-! # Natural local-ring presentation of an affine module model

Source: Stacks Project, Tags 01BH, 01HV (7), and 008B.
(blueprint: new-e3-affine-model-stalk-presentation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- An affine model presents the original module stalk over its own local ring.
Source: Stacks Project, Tag 01BH, Lemma 17.10.5 (3), and Tag 01HV (7).
(blueprint: new-e3-affine-model-stalk-presentation)

Proof: Put q = isoSpec(x) and p = q.asIdeal. Restriction along the open immersion
U -> Y identifies F_x with (F|U)_x. Take the stalk of the supplied model
isomorphism and then use restriction along isoSpec to identify this with the
stalk of tilde M at q. These identifications are compatible with the stalk-ring
maps: represent both a ring element and a module element by germs on a common
neighborhood, and use the restriction scalar action and germ_smul. The germ
A -> S identifies S with A localized at A minus p. The map tilde.toStalk M q
is a module localization at the same multiplicative set. Transport this map
through the above stalk identifications. Its localization universal property,
and IsLocalizedModule.isBaseChange, give an S-linear equivalence S tensor_A M
-> F_x sending s tensor m to s times the transported germ of m. This specifies
the equivalence uniquely. For a compatible pair c,d, the given square identifies
their maps on germs of elements m. The stalk maps are S-linear, and pure tensors
generate S tensor_A M, so the two composites agree on every tensor. This proves
naturality. No global quasi-coherence of F is used: only its restriction is modeled
by tilde M. The zero module is covered by the same localization universal property;
an empty affine open has no point x satisfying hx. -/
theorem exists_affine_model_stalk_presentation
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1) :
    let A := (Γ(Y, U.1) : Type u)
    let S := (Y.presheaf.stalk x : Type u)
    letI : Algebra A S := (Y.presheaf.germ U.1 x hx).hom.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ δ : ∀ (F : Y.Modules) (M : ModuleCat.{u} A),
      ((Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) →
        (S ⊗[A] M) ≃ₗ[S] F.presheaf.stalk x,
      ∀ (F G : Y.Modules) (M N : ModuleCat.{u} A) (c : F ⟶ G) (d : M ⟶ N)
        (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M)
        (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj N),
        (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map d →
        ∀ t, c.stalkLinearMap x (δ F M eF t) =
          δ G N eG (d.hom.baseChange S t) := by
  classical
  dsimp
  let A := (Γ(Y, U.1) : Type u)
  let S := (Y.presheaf.stalk x : Type u)
  let : Algebra A S := (Y.presheaf.germ U.1 x hx).hom.toAlgebra
  let q := U.2.primeIdealOf ⟨x, hx⟩
  let W := q.asIdeal.primeCompl
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let inst (F : Y.Modules) : Module A (F.presheaf.stalk x) :=
    Module.compHom _ (Y.presheaf.germ U.1 x hx).hom
  have tower (F : Y.Modules) : IsScalarTower A S (F.presheaf.stalk x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  let E (F : Y.Modules) (M : ModuleCat.{u} A)
      (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) :
      (tilde M).presheaf.stalk q ≃ₗ[A] F.presheaf.stalk x := by
    exact { affineModelStalkAddEquiv x U hx F M e with
      map_smul' := affineModelStalkAddEquiv_smul x U hx F M e }
  let f (F : Y.Modules) (M : ModuleCat.{u} A)
      (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) :=
    (E F M e).toLinearMap.comp (tilde.toStalk M q).hom
  have hloc (F : Y.Modules) (M : ModuleCat.{u} A)
      (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) :
      IsLocalizedModule W (f F M e) :=
    IsLocalizedModule.of_linearEquiv W (tilde.toStalk M q).hom (E F M e)
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  let δ (F : Y.Modules) (M : ModuleCat.{u} A)
      (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) :
      (S ⊗[A] M) ≃ₗ[S] F.presheaf.stalk x := by
    have := hloc F M e
    exact (IsLocalizedModule.isBaseChange W S (f F M e)).equiv
  refine ⟨δ, ?_⟩
  intro F G M N c d eF eG h t
  have hn (m : M) : c.stalkLinearMap x (f F M eF m) = f G N eG (d.hom m) := by
    let K := Scheme.Modules.toPresheaf U.1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.1.toScheme)
    let L := Scheme.Modules.toPresheaf (Spec Γ(Y, U.1)) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} q
    let J := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    let a := Scheme.Modules.restrictStalkNatIso U.2.isoSpec.hom ⟨x, hx⟩
    let b := Scheme.Modules.restrictStalkNatIso U.1.ι ⟨x, hx⟩
    have he : (T.map d) ≫ eG.inv = eF.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map c := by
      apply (cancel_mono eG.hom).mp
      simp only [Category.assoc, eG.inv_hom_id]
      erw [h, ← Category.assoc, eF.inv_hom_id, Category.id_comp, Category.comp_id]
      rfl
    have he' := congrArg K.map he
    simp only [Functor.map_comp] at he'
    have ha := a.inv.naturality (tilde.map d)
    change L.map (tilde.map d) ≫ a.inv.app (tilde N) =
      a.inv.app (tilde M) ≫ K.map (T.map d) at ha
    have hb := b.hom.naturality c
    change K.map ((Scheme.Modules.restrictFunctor U.1.ι).map c) ≫ b.hom.app G =
      b.hom.app F ≫ J.map c at hb
    have hc : a.inv.app (tilde M) ≫ K.map eF.inv ≫ b.hom.app F ≫ J.map c =
        L.map (tilde.map d) ≫ a.inv.app (tilde N) ≫ K.map eG.inv ≫ b.hom.app G := by
      erw [← hb]
      erw [← Category.assoc (K.map eF.inv), ← he']
      simp only [Category.assoc]
      erw [← Category.assoc (a.inv.app (tilde M)), ← ha]
      simp only [Category.assoc]
    have hm := ConcreteCategory.congr_hom hc ((tilde.toStalk M q).hom m)
    simp only [ConcreteCategory.comp_apply] at hm
    change c.stalkLinearMap x
      (affineModelStalkAddEquiv x U hx F M eF ((tilde.toStalk M q).hom m)) =
      affineModelStalkAddEquiv x U hx G N eG ((tilde.toStalk N q).hom (d.hom m))
    change c.stalkLinearMap x
      (affineModelStalkAddEquiv x U hx F M eF ((tilde.toStalk M q).hom m)) =
      affineModelStalkAddEquiv x U hx G N eG
        ((ConcreteCategory.hom (L.map (tilde.map d))) ((tilde.toStalk M q).hom m)) at hm
    refine hm.trans (congrArg (affineModelStalkAddEquiv x U hx G N eG) ?_)
    dsimp only [L, Scheme.Modules.toPresheaf, Functor.comp_map, tilde.toStalk,
      StructureSheaf.toStalkₗ]
    change (TopCat.Presheaf.stalkFunctor Ab.{u} q).map
      (tilde.map d).mapPresheaf
      ((tilde M).presheaf.germ ⊤ q (by simp) (StructureSheaf.toOpenₗ A M ⊤ m)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    have hd := ConcreteCategory.congr_hom (tilde.toOpen_map_app d ⊤) m
    change (tilde N).presheaf.germ ⊤ q _ _ = (tilde N).presheaf.germ ⊤ q _ _
    congr 1
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp [ht, ht']
  | tmul s m =>
    change c.stalkLinearMap x
      ((IsLocalizedModule.isBaseChange W S (f F M eF)).equiv (s ⊗ₜ[A] m)) =
      (IsLocalizedModule.isBaseChange W S (f G N eG)).equiv (s ⊗ₜ[A] d.hom m)
    erw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
    simp only [map_smul]
    rw [hn]

end AlgebraicGeometry
