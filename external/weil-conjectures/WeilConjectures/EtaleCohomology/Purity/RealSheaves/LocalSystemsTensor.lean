/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems

/-!
# The Galois correspondence for finite local systems is a tensor equivalence

Let `Y` be a scheme, `s` a geometric point, `Λ` a finite ring and `G` a group acting naturally on
the geometric fibres of finite étale `Y`-schemes (for instance `π₁(Y, s)`). The geometric stalk
`AlgebraicGeometry.Scheme.galoisRepFunctor` sends a finite locally constant sheaf of
`Λ`-modules `F` to its stalk `F_s` with the action of `G` through the finite étale cover
representing `F`. We show it is compatible with tensor products and units:

- the stalk of a tensor product of sheaves of `Λ`-modules is the tensor product of the stalks,
  `(F₁ ⊗ F₂)_s ≅ F₁_s ⊗ F₂_s`, naturally, sending the germ of `σ ⊗ τ` to `σ_s ⊗ τ_s`
  (`AlgebraicGeometry.Scheme.sheafFiberTensorIso'`), and the stalk of `Λ_Y` is `Λ`
  (`AlgebraicGeometry.Scheme.sheafFiberUnitIso'`);
- these identifications are `G`-equivariant: `g (x ⊗ y) = g x ⊗ g y` and `G` acts trivially on
  the stalk of `Λ_Y` (`AlgebraicGeometry.Scheme.galoisRepFunctorTensorNatIso`,
  `AlgebraicGeometry.Scheme.galoisRepFunctorUnitIso`).

The Galois action is only natural for morphisms of the underlying sheaves of *sets*, which is
how the equivariance is proved: the pairing `(σ, τ) ↦ σ ⊗ τ` is a morphism
`F₁ ⊞ F₂ ⟶ F₁ ⊗ F₂` of finite locally constant sheaves of sets
(`AlgebraicGeometry.Scheme.tensorPairing`), and a constant section of `Λ_Y` is a morphism from
the terminal sheaf of sets (`AlgebraicGeometry.Scheme.unitSection`).

## Main results

- `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor`: the Galois
  correspondence (`proposition-lattices-representations-normal-scheme`) as a tensor equivalence.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

instance (X : ModuleCat.{u + 1} Λ) : PreservesFilteredColimitsOfSize.{u, u} (tensorRight X) :=
  ⟨fun _ _ _ ↦ ⟨fun {F} ↦ preservesColimit_of_natIso F
    (BraidedCategory.tensorLeftIsoTensorRight X)⟩⟩

/-- For sheaves `F` and `G`, the sheafification of the presheaf tensor product
`F ⊗ᵖ G` is the sheaf tensor product `F ⊗ G`. -/
def Scheme.sheafifyTensorIso (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (F.obj ⊗ G.obj) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      F.obj G.obj).symm ≪≫
    tensorIso (asIso ((sheafificationAdjunction _ _).counit.app F))
      (asIso ((sheafificationAdjunction _ _).counit.app G))

/-- The canonical map from the presheaf tensor product `F ⊗ᵖ G` of two sheaves to their sheaf
tensor product `F ⊗ G`: on sections, `σ ⊗ τ ↦ σ ⊗ τ`. -/
def Scheme.tensorToSheafTensor (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify _ _ ≫ (Scheme.sheafifyTensorIso F G).hom.hom

@[reassoc]
lemma Scheme.tensorToSheafTensor_naturality
    {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') :
    (f.hom ⊗ₘ g.hom) ≫ Scheme.tensorToSheafTensor F' G' =
      Scheme.tensorToSheafTensor F G ≫ (f ⊗ₘ g).hom := by
  have n₁ : (presheafToSheaf _ _).map f.hom ≫ (sheafificationAdjunction _ _).counit.app F' =
      (sheafificationAdjunction _ _).counit.app F ≫ f :=
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.naturality f
  have n₂ : (presheafToSheaf _ _).map g.hom ≫ (sheafificationAdjunction _ _).counit.app G' =
      (sheafificationAdjunction _ _).counit.app G ≫ g :=
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.naturality g
  have h : (presheafToSheaf _ _).map (f.hom ⊗ₘ g.hom) ≫ (Scheme.sheafifyTensorIso F' G').hom =
      (Scheme.sheafifyTensorIso F G).hom ≫ (f ⊗ₘ g) := by
    simp only [Scheme.sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      tensorIso_hom, asIso_hom, Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc (presheafToSheaf _ _) f.hom g.hom,
      tensorHom_comp_tensorHom, n₁, n₂, tensorHom_comp_tensorHom]
  rw [Scheme.tensorToSheafTensor, Scheme.tensorToSheafTensor, toSheafify_naturality_assoc,
    Category.assoc]
  exact congrArg (fun φ ↦ toSheafify _ _ ≫ φ.hom) h


section Stalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

instance (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G)) := by
  rw [Scheme.tensorToSheafTensor, Functor.map_comp]
  have : IsIso (Scheme.sheafifyTensorIso F G).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso (Scheme.sheafifyTensorIso F G)).hom)
  infer_instance

/-- The stalk at `s` of a tensor product of sheaves of `Λ`-modules is the tensor product of the
stalks, `(F ⊗ G)_s ≅ F_s ⊗ G_s`: the stalk of the presheaf tensor product is the tensor product of
the stalks, and sheafifying does not change stalks. It sends the germ of `σ ⊗ τ` to
`σ_s ⊗ τ_s` (`AlgebraicGeometry.Scheme.sheafFiberTensorIso'_inv_tmul`). -/
def Scheme.sheafFiberTensorIso' (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (F ⊗ G) ≅
      (Scheme.pointSmallEtale s).sheafFiber.obj F ⊗ (Scheme.pointSmallEtale s).sheafFiber.obj G :=
  (asIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G))).symm ≪≫
    (Functor.Monoidal.μIso (Scheme.pointSmallEtale s).presheafFiber F.obj G.obj).symm

lemma Scheme.sheafFiberTensorIso'_inv (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Scheme.sheafFiberTensorIso' s F G).inv =
      Functor.LaxMonoidal.μ (Scheme.pointSmallEtale s).presheafFiber F.obj G.obj ≫
        (Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G) :=
  rfl

/-- `AlgebraicGeometry.Scheme.sheafFiberTensorIso'` on germs: the germ at `s` of `σ ⊗ τ` is
`σ_s ⊗ τ_s`. -/
lemma Scheme.sheafFiberTensorIso'_inv_tmul (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) (σ : F.obj.obj (.op V))
    (τ : G.obj.obj (.op V)) :
    (Scheme.sheafFiberTensorIso' s F G).inv.hom
        ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj σ ⊗ₜ
          (Scheme.pointSmallEtale s).toPresheafFiber V v G.obj τ) =
      (Scheme.pointSmallEtale s).toPresheafFiber V v (F ⊗ G).obj
        ((Scheme.tensorToSheafTensor F G).app (.op V) (σ ⊗ₜ τ)) := by
  have h := ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.tensorHom_comp_toPresheafFiber_μ (Scheme.pointSmallEtale s) V v
      F.obj G.obj) (σ ⊗ₜ τ)
  rw [Scheme.sheafFiberTensorIso'_inv, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ConcreteCategory.comp_apply] at h
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  erw [h]
  exact (Scheme.pointSmallEtale s).toPresheafFiber_naturality_apply _ V v _

/-- Naturality of `AlgebraicGeometry.Scheme.sheafFiberTensorIso'` in both variables. -/
@[reassoc]
lemma Scheme.sheafFiberTensorIso'_hom_naturality
    {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') :
    (Scheme.pointSmallEtale s).sheafFiber.map (f ⊗ₘ g) ≫ (Scheme.sheafFiberTensorIso' s F' G').hom =
      (Scheme.sheafFiberTensorIso' s F G).hom ≫
        ((Scheme.pointSmallEtale s).sheafFiber.map f ⊗ₘ
          (Scheme.pointSmallEtale s).sheafFiber.map g) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, Scheme.sheafFiberTensorIso'_inv,
    Scheme.sheafFiberTensorIso'_inv, Category.assoc]
  change _ = ((Scheme.pointSmallEtale s).presheafFiber.map f.hom ⊗ₘ
    (Scheme.pointSmallEtale s).presheafFiber.map g.hom) ≫ _
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp,
    Scheme.tensorToSheafTensor_naturality, Functor.map_comp]
  rfl

end Stalk

/-- The pairing `F ⊞ G → F ⊗ G`, `(σ, τ) ↦ σ ⊗ τ`, as a morphism of the underlying étale sheaves
of sets. It is not linear, but it is a morphism of finite locally constant sheaves of sets, so it
commutes with the Galois action on stalks. -/
def Scheme.tensorPairing (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj (F ⊞ G) ⟶
      (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj (F ⊗ G) :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom fun z ↦ (Scheme.tensorToSheafTensor F G).app U
        ((biprod.fst : F ⊞ G ⟶ F).hom.app U z ⊗ₜ (biprod.snd : F ⊞ G ⟶ G).hom.app U z)
      naturality U V i := by
        ext z
        change (Scheme.tensorToSheafTensor F G).app V
            ((biprod.fst : F ⊞ G ⟶ F).hom.app V ((F ⊞ G).obj.map i z) ⊗ₜ
              (biprod.snd : F ⊞ G ⟶ G).hom.app V ((F ⊞ G).obj.map i z)) =
          (F ⊗ G).obj.map i ((Scheme.tensorToSheafTensor F G).app U
            ((biprod.fst : F ⊞ G ⟶ F).hom.app U z ⊗ₜ (biprod.snd : F ⊞ G ⟶ G).hom.app U z))
        rw [← NatTrans.naturality_apply (Scheme.tensorToSheafTensor F G) i,
          NatTrans.naturality_apply (biprod.fst : F ⊞ G ⟶ F).hom i,
          NatTrans.naturality_apply (biprod.snd : F ⊞ G ⟶ G).hom i]
        rfl }

lemma Scheme.tensorPairing_app (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etaleᵒᵖ) (z : (F ⊞ G).obj.obj U) :
    (Scheme.tensorPairing F G).hom.app U z = (Scheme.tensorToSheafTensor F G).app U
      ((biprod.fst : F ⊞ G ⟶ F).hom.app U z ⊗ₜ (biprod.snd : F ⊞ G ⟶ G).hom.app U z) :=
  rfl

section Galois

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) [Finite Λ]

/-- On the stalk at `s`, the pairing `AlgebraicGeometry.Scheme.tensorPairing` is
`(x, y) ↦ x ⊗ y`, read through `AlgebraicGeometry.Scheme.sheafFiberTensorIso'`. -/
lemma Scheme.IsFiniteLocallyConstantSheaf.sheafFiber_map_tensorPairing
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hB : IsFiniteLocallyConstantSheaf (F ⊞ G)) (hT : IsFiniteLocallyConstantSheaf (F ⊗ G))
    (z : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj (F ⊞ G)) :
    (hT.stalkEquiv s).symm ((Scheme.pointSmallEtale s).sheafFiber.map (Scheme.tensorPairing F G)
        (hB.stalkEquiv s z)) =
      (Scheme.sheafFiberTensorIso' s F G).inv.hom
        ((Scheme.pointSmallEtale s).sheafFiber.map (biprod.fst : F ⊞ G ⟶ F) z ⊗ₜ
          (Scheme.pointSmallEtale s).sheafFiber.map (biprod.snd : F ⊞ G ⟶ G) z) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, w, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective z
  rw [Equiv.symm_apply_eq]
  erw [hB.stalkEquiv_toPresheafFiber]
  change _ = hT.stalkEquiv s ((Scheme.sheafFiberTensorIso' s F G).inv.hom
    ((Scheme.pointSmallEtale s).presheafFiber.map (biprod.fst : F ⊞ G ⟶ F).hom
        ((Scheme.pointSmallEtale s).toPresheafFiber V v (F ⊞ G).obj w) ⊗ₜ
      (Scheme.pointSmallEtale s).presheafFiber.map (biprod.snd : F ⊞ G ⟶ G).hom
        ((Scheme.pointSmallEtale s).toPresheafFiber V v (F ⊞ G).obj w)))
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
    GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
    Scheme.sheafFiberTensorIso'_inv_tmul, hT.stalkEquiv_toPresheafFiber]
  exact GrothendieckTopology.Point.toPresheafFiber_naturality_apply _
    (Scheme.tensorPairing F G).hom V v w

variable (G : Type u) [Group G] [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G]

/-- The Galois action on stalks commutes with the stalk of any morphism of the underlying
sheaves of sets, linear or not. -/
lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_map_of_types (g : G)
    {F₁ F₂ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h₁ : IsFiniteLocallyConstantSheaf F₁) (h₂ : IsFiniteLocallyConstantSheaf F₂)
    (φ : h₁.toFLC ⟶ h₂.toFLC)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F₁) :
    (h₂.stalkEquiv s).symm ((Scheme.pointSmallEtale s).sheafFiber.map φ.hom
        (h₁.stalkEquiv s (h₁.galoisAct s G g x))) =
      h₂.galoisAct s G g ((h₂.stalkEquiv s).symm
        ((Scheme.pointSmallEtale s).sheafFiber.map φ.hom (h₁.stalkEquiv s x))) := by
  simp only [galoisAct, Equiv.apply_symm_apply,
    Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g φ]

/-- **The Galois action on the stalk of a tensor product** is the tensor product of the Galois
actions: `g (x ⊗ y) = g x ⊗ g y`, through `AlgebraicGeometry.Scheme.sheafFiberTensorIso'`. -/
lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_sheafFiberTensorIso'_inv_tmul (g : G)
    {F₁ F₂ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h₁ : IsFiniteLocallyConstantSheaf F₁) (h₂ : IsFiniteLocallyConstantSheaf F₂)
    (hT : IsFiniteLocallyConstantSheaf (F₁ ⊗ F₂))
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F₁)
    (y : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F₂) :
    hT.galoisAct s G g ((Scheme.sheafFiberTensorIso' s F₁ F₂).inv.hom (x ⊗ₜ y)) =
      (Scheme.sheafFiberTensorIso' s F₁ F₂).inv.hom
        (h₁.galoisAct s G g x ⊗ₜ h₂.galoisAct s G g y) := by
  have := h₁
  have := h₂
  have hB : IsFiniteLocallyConstantSheaf (F₁ ⊞ F₂) :=
    Scheme.IsFiniteLocallyConstantSheaf.biprod F₁ F₂
  let St := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let z := St.map biprod.inl x + St.map biprod.inr y
  have hfst : St.map biprod.fst z = x := St.map_biprod_fst_inl_add_inr x y
  have hsnd : St.map biprod.snd z = y := St.map_biprod_snd_inl_add_inr x y
  have k₁ := hB.sheafFiber_map_tensorPairing s hT z
  have k₂ := hB.sheafFiber_map_tensorPairing s hT (hB.galoisAct s G g z)
  rw [hfst, hsnd] at k₁
  rw [galoisAct_naturality s G g hB h₁, galoisAct_naturality s G g hB h₂, hfst, hsnd] at k₂
  rw [← k₁, ← k₂]
  exact (galoisAct_map_of_types s G g hB hT (ObjectProperty.homMk (Scheme.tensorPairing F₁ F₂))
    z).symm

/-- The Galois representation on the stalk of a tensor product is the tensor product of the
Galois representations, through `AlgebraicGeometry.Scheme.sheafFiberTensorIso'`. -/
def Scheme.IsFiniteLocallyConstantSheaf.galoisRepTensorEquiv
    {F₁ F₂ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h₁ : IsFiniteLocallyConstantSheaf F₁) (h₂ : IsFiniteLocallyConstantSheaf F₂)
    (hT : IsFiniteLocallyConstantSheaf (F₁ ⊗ F₂)) :
    (hT.galoisRep s G).Equiv ((h₁.galoisRep s G).tprod (h₂.galoisRep s G)) :=
  .mk (Scheme.sheafFiberTensorIso' s F₁ F₂).toLinearEquiv fun g ↦ by
    let e := (Scheme.sheafFiberTensorIso' s F₁ F₂).toLinearEquiv
    have key (t) : hT.galoisRep s G g (e.symm t) =
        e.symm ((h₁.galoisRep s G).tprod (h₂.galoisRep s G) g t) := by
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [Representation.tprod_apply, TensorProduct.map_tmul]
        exact galoisAct_sheafFiberTensorIso'_inv_tmul s G g h₁ h₂ hT x y
      | add t t' ht ht' => simp only [map_add, ht, ht']
    ext w
    obtain ⟨t, rfl⟩ := e.symm.surjective w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
    change e (e.symm _) = (h₁.galoisRep s G).tprod (h₂.galoisRep s G) g (e (e.symm t))
    rw [e.apply_symm_apply, e.apply_symm_apply]

end Galois

/-- Finite locally constant sheaves of `Λ`-modules are closed under tensor products and contain
the constant sheaf `Λ_Y`, so they form a full monoidal subcategory. -/
instance Scheme.isMonoidal_isFiniteLocallyConstantSheaf :
    ObjectProperty.IsMonoidal (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
      Scheme.IsFiniteLocallyConstantSheaf F) where
  prop_unit := { }
  prop_tensor _ _ h₁ h₂ := h₁.tensorObj h₂

section GaloisRepFunctor

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) [Finite Λ]
  (G : Type u) [Group G] [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G]

/-- **The geometric stalk is compatible with tensor products**: the representation of `G` on the
stalk at `s` of `F₁ ⊗ F₂` is the tensor product of those on the stalks of `F₁` and `F₂`. The
underlying linear map is `AlgebraicGeometry.Scheme.sheafFiberTensorIso'`,
`(F₁ ⊗ F₂)_s ≅ F₁_s ⊗ F₂_s`. -/
def Scheme.galoisRepFunctorTensorIso
    (F₁ F₂ : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstantSheaf F)) :
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj (F₁ ⊗ F₂) ≅
      (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj F₁ ⊗
        (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj F₂ :=
  Rep.mkIso (F₁.2.galoisRepTensorEquiv s G F₂.2 (F₁ ⊗ F₂).2)

lemma Scheme.galoisRepFunctorTensorIso_hom_hom_apply
    (F₁ F₂ : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstantSheaf F))
    (w : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (F₁.obj ⊗ F₂.obj)) :
    (Scheme.galoisRepFunctorTensorIso s G F₁ F₂).hom.hom w =
      (Scheme.sheafFiberTensorIso' s F₁.obj F₂.obj).hom.hom w :=
  rfl

/-- Naturality of `AlgebraicGeometry.Scheme.galoisRepFunctorTensorIso` in both variables. -/
@[reassoc]
lemma Scheme.galoisRepFunctorTensorIso_hom_naturality
    {F₁ F₁' F₂ F₂' : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstantSheaf F)}
    (f₁ : F₁ ⟶ F₁') (f₂ : F₂ ⟶ F₂') :
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).map (f₁ ⊗ₘ f₂) ≫
        (Scheme.galoisRepFunctorTensorIso s G F₁' F₂').hom =
      (Scheme.galoisRepFunctorTensorIso s G F₁ F₂).hom ≫
        ((Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).map f₁ ⊗ₘ
          (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).map f₂) := by
  ext w
  exact ConcreteCategory.congr_hom (Scheme.sheafFiberTensorIso'_hom_naturality s f₁.hom f₂.hom) w

/-- **The geometric stalk is a tensor functor**, as an isomorphism of bifunctors
`(F₁ ⊗ F₂)_s ≅ F₁_s ⊗ F₂_s` of representations of `G`, natural in `F₁` and `F₂`
(`AlgebraicGeometry.Scheme.galoisRepFunctorTensorIso`). -/
def Scheme.galoisRepFunctorTensorNatIso :
    MonoidalCategory.tensor _ ⋙ Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ) ≅
      (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).prod
        (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)) ⋙
        MonoidalCategory.tensor (Rep.{u + 1} Λ G) :=
  NatIso.ofComponents (fun X ↦ Scheme.galoisRepFunctorTensorIso s G X.1 X.2)
    fun f ↦ Scheme.galoisRepFunctorTensorIso_hom_naturality s G f.1 f.2

end GaloisRepFunctor

section Unit

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

variable (Y Λ) in
/-- The canonical map from the constant presheaf `Λ` to the constant sheaf `Λ_Y`. -/
def Scheme.unitToSheafUnit :
    𝟙_ (Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⟶
      (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj :=
  toSheafify _ _ ≫ (Functor.Monoidal.εIso (presheafToSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).inv.hom

instance : IsIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.unitToSheafUnit Y Λ)) := by
  rw [Scheme.unitToSheafUnit, Functor.map_comp]
  have : IsIso (Functor.Monoidal.εIso (presheafToSheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))).inv.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso (Functor.Monoidal.εIso
      (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).inv)
  infer_instance

variable (Λ) in
/-- The stalk at `s` of the constant sheaf `Λ_Y` is `Λ`. It sends `c ∈ Λ` to the germ of the
constant section `c` (`AlgebraicGeometry.Scheme.sheafFiberUnitIso'_inv_apply`). -/
def Scheme.sheafFiberUnitIso' :
    (Scheme.pointSmallEtale s).sheafFiber.obj (𝟙_ (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) ≅ 𝟙_ (ModuleCat.{u + 1} Λ) :=
  (asIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.unitToSheafUnit Y Λ))).symm ≪≫
    (Functor.Monoidal.εIso (Scheme.pointSmallEtale s).presheafFiber).symm

lemma Scheme.sheafFiberUnitIso'_inv_apply (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (c : Λ) :
    (Scheme.sheafFiberUnitIso' Λ s).inv.hom c =
      (Scheme.pointSmallEtale s).toPresheafFiber V v
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj
        ((Scheme.unitToSheafUnit Y Λ).app (.op V) c) := by
  change (Scheme.pointSmallEtale s).presheafFiber.map (Scheme.unitToSheafUnit Y Λ)
    ((Functor.LaxMonoidal.ε ((Scheme.pointSmallEtale s).presheafFiber
      (A := ModuleCat.{u + 1} Λ))).hom c) = _
  rw [GrothendieckTopology.Point.toPresheafFiber_ε _ V v]
  exact (Scheme.pointSmallEtale s).toPresheafFiber_naturality_apply _ V v _

/-- The constant section `c` of `Λ_Y`, as a morphism from the terminal sheaf of sets to the
sheaf of sets underlying `Λ_Y`. -/
def Scheme.unitSection (c : Λ) :
    ⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1))) ⟶
      (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom fun _ ↦ (Scheme.unitToSheafUnit Y Λ).app U c
      naturality U V i := by
        ext z
        change (Scheme.unitToSheafUnit Y Λ).app V c =
          (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj.map i
            ((Scheme.unitToSheafUnit Y Λ).app U c)
        rw [← NatTrans.naturality_apply (Scheme.unitToSheafUnit Y Λ) i]
        rfl }

variable [Finite Λ] (G : Type u) [Group G] [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsNaturalSMul (Scheme.FiniteEtale.fiber s) G]

/-- **The Galois action on the stalk of the constant sheaf `Λ_Y` is trivial**: every element of
the stalk is the germ of a constant section, which comes from the terminal sheaf of sets, whose
stalk is a point. -/
lemma Scheme.IsFiniteLocallyConstantSheaf.galoisAct_unit
    (hU : IsFiniteLocallyConstantSheaf (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (g : G) (w : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :
    hU.galoisAct s G g w = w := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  obtain ⟨V, v, σ, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective w
  set c : Λ := (Scheme.sheafFiberUnitIso' Λ s).hom.hom
    ((Scheme.pointSmallEtale s).toPresheafFiber V v
      (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj σ)
  have hw : (Scheme.pointSmallEtale s).toPresheafFiber V v
      (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj σ =
      (Scheme.pointSmallEtale s).toPresheafFiber V v
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj
        ((Scheme.unitToSheafUnit Y Λ).app (.op V) c) := by
    rw [← Scheme.sheafFiberUnitIso'_inv_apply]
    exact (ConcreteCategory.congr_hom (Scheme.sheafFiberUnitIso' Λ s).hom_inv_id _).symm
  erw [hw]
  obtain ⟨⟨𝒰, -⟩, -⟩ := hU.toFLC.property
  let S0 : Y.FiniteLocallyConstant :=
    ⟨⊤_ _, ⟨𝒰, fun i ↦ Scheme.isConstant_over_terminal _⟩, Scheme.isFiniteSheaf_terminal⟩
  let e := PreservesTerminal.iso ((sheafToPresheaf Y.smallEtaleTopology (Type (u + 1))) ⋙
    (CategoryTheory.evaluation _ _).obj (.op V)) ≪≫ Types.terminalIso
  let pt := (Scheme.pointSmallEtale s).toPresheafFiber V v S0.obj.obj (e.inv PUnit.unit)
  have hpt : (Scheme.pointSmallEtale s).sheafFiber.map (Scheme.unitSection c) pt =
      hU.stalkEquiv s ((Scheme.pointSmallEtale s).toPresheafFiber V v
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj
        ((Scheme.unitToSheafUnit Y Λ).app (.op V) c)) := by
    rw [hU.stalkEquiv_toPresheafFiber]
    exact (Scheme.pointSmallEtale s).toPresheafFiber_naturality_apply _ V v _
  have : Subsingleton ((Scheme.pointSmallEtale s).sheafFiber.obj S0.obj) :=
    Functor.subsingleton_obj_terminal
      (H := (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1)))
  have hn := Scheme.FiniteLocallyConstant.galoisSMul_naturality s G g (S := S0)
    (S' := hU.toFLC) (ObjectProperty.homMk (Scheme.unitSection c)) pt
  rw [Subsingleton.elim (Scheme.FiniteLocallyConstant.galoisSMul s G g S0 pt) pt] at hn
  rw [galoisAct, ← hpt]
  erw [← hn]
  erw [hpt, Equiv.symm_apply_apply]

/-- **The geometric stalk of the constant sheaf is the trivial representation**: the
representation of `G` on the stalk at `s` of `Λ_Y` is `Λ` with the trivial action. The
underlying linear map is `AlgebraicGeometry.Scheme.sheafFiberUnitIso'`. -/
def Scheme.galoisRepFunctorUnitIso :
    (Scheme.galoisRepFunctor (s := s) (G := G) (Λ := Λ)).obj (𝟙_ _) ≅ 𝟙_ (Rep.{u + 1} Λ G) :=
  Rep.mkIso (.mk (Scheme.sheafFiberUnitIso' Λ s).toLinearEquiv fun g ↦ LinearMap.ext fun w ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply]
    exact congrArg _ (Scheme.IsFiniteLocallyConstantSheaf.galoisAct_unit s G _ g w))

lemma Scheme.galoisRepFunctorUnitIso_hom_hom_apply
    (w : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :
    (Scheme.galoisRepFunctorUnitIso s G).hom.hom w = (Scheme.sheafFiberUnitIso' Λ s).hom.hom w :=
  rfl

end Unit


/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems, with its tensor structure.

Let `Y` be a connected scheme, `s` a geometric point, `Λ` a finite ring and `G = π₁(Y, s)` a
fundamental group of the fibre functor at `s`. The geometric stalk at `s` is an equivalence `e`
between finite locally constant sheaves of `Λ`-modules on `Y_ét` and finite continuous
representations of `G` such that
* the underlying `Λ`-module of `e F` is the stalk `F_s` (the isomorphism `η`);
* `e` is compatible with tensor products: there is an isomorphism of bifunctors
  `τ : e (F₁ ⊗ F₂) ≅ e F₁ ⊗ e F₂`, natural in `F₁` and `F₂`, whose underlying linear map is, via
  `η`, the identification `(F₁ ⊗ F₂)_s ≅ F₁_s ⊗ F₂_s` of
  `AlgebraicGeometry.Scheme.sheafFiberTensorIso'`;
* `e` sends the constant sheaf `Λ_Y` to the trivial representation `Λ`.
Exactness is `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor_of_isFundamentalGroup
    (Y : Scheme.{u}) [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G] :
    ∃ (e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)))
      (η : e.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber)
      (τ : MonoidalCategory.tensor _ ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
        (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
          MonoidalCategory.tensor (Rep.{u + 1} Λ G)),
      (∀ F₁ F₂, (forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ)).map (τ.hom.app (F₁, F₂)) =
        η.hom.app (F₁ ⊗ F₂) ≫ (Scheme.sheafFiberTensorIso' s F₁.obj F₂.obj).hom ≫
          (η.inv.app F₁ ⊗ₘ η.inv.app F₂)) ∧
      Nonempty ((e.functor ⋙ ObjectProperty.ι _).obj (𝟙_ _) ≅ 𝟙_ (Rep.{u + 1} Λ G)) := by
  refine ⟨(Scheme.galoisRepFunctorFiniteContinuous s (Λ := Λ) G).asEquivalence,
    Scheme.galoisRepFunctorCompForget₂Iso s G, Scheme.galoisRepFunctorTensorNatIso s G,
    fun F₁ F₂ ↦ ?_, ⟨Scheme.galoisRepFunctorUnitIso s G⟩⟩
  have h₁ : (Scheme.galoisRepFunctorCompForget₂Iso s G).inv.app F₁ = 𝟙 _ := rfl
  have h₂ : (Scheme.galoisRepFunctorCompForget₂Iso s G).inv.app F₂ = 𝟙 _ := rfl
  have h₃ : (Scheme.galoisRepFunctorCompForget₂Iso s G).hom.app (F₁ ⊗ F₂) = 𝟙 _ := rfl
  rw [h₁, h₂, h₃]
  erw [MonoidalCategory.id_tensorHom_id]
  ext w
  rfl

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems, as an exact *tensor* equivalence.

For a connected scheme `Y`, a geometric point `s` and a finite ring `Λ`, there is a profinite
group `G` (the étale fundamental group `π₁(Y, s)`) and an equivalence `e` between finite locally
constant sheaves of `Λ`-modules on `Y_ét` and finite continuous representations of `G`, such that
the underlying `Λ`-module of `e F` is the stalk `F_s` (via `η`), `e` is compatible with tensor
products through an isomorphism of bifunctors `τ` lifting
`(F₁ ⊗ F₂)_s ≅ F₁_s ⊗ F₂_s` (`AlgebraicGeometry.Scheme.sheafFiberTensorIso'`), and `e` sends
`Λ_Y` to the trivial representation. See the `_of_isFundamentalGroup` version for the statement
with `G` named; exactness is
`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor (Y : Scheme.{u})
    [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (G : ProfiniteGrp.{u})
      (e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)))
      (η : e.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber)
      (τ : MonoidalCategory.tensor _ ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
        (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
          MonoidalCategory.tensor (Rep.{u + 1} Λ G)),
      (∀ F₁ F₂, (forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ)).map (τ.hom.app (F₁, F₂)) =
        η.hom.app (F₁ ⊗ F₂) ≫ (Scheme.sheafFiberTensorIso' s F₁.obj F₂.obj).hom ≫
          (η.inv.app F₁ ⊗ₘ η.inv.app F₂)) ∧
      Nonempty ((e.functor ⋙ ObjectProperty.ι _).obj (𝟙_ _) ≅ 𝟙_ (Rep.{u + 1} Λ G)) := by
  obtain ⟨G, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup s
  exact ⟨G, exists_equivalence_isFiniteLocallyConstantSheaf_tensor_of_isFundamentalGroup Y s Λ G⟩

end AlgebraicGeometry
