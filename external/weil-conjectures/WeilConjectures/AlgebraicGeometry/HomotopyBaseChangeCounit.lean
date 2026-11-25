/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HomotopyPullbackSquareLocalization
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Localization of the canonical homotopy pullback square

Source: Stacks Project, Tags 0D5S and 0DVC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem map_counit
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    [Limits.HasBinaryBiproducts C₁] [Limits.HasBinaryBiproducts C₂]
    [Limits.HasBinaryBiproducts C₃] [Limits.HasBinaryBiproducts C₄]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
    (a : L ⊣ R) (a' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ G') (b : R ⋙ G ⟶ G' ⋙ R')
    (hb : ∀ F, e.hom.app (R.obj F) ≫ G'.map (a.counit.app F) =
      L'.map (b.app F) ≫ a'.counit.app (G'.obj F))
    (D : HomotopyCategory C₁ (.up ℤ)) :
    ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ G')) (.up ℤ)).inv).app
        ((R.mapHomotopyCategory (.up ℤ)).obj D) ≫
      (G'.mapHomotopyCategory (.up ℤ)).map
        ((a.mapHomotopyCategory (.up ℤ)).counit.app D) =
    ((a'.mapHomotopyCategory (.up ℤ)).homEquiv _ _).symm
      (((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory b (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G' ⋙ R')) (.up ℤ)).inv).app D) := by
  rw [Adjunction.homEquiv_counit]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective D
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  simp only [NatTrans.comp_app]
  let Q := HomotopyCategory.quotient C₃ (.up ℤ)
  change (Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ G'))
      (.up ℤ)).inv.app ((R.mapHomologicalComplex (.up ℤ)).obj K))) ≫
    Q.map ((G'.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) =
    Q.map ((L'.mapHomologicalComplex (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex b (.up ℤ)).app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ R')) (.up ℤ)).inv.app K)) ≫
    Q.map ((a'.mapHomologicalComplex (.up ℤ)).counit.app
      ((G'.mapHomologicalComplex (.up ℤ)).obj K))
  rw [← Q.map_comp, ← Q.map_comp, ← Q.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_comp, Category.assoc]
  change e.hom.app (R.obj (K.X n)) ≫ 𝟙 _ ≫ G'.map (a.counit.app (K.X n)) =
    L'.map (𝟙 _) ≫ L'.map (b.app (K.X n)) ≫ L'.map (𝟙 _) ≫
      a'.counit.app (G'.obj (K.X n))
  rw [L'.map_id, L'.map_id]
  simpa only [Category.id_comp] using hb (K.X n)


private noncomputable abbrev adj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)

private noncomputable def compIso {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) :=
  (conjugateIsoEquiv (adj (k ≫ l)) ((adj l).comp (adj k))).symm
    (Scheme.Modules.pushforwardComp k l).symm

private noncomputable def ordinarySquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :=
  compIso f' g ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback h.symm) ≪≫
    (compIso p f).symm

private theorem equality_mate {A B : Scheme.{u}} (k l : A ⟶ B) (e : k = l) :
    (conjugateEquiv (adj k) (adj l)).symm
      (Scheme.Modules.pushforwardCongr e).hom =
        eqToHom (congrArg Scheme.Modules.tensorPullback e.symm) := by
  subst l
  have he : (Scheme.Modules.pushforwardCongr (rfl : k = k)).hom =
      𝟙 (Scheme.Modules.pushforward k) := by
    ext M U
    simp
  rw [he]
  simp

private theorem ordinarySquare_mate {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (conjugateEquiv ((adj f).comp (adj p)) ((adj g).comp (adj f'))).symm
      ((Scheme.Modules.pushforwardComp p f).hom ≫
        (Scheme.Modules.pushforwardCongr h).hom ≫
        (Scheme.Modules.pushforwardComp f' g).inv) = (ordinarySquare f f' g p h).hom := by
  rw [← conjugateEquiv_symm_comp _ (adj (p ≫ f))]
  rw [← conjugateEquiv_symm_comp _ (adj (f' ≫ g))]
  rw [equality_mate]
  simp [ordinarySquare, compIso, conjugateIsoEquiv_symm_apply_hom,
    conjugateIsoEquiv_symm_apply_inv, Category.assoc]

private theorem ordinary_counit {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (F : X.Modules) :
    (ordinarySquare f f' g p h).hom.app ((Scheme.Modules.pushforward f).obj F) ≫
      (Scheme.Modules.tensorPullback p).map ((adj f).counit.app F) =
    (Scheme.Modules.tensorPullback f').map
      (Scheme.Modules.moduleBaseChangeMap f f' g p h F) ≫
        (adj f').counit.app ((Scheme.Modules.tensorPullback p).obj F) := by
  let r : TwoSquare (Scheme.Modules.pushforward p) (Scheme.Modules.pushforward f')
      (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g) :=
    TwoSquare.mk _ _ _ _ ((Scheme.Modules.pushforwardComp p f).hom ≫
      (Scheme.Modules.pushforwardCongr h).hom ≫ (Scheme.Modules.pushforwardComp f' g).inv)
  let b := (mateEquiv (adj p) (adj g)).symm r
  have hb : b.app F = Scheme.Modules.moduleBaseChangeMap f f' g p h F := by
    apply ((adj g).homEquiv _ _).injective
    dsimp only [adj, Functor.comp_obj]
    rw [Scheme.Modules.moduleBaseChangeMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm (adj p) (adj g) r F).symm
  have he : ((mateEquiv (adj f) (adj f')).symm b) =
      (ordinarySquare f f' g p h).hom := by
    dsimp only [b]
    rw [iterated_mateEquiv_conjugateEquiv_symm]
    exact ordinarySquare_mate f f' g p h
  have hc := mateEquiv_counit_symm (adj f) (adj f') b F
  rw [hb] at hc
  change _ = ((mateEquiv (adj f) (adj f')).symm b).app
    ((Scheme.Modules.pushforward f).obj F) ≫ _ at hc
  rw [he] at hc
  exact hc.symm

private theorem homotopySquare_eq {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    moduleHomotopyPullbackSquare f f' g p h =
      (Functor.mapHomotopyCategoryCompIso (ordinarySquare f f' g p h) (.up ℤ)).hom ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.tensorPullback f ⋙ Scheme.Modules.tensorPullback p)) (.up ℤ)).inv := by
  rfl


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary exchange is the mate of the canonical pullback square on homotopy
categories, expressed by its counit transpose.
Source: Stacks Project, Tag 08HY, the two descriptions of the base-change map.
(blueprint: lem-pc-homotopy-base-change-counit).

Proof: On modules, let k be the f' adjoint of the pullback square at f_*D
followed by p* of the f counit. Apply the g Hom equivalence to k: its expression
starts with the unit of the composite adjunction (g,f'), followed by the image
of the pullback square and the image of p* of the f counit. The conjugate unit
identity for the square replaces the first two factors by the unit of the
composite adjunction (f,p), followed by the right-adjoint square comparison.
Naturality of that comparison moves p* of the f counit to its left. Naturality
of the p unit then moves the f counit across that unit. The right triangle
identity for f cancels its unit followed by f_* of its counit. The remaining
map is f_* of the p unit followed by pushforwardComp(p,f), the equality transport
of the square and the inverse pushforwardComp(f',g): precisely the g adjoint
used to define moduleBaseChangeMap. Injectivity of the g Hom equivalence identifies
k with that map; transposing under f' gives the desired ordinary counit formula.
Apply this equality degreewise to complexes. The mapped composition
identifications and adjunction counits descend through the homotopy quotient;
every homotopy object is the quotient of a complex. This gives the displayed
identity. The proof uses only adjunction identities, so no cartesian, flatness,
acyclicity, or nonempty-scheme hypothesis is necessary. -/
theorem moduleHomotopyBaseChange_counit
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (D : HomotopyCategory X.Modules (.up ℤ)) :
    let af := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory (.up ℤ)
    let af' := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f')).mapHomotopyCategory (.up ℤ)
    let b :=
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory
        { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
          naturality := fun _ _ a ↦
            Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
        (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f'))
        (ComplexShape.up ℤ)).inv
    (moduleHomotopyPullbackSquare f f' g p h).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj D) ≫
      ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map
        (af.counit.app D) = (af'.homEquiv _ _).symm (b.app D) := by
  dsimp only
  rw [homotopySquare_eq]
  have hD := map_counit (C₁ := X.Modules) (C₂ := S.Modules)
    (C₃ := X'.Modules) (C₄ := S'.Modules)
    (L := Scheme.Modules.tensorPullback f) (R := Scheme.Modules.pushforward f)
    (L' := Scheme.Modules.tensorPullback f') (R' := Scheme.Modules.pushforward f')
    (G := Scheme.Modules.tensorPullback g) (G' := Scheme.Modules.tensorPullback p)
    (adj f) (adj f') (ordinarySquare f f' g p h)
    { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
      naturality := fun _ _ a ↦
        Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
    (ordinary_counit f f' g p h) D
  exact hD

end
end AlgebraicGeometry
