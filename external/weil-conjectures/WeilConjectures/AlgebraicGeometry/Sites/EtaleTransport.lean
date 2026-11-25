/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.CategoryTheory.Sites.ModuleCohomologyExt

/-!
# Restriction of étale cohomology and torsors along an étale monomorphism

Let `f : X ⟶ Y` be an étale monomorphism of schemes, for instance an isomorphism. Restriction
along the localization functor `Φ : X.Etale ⥤ Y.Etale`, `U ↦ (U ⟶ X ⟶ Y)`, is an exact functor
`R : Sh(Y_ét) ⥤ Sh(X_ét)` with `(R F)(U) = F(Φ U)`
(`AlgebraicGeometry.Scheme.etaleRestriction`). It induces maps `H^n(Y, F) ⟶ H^n(X, R F)` on
étale cohomology
(`AlgebraicGeometry.Scheme.etaleRestrictionH`), natural in `F`, compatible with connecting
homomorphisms and given in degree `0` by restriction of global sections. Restricting the
underlying sheaf of a `G`-torsor gives an `R G`-torsor
(`CategoryTheory.Sheaf.Torsor.restrict`), and the class of the restricted torsor in
`H¹(X, R G)` is the image of the class of the torsor
(`AlgebraicGeometry.Scheme.classH1_etaleRestriction`).

For an isomorphism `e : X ≅ Y` this is the transport of étale cohomology and torsors along `e`,
used to show that cup products and Kummer maps are invariant under automorphisms such as the
Frobenius of the geometric fibre of a curve over a finite field.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleRestriction`: the restriction functor `R`.
- `AlgebraicGeometry.Scheme.etaleRestrictionH`: the induced map on cohomology.

## Main statements

- `AlgebraicGeometry.Scheme.etaleRestrictionH_map`, `etaleRestrictionH_δSucc`,
  `equiv₀_etaleRestrictionH`: naturality, connecting homomorphisms, degree `0`.
- `AlgebraicGeometry.Scheme.classH1_etaleRestriction`: compatibility with classes of torsors.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  {T : C} (hT : IsTerminal T)

lemma H.equiv₀_eq_constantHomEquiv (F : Sheaf J AddCommGrpCat.{u}) [HasExt.{u} (Sheaf J
    AddCommGrpCat.{u})] (x : H F 0) :
    H.equiv₀ F hT x = constantHomEquiv hT F (Ext.addEquiv₀ x) :=
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- The localization functor `X.Etale ⥤ Y.Etale`, `U ↦ (U ⟶ X ⟶ Y)`, along an étale `f`. -/
noncomputable abbrev etaleLocalization : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ ‹Etale f›

instance : (etaleLocalization f).IsContinuous (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) :=
  isContinuous_overMap ‹Etale f› le_rfl

instance : (etaleLocalization f).IsCocontinuous (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) :=
  isCocontinuous_overMap ‹Etale f› le_rfl

/-- The restriction `R : Sh(Y_ét) ⥤ Sh(X_ét)` along an étale morphism `f : X ⟶ Y`:
`(R F)(U) = F(U ⟶ X ⟶ Y)`. For `f` étale it is the pullback `f^*`
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`). -/
noncomputable abbrev etaleRestriction :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.localizationRestriction AddCommGrpCat.{u + 1} f ‹_›

instance : (etaleRestriction f).Additive where
  map_add := rfl

instance : (etaleRestriction f).IsLeftAdjoint :=
  (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f ‹_›).isLeftAdjoint

instance [Mono f] : PreservesFiniteLimits (etaleRestriction f) :=
  inferInstance

instance : PreservesFiniteColimits (etaleRestriction f) :=
  inferInstance

/-- The localization `X ⟶ Y` of the terminal object `𝟙 : X ⟶ X` of `X.Etale`. -/
noncomputable abbrev etaleRestrictionTop : Y.Etale :=
  (etaleLocalization f).obj (MorphismProperty.Over.mk ⊤ (𝟙 X)
    (MorphismProperty.id_mem _ X))

/-- The terminal object `𝟙 : X ⟶ X` of the small étale site. -/
noncomputable abbrev isTerminalEtale (X : Scheme.{u}) :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @Etale X)) :=
  MorphismProperty.Over.mkIdTerminal @Etale X


/-- The comparison `ℤ_X ⟶ R ℤ_Y` of constant sheaves sending `1` to the restriction of `1`. -/
noncomputable def constantSheafToEtaleRestriction :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (etaleRestriction f).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) :=
  (Sheaf.constantHomEquiv (isTerminalEtale X) _).symm
    (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))).obj.map ((isTerminalEtale Y).from (etaleRestrictionTop f)).op
        (Sheaf.constantHomEquiv (isTerminalEtale Y) _ (𝟙 _)))

/-- The map `H^n(Y, F) ⟶ H^n(X, R F)` induced by the restriction along an étale monomorphism:
push an `Ext`-class forward along the exact functor `R` and precompose with the comparison
`ℤ_X ⟶ R ℤ_Y` of constant sheaves. -/
noncomputable def etaleRestrictionH [Mono f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((etaleRestriction f).obj F) n :=
  ((Ext.mk₀ (constantSheafToEtaleRestriction f)).precomp _ (zero_add n)).comp
    ((etaleRestriction f).mapExtAddHom _ F n)

variable [Mono f]

lemma etaleRestrictionH_apply (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H F n) :
    etaleRestrictionH f F n x = (Ext.mk₀ (constantSheafToEtaleRestriction f)).comp
      (x.mapExactFunctor (etaleRestriction f)) (zero_add n) :=
  rfl

/-- The map on cohomology is natural in the sheaf. -/
lemma etaleRestrictionH_map {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ F') (n : ℕ) (x : Sheaf.H F n) :
    etaleRestrictionH f F' n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((etaleRestriction f).map φ) n (etaleRestrictionH f F n x) := by
  simp only [etaleRestrictionH_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

/-- The map on cohomology commutes with the connecting homomorphisms. -/
lemma etaleRestrictionH_δSucc {S : ShortComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H S.X₃ n) :
    etaleRestrictionH f S.X₁ (n + 1) (Sheaf.H.δSucc hS n x) =
      Sheaf.H.δSucc (hS.map_of_exact (etaleRestriction f)) n
        (etaleRestrictionH f S.X₃ n x) := by
  simp only [etaleRestrictionH_apply, Sheaf.H.δSucc_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- In degree `0` the map on cohomology is the restriction of global sections along
`(X ⟶ Y) ⟶ (Y ⟶ Y)`. -/
lemma equiv₀_etaleRestrictionH (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ _ (isTerminalEtale X) (etaleRestrictionH f F 0 x) =
      F.obj.map ((isTerminalEtale Y).from (etaleRestrictionTop f)).op
        (Sheaf.H.equiv₀ F (isTerminalEtale Y) x) := by
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [etaleRestrictionH_apply, Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀, Sheaf.H.equiv₀_eq_constantHomEquiv, Sheaf.H.equiv₀_eq_constantHomEquiv]
  erw [Ext.addEquiv₀.apply_symm_apply, Ext.addEquiv₀.apply_symm_apply]
  rw [Sheaf.constantHomEquiv_comp, constantSheafToEtaleRestriction, Equiv.apply_symm_apply]
  exact Sheaf.constantHomEquiv_naturality (isTerminalEtale Y) g _

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf.Torsor

open AlgebraicGeometry Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- The restriction of a `G`-torsor along an étale morphism `f : X ⟶ Y`, an `R G`-torsor:
its sections over `U` are those of the torsor over `U ⟶ X ⟶ Y`. -/
noncomputable def restrict (P : Torsor G) : Torsor ((etaleRestriction f).obj G) where
  sheaf := ((etaleLocalization f).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)).obj P.sheaf
  vadd U a x := P.vadd (op ((etaleLocalization f).obj U.unop)) a x
  zero_vadd U x := P.zero_vadd _ x
  add_vadd U a b x := P.add_vadd _ a b x
  map_vadd g a x := P.map_vadd _ a x
  bijective_vadd U x := P.bijective_vadd _ x
  nonemptySieve_mem U := by
    refine X.smallEtaleTopology.superset_covering ?_
      ((etaleLocalization f).cover_lift (X.smallGrothendieckTopology @Etale)
        (Y.smallGrothendieckTopology @Etale) (P.nonemptySieve_mem _))
    intro V g hg
    exact hg

lemma restrict_vadd (P : Torsor G) (U : X.Etaleᵒᵖ) (a : G.obj.obj
    (op ((etaleLocalization f).obj U.unop))) (x) :
    (P.restrict f).vadd U a x =
      P.vadd (op ((etaleLocalization f).obj U.unop)) a x :=
  rfl


/-- The sections of the restriction of a torsor over `U` are its sections over the
localization of `U`. -/
def restrictSheafEquiv (P : Torsor G) (U : X.Etaleᵒᵖ) :
    (P.restrict f).sheaf.obj.obj U ≃ P.sheaf.obj.obj (op ((etaleLocalization f).obj U.unop)) :=
  Equiv.refl _

lemma restrictSheafEquiv_map (P : Torsor G) {U V : X.Etaleᵒᵖ} (g : U ⟶ V)
    (x : (P.restrict f).sheaf.obj.obj U) :
    P.restrictSheafEquiv f V ((P.restrict f).sheaf.obj.map g x) =
      P.sheaf.obj.map ((etaleLocalization f).map g.unop).op (P.restrictSheafEquiv f U x) :=
  rfl

lemma restrictSheafEquiv_vadd (P : Torsor G) (U : X.Etaleᵒᵖ)
    (a : G.obj.obj (op ((etaleLocalization f).obj U.unop))) (x : (P.restrict f).sheaf.obj.obj U) :
    P.restrictSheafEquiv f U ((P.restrict f).vadd U a x) =
      P.vadd (op ((etaleLocalization f).obj U.unop)) a (P.restrictSheafEquiv f U x) :=
  rfl


/-- Restriction preserves isomorphism of torsors. -/
lemma restrict_equiv {P P' : Torsor G} (h : P ≈ P') :
    P.restrict f ≈ P'.restrict f := by
  obtain ⟨e⟩ := h
  exact ⟨Iso.ofHom (((etaleLocalization f).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)).map e.iso.hom)
    fun U a x ↦ e.map_vadd _ a x⟩

end CategoryTheory.Sheaf.Torsor

namespace AlgebraicGeometry.Scheme

open Sheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [Mono f]

/-- The restriction of a lifting torsor is a lifting torsor. -/
lemma etaleRestriction_lifts_equiv {G I Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0} (hS : (ShortComplex.mk ι d w).ShortExact)
    (s : Q.obj.obj (op _)) :
    (Torsor.lifts (isTerminalEtale Y) hS s).restrict f ≈
      Torsor.lifts (isTerminalEtale X) (hS.map_of_exact (etaleRestriction f))
        (Q.obj.map ((isTerminalEtale Y).from (etaleRestrictionTop f)).op s) := by
  set P := Torsor.lifts (isTerminalEtale Y) hS s
  refine ⟨Torsor.Iso.ofHom ⟨{ app U := ↾fun x ↦ ⟨(x : P.sheaf.obj.obj
    (op ((etaleLocalization f).obj U.unop))).1, ?_⟩, naturality U V g := rfl }⟩ fun U a x ↦ rfl⟩
  have hx : d.hom.app _ (x : P.sheaf.obj.obj (op ((etaleLocalization f).obj U.unop))).1 = _ :=
    x.2
  change d.hom.app _ (x : P.sheaf.obj.obj (op ((etaleLocalization f).obj U.unop))).1 =
    Q.obj.map ((etaleLocalization f).map ((isTerminalEtale X).from U.unop)).op
      (Q.obj.map ((isTerminalEtale Y).from (etaleRestrictionTop f)).op s)
  rw [hx, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp]
  congr 3

/-- **Classes of restricted torsors.** The class of the restriction of a `G`-torsor `P` is the
image of the class of `P` under `H¹(Y, G) ⟶ H¹(X, R G)`. -/
theorem classH1_etaleRestriction {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Torsor G) :
    Torsor.classH1 _ (isTerminalEtale X) ⟦P.restrict f⟧ =
      etaleRestrictionH f G 1 (Torsor.classH1 G (isTerminalEtale Y) ⟦P⟧) := by
  have hS := Torsor.injectiveSequence_shortExact G
  obtain ⟨s, hs⟩ := Torsor.exists_equiv_lifts (isTerminalEtale Y) hS P
  obtain ⟨x, rfl⟩ := (H.equiv₀ _ (isTerminalEtale Y)).surjective s
  rw [_root_.Quotient.sound hs, _root_.Quotient.sound (Torsor.restrict_equiv f hs),
    _root_.Quotient.sound (etaleRestriction_lifts_equiv f hS _), Torsor.classH1_lifts,
    Torsor.classH1_lifts, ← equiv₀_etaleRestrictionH, ← H.δSucc_zero, ← H.δSucc_zero]
  exact (etaleRestrictionH_δSucc f hS 0 x).symm

end AlgebraicGeometry.Scheme
