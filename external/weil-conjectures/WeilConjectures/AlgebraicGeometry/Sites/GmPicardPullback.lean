/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GmConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.GmTransport
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.Sites.TorsorPullback

/-!
# Naturality of `Pic = H¹(-, 𝔾ₘ)` under pullback

Let `g : X ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module. For an étale
`Y`-scheme `V`, pulling back a trivialisation `V^* 𝒪_Y ≅ V^* L` along the first projection
`V ×_Y X ⟶ V` gives a trivialisation of `g^* L` over the étale `X`-scheme `V ×_Y X`
(`AlgebraicGeometry.Scheme.Modules.presheafHomPullback`). These maps are natural in `V` and
equivariant along `𝔾ₘ ⟶ g_* 𝔾ₘ`, so the torsor `Isom(𝒪_X, g^* L)` is obtained from
`Isom(𝒪_Y, L)` by pullback along `g`. Hence under the identification `Pic = H¹(-, 𝔾ₘ)` the
pullback map `H¹(Y, 𝔾ₘ) ⟶ H¹(X, 𝔾ₘ)` is the pullback of line bundles
(`AlgebraicGeometry.Scheme.gmCohomologyMap_toCohomologicalPicardGroup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- For an étale `Y`-scheme `V`, the first projection `V ×_Y X ⟶ V`, as a morphism of schemes
over `Y`. -/
noncomputable def etalePullbackFst (V : Y.Etale) :
    (Over.map g).obj ((toProEt X ⋙ ProEt.forget X).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) ⟶
      (toProEt Y ⋙ ProEt.forget Y).obj V :=
  Over.homMk (pullback.fst V.hom g) pullback.condition

@[simp]
lemma etalePullbackFst_left (V : Y.Etale) :
    (etalePullbackFst g V).left = pullback.fst V.hom g :=
  rfl

/-- The first projections `V ×_Y X ⟶ V` are natural in the étale `Y`-scheme `V`. -/
lemma etalePullbackFst_naturality {U V : Y.Etale} (f : V ⟶ U) :
    (Over.map g).map ((toProEt X ⋙ ProEt.forget X).map
        ((MorphismProperty.Over.pullback @Etale ⊤ g).map f)) ≫ etalePullbackFst g U =
      etalePullbackFst g V ≫ (toProEt Y ⋙ ProEt.forget Y).map f := by
  ext
  exact Hom.etale_map_left_comp_fst g f

/-- For an étale `Y`-scheme `V`, a morphism `V^* 𝒪_Y ⟶ V^* M` gives a morphism
`(V ×_Y X)^* 𝒪_X ⟶ (V ×_Y X)^* (g^* M)`, by pullback along the first projection
`V ×_Y X ⟶ V` and the identification `g^* 𝒪_Y ≅ 𝒪_X`. -/
noncomputable def presheafHomPullback (M : modulesPseudofunctor.obj (.mk (op Y))) (V : Y.Etale)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj
      (op ((toProEt Y ⋙ ProEt.forget Y).obj V))) :
    (modulesPseudofunctor.presheafHom (unitObj X)
      ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M)).obj
        (op ((toProEt X ⋙ ProEt.forget X).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))) :=
  presheafHomRestrict g M _
    ((modulesPseudofunctor.presheafHom (unitObj Y) M).map (etalePullbackFst g V).op x)

instance isIso_presheafHomPullback (M : modulesPseudofunctor.obj (.mk (op Y))) (V : Y.Etale)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj
      (op ((toProEt Y ⋙ ProEt.forget Y).obj V))) [IsIso x] :
    IsIso (presheafHomPullback g M V x) := by
  rw [presheafHomPullback]
  infer_instance

-- the defeq checks through the pseudofunctor of modules are slow
/-- `AlgebraicGeometry.Scheme.Modules.presheafHomPullback` is natural in the étale
`Y`-scheme `V`. -/
lemma presheafHomPullback_naturality (M : modulesPseudofunctor.obj (.mk (op Y)))
    {U V : Y.Etale} (f : V ⟶ U)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj
      (op ((toProEt Y ⋙ ProEt.forget Y).obj U))) :
    (modulesPseudofunctor.presheafHom (unitObj X) _).map
        ((toProEt X ⋙ ProEt.forget X).map
          ((MorphismProperty.Over.pullback @Etale ⊤ g).map f)).op
        (presheafHomPullback g M U x) =
      presheafHomPullback g M V
        ((modulesPseudofunctor.presheafHom (unitObj Y) M).map
          ((toProEt Y ⋙ ProEt.forget Y).map f).op x) := by
  rw [presheafHomPullback, presheafHomPullback, ← presheafHomRestrict_naturality,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, etalePullbackFst_naturality]

/-- `AlgebraicGeometry.Scheme.Modules.presheafHomPullback` is compatible with multiplication
by functions, which are pulled back along the first projection `V ×_Y X ⟶ V`. -/
lemma presheafHomPullback_smulMor (M : modulesPseudofunctor.obj (.mk (op Y))) (V : Y.Etale)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj
      (op ((toProEt Y ⋙ ProEt.forget Y).obj V)))
    (a : Γ(V.left, ⊤)) :
    presheafHomPullback g M V (smulMor _ a ≫ x) =
      smulMor _ ((pullback.fst V.hom g).appTop a) ≫ presheafHomPullback g M V x := by
  rw [presheafHomPullback, presheafHomPullback, presheafHom_map_smulMor_comp]
  exact presheafHomRestrict_smulMor g M _ _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules Sheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The map `Isom(𝒪_Y, M)(V) → Isom(𝒪_X, g^* M)(V ×_Y X)` pulling back a trivialisation along
the first projection `V ×_Y X ⟶ V`. -/
noncomputable def etaleIsoTorsorPullback (M : modulesPseudofunctor.obj (.mk (op Y)))
    [SheafOfModules.IsInvertible.{u, u, u} (M : Y.Modules)]
    [SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M : X.Modules)]
    (V : Y.Etaleᵒᵖ) (x : (etaleIsoTorsor M).sheaf.obj.obj V) :
    (etaleIsoTorsor ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M)).sheaf.obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V.unop)) :=
  etaleIsoTorsorMk _ (presheafHomPullback g M V.unop (etaleIsoTorsorVal M (U := V) x))
    inferInstance

-- the defeq checks through the small étale and pro-étale sites are slow
/-- `AlgebraicGeometry.Scheme.Modules.etaleIsoTorsorPullback` is natural in `V`. -/
lemma etaleIsoTorsorPullback_naturality (M : modulesPseudofunctor.obj (.mk (op Y)))
    [SheafOfModules.IsInvertible.{u, u, u} (M : Y.Modules)]
    [SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M : X.Modules)]
    ⦃U V : Y.Etaleᵒᵖ⦄ (f : U ⟶ V) (x : (etaleIsoTorsor M).sheaf.obj.obj U) :
    (etaleIsoTorsor ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M)).sheaf.obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ g).map f.unop).op
        (etaleIsoTorsorPullback g M U x) =
      etaleIsoTorsorPullback g M V ((etaleIsoTorsor M).sheaf.obj.map f x) := by
  apply etaleIsoTorsorVal_injective
  exact presheafHomPullback_naturality g M f.unop (etaleIsoTorsorVal M (U := U) x)

-- the defeq checks through the small étale and pro-étale sites are slow
/-- `AlgebraicGeometry.Scheme.Modules.etaleIsoTorsorPullback` is equivariant along
`𝔾ₘ ⟶ g_* 𝔾ₘ`. -/
lemma etaleIsoTorsorPullback_vadd (M : modulesPseudofunctor.obj (.mk (op Y)))
    [SheafOfModules.IsInvertible.{u, u, u} (M : Y.Modules)]
    [SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M : X.Modules)]
    (V : Y.Etaleᵒᵖ) (a : Y.gmSheaf.obj.obj V) (x : (etaleIsoTorsor M).sheaf.obj.obj V) :
    etaleIsoTorsorPullback g M V ((etaleIsoTorsor M).vadd V a x) =
      (etaleIsoTorsor ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M)).vadd _
        ((gmSheafToLowerStarGmSheaf g).hom.app V a) (etaleIsoTorsorPullback g M V x) := by
  apply etaleIsoTorsorVal_injective
  exact presheafHomPullback_smulMor g M V.unop (etaleIsoTorsorVal M (U := V) x) _

-- the defeq checks through the small étale and pro-étale sites are slow
/-- **Pullback of `Isom(𝒪, M)`.** The class in `H¹(X, 𝔾ₘ)` of the torsor `Isom(𝒪_X, g^* M)` is
the image under the pullback map `H¹(Y, 𝔾ₘ) ⟶ H¹(X, 𝔾ₘ)` of the class of `Isom(𝒪_Y, M)`. -/
lemma classH1_etaleIsoTorsor_pullback (M : modulesPseudofunctor.obj (.mk (op Y)))
    [SheafOfModules.IsInvertible.{u, u, u} (M : Y.Modules)]
    [SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M : X.Modules)] :
    Torsor.classH1 X.gmSheaf (isTerminalEtale X)
        ⟦etaleIsoTorsor ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M)⟧ =
      gmCohomologyMap g 1 (Torsor.classH1 Y.gmSheaf (isTerminalEtale Y)
        ⟦etaleIsoTorsor M⟧) := by
  exact Etale.classH1_eq_map_cohomologyMap_of_equivariant g (gmSheafToLowerStarGmSheaf g)
    (etaleIsoTorsor M) (etaleIsoTorsor ((modulesPseudofunctor.map g.op.toLoc).toFunctor.obj M))
    (etaleIsoTorsorPullback g M) (etaleIsoTorsorPullback_naturality g M)
    (etaleIsoTorsorPullback_vadd g M)

/-- **Naturality of `Pic = H¹(-, 𝔾ₘ)` under pullback.** Under the identification
`Pic = H¹(-, 𝔾ₘ)` of `AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroup`, the pullback map
`H¹(Y, 𝔾ₘ) ⟶ H¹(X, 𝔾ₘ)`
along any morphism of schemes `g: X ⟶ Y` is the pullback of line bundles along `g`. This is used
for the naturality of the Brauer group computations under restriction and extension of the
algebraically closed ground field. -/
theorem gmCohomologyMap_toCohomologicalPicardGroup (L : Y.Pic) :
    gmCohomologyMap g 1 (Pic.toCohomologicalPicardGroup Y L) =
      Pic.toCohomologicalPicardGroup X (Pic.map g L) := by
  have := Pic.isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pullback g).obj ((fromSkeleton Y.Modules).obj L.val)) :=
    SheafOfModules.IsInvertible.pullback this
  have hL : Pic.map g L =
      Pic.mk ((Modules.pullback g).obj ((fromSkeleton Y.Modules).obj L.val)) :=
    Pic.ext rfl
  rw [Pic.toCohomologicalPicardGroup_apply, Pic.toCohomologicalPicardGroup_apply, hL,
    Pic.etaleTorsorClass_mk]
  exact (@classH1_etaleIsoTorsor_pullback _ _ g _ _ this).symm

/-- **Pullback of global units.** In degree zero, under the identification of `H⁰(-, 𝔾ₘ)` with
the sections of `𝔾ₘ` over the terminal object, the pullback map `H⁰(Y, 𝔾ₘ) ⟶ H⁰(X, 𝔾ₘ)` along
`g : X ⟶ Y` is the pullback of sections `AlgebraicGeometry.Scheme.gmSectionsPullback`, that is,
the pullback of global units (`AlgebraicGeometry.Scheme.gmSectionsPullback_gmSection`). -/
lemma equiv₀_gmCohomologyMap_zero (x : Sheaf.H Y.gmSheaf 0) :
    Sheaf.H.equiv₀ _ terminalIsTerminal (gmCohomologyMap g 0 x) =
      (gmSectionsPullback g).hom (Sheaf.H.equiv₀ _ terminalIsTerminal x) :=
  Etale.equiv₀_map_cohomologyMap g (gmSheafToLowerStarGmSheaf g) x terminalIsTerminal
    terminalIsTerminal (PreservesTerminal.iso g.Etale).inv

end AlgebraicGeometry.Scheme
