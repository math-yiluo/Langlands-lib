/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Blueprint statements

thm-galois-lc-etale.
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

section Equivalence

variable (Y : Scheme.{v})

/-- The functor `P ↦ Hom_Y(-, P)` from finite étale `Y`-schemes to finite locally constant
sheaves of sets (`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`). -/
noncomputable def FiniteEtale.toFLC : Y.FiniteEtale ⥤ Y.FiniteLocallyConstant :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1})
    fun P ↦ by
      have : IsFinite P.obj.hom := P.property
      obtain ⟨_, h⟩ := (isFiniteLocallyConstant_yoneda_and_exists_iso Y).1 _ P.obj.hom
      exact h

/-- `AlgebraicGeometry.Scheme.FiniteEtale.toFLC` is fully faithful, by the Yoneda lemma. -/
noncomputable def FiniteEtale.fullyFaithfulToFLC : (FiniteEtale.toFLC Y).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    (((ObjectProperty.fullyFaithfulι _).comp
      Y.smallEtaleTopology.fullyFaithfulUliftYoneda.{v + 1}) :
      (ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}).FullyFaithful)

/-- `AlgebraicGeometry.Scheme.FiniteEtale.toFLC` is full. -/
instance : (FiniteEtale.toFLC Y).Full := (FiniteEtale.fullyFaithfulToFLC Y).full

/-- `AlgebraicGeometry.Scheme.FiniteEtale.toFLC` is faithful. -/
instance : (FiniteEtale.toFLC Y).Faithful := (FiniteEtale.fullyFaithfulToFLC Y).faithful

/-- Every finite locally constant sheaf of sets is represented by a finite étale scheme
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`). -/
instance : (FiniteEtale.toFLC Y).EssSurj where
  mem_essImage E := by
    obtain ⟨P, π, _, _, ⟨e⟩⟩ := (isFiniteLocallyConstant_yoneda_and_exists_iso Y).2 E.obj
      E.property
    exact ⟨⟨Scheme.Etale.mk π, ‹IsFinite π›⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
      ((fullyFaithfulSheafToPresheaf _ _).preimageIso e.symm)⟩⟩

/-- `AlgebraicGeometry.Scheme.FiniteEtale.toFLC` is an equivalence. -/
instance : (FiniteEtale.toFLC Y).IsEquivalence where

variable {Y}

/-- The stalk at a geometric point `s` of the sheaf of sections of a finite étale `Y`-scheme `P` is
the geometric fibre of `P` at `s`. -/
noncomputable def FiniteEtale.toFLCCompSheafFiberIso {Ω : Type v} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) :
    FiniteEtale.toFLC Y ⋙ ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
      FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v} :=
  have : Y.smallEtaleTopology.HasSheafCompose uliftFunctor.{v + 1, v} := inferInstance
  have : Limits.PreservesFilteredColimitsOfSize.{v, v} uliftFunctor.{v + 1, v} := inferInstance
  Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.yoneda)
      ((pointSmallEtale s).sheafFiberCompIso uliftFunctor.{v + 1}) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (Functor.isoWhiskerRight Y.smallEtaleTopology.yonedaCompSheafToPresheaf
          (pointSmallEtale s).presheafFiber ≪≫
        Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm (pointSmallEtale s).presheafFiber ≪≫
        (pointSmallEtale s).shrinkYonedaCompPresheafFiberIso)) uliftFunctor.{v + 1}

/-- Base change of finite étale schemes is base change of étale schemes. -/
noncomputable def FiniteEtale.pullbackCompιIso {X : Scheme.{v}} (f : X ⟶ Y) :
    ObjectProperty.ι _ ⋙ f.Etale ≅
      FiniteEtale.pullback f ⋙ ObjectProperty.ι _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    refine EtaleTorsor.etaleHom_ext ?_
    apply Limits.pullback.hom_ext <;> simp [FiniteEtale.pullback, Hom.Etale]

/-- The inverse image of the sheaf of sections of a finite étale `Y`-scheme `P` along
`f : X ⟶ Y` is the sheaf of sections of the base change `P ×_Y X`: the inverse image is left
adjoint to the pushforward, so it sends representable sheaves to representable sheaves. -/
noncomputable def FiniteEtale.toFLCPullbackIso {X : Scheme.{v}} (f : X ⟶ Y) :
    FiniteEtale.toFLC Y ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
      FiniteEtale.pullback f ⋙ FiniteEtale.toFLC X ⋙ ObjectProperty.ι _ :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        f.Etale (Type (v + 1))
        Y.smallEtaleTopology X.smallEtaleTopology).uliftYonedaCompIso ≪≫
    Functor.isoWhiskerRight (FiniteEtale.pullbackCompιIso f) X.smallEtaleTopology.uliftYoneda

end Equivalence

/-- Blueprint: thm-galois-lc-etale. -/
theorem exists_finiteEtale_flc_equivalence (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FiniteLocallyConstant,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) := by
  refine ⟨(FiniteEtale.toFLC Y).asEquivalence, ⟨Iso.refl _⟩, fun Ω _ _ s ↦
    ⟨FiniteEtale.toFLCCompSheafFiberIso s⟩, fun X f ↦ ⟨(FiniteEtale.toFLC X).asEquivalence,
      ⟨Iso.refl _⟩, ⟨FiniteEtale.toFLCPullbackIso f⟩⟩⟩

/-- Blueprint: thm-galois-lc-etale. -/
theorem finiteEtale_flc_preserves_torsors {Y : Scheme.{v}}
    (Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant)
    (α : Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) :
    ∀ (M : Type (v + 1)) [AddCommGroup M] [Finite M] (t : EtaleTorsor M Y),
      ∃ ε : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj ≅ t.toSheafTorsor.sheaf,
        ε = α.app ⟨t.toEtale, t.isFinite⟩ ∧
        ∀ (U : Y.Etale) (m : M)
          (x : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj.obj.obj (op U)),
          ε.hom.hom.app (op U)
            ((Φ.functor.map (ObjectProperty.homMk
              (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)))).hom.hom.app (op U) x) =
            ⟨(ε.hom.hom.app (op U) x).down ≫
              MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)⟩ := by
  intro M _ _ t
  refine ⟨α.app ⟨t.toEtale, t.isFinite⟩, rfl, fun U m x ↦ ?_⟩
  exact congrArg (fun f ↦ f.hom.app (op U) x) (α.hom.naturality (ObjectProperty.homMk
    (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)) :
      (⟨t.toEtale, t.isFinite⟩ : Y.FiniteEtale) ⟶ ⟨t.toEtale, t.isFinite⟩))

end AlgebraicGeometry.Scheme
