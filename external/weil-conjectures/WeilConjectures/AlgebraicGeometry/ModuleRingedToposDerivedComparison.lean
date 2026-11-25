/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
/-! # Module-object and ringed-topos derived comparison

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(auxiliary; not a blueprint node).

## Main definitions and statements

- `ordinary_exact_flat_kflat`, `ordinary_monoidal`: the ordinary equivalence clauses.
- `derivedPullComparison`, `derivedPushComparison`, `derived_homEquiv`: derived operations.
- `tensorPullComparison`, `delta_comparison`, `mu_comparison`: specified tensor maps.
- `composition_comparison`, `projection_comparison`: composition and the proper mate.
- `open_homEquiv`, `openProjection_comparison`: open adjunction and its unit mate.

-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private def curryComparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D × D ⥤ D)
    (t : Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ S) :
    (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (Functor.curry.obj S) where
  app M :=
    { app := fun N ↦ t.app (M, N)
      naturality := by
        intro N N' f
        simpa using t.naturality (Prod.mkHom (𝟙 M) f) }
  naturality := by
    intro M M' f
    ext N
    simpa using t.naturality (Prod.mkHom f (𝟙 N))

private theorem tensorSquare_right
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {A B V W X X' Y Y' : C} (p : X ≅ X') (q : Y ≅ Y') (r : A ≅ B)
    (a : A ⟶ V) (b : V ⟶ T.obj (X, Y))
    (c : B ⟶ W) (d : W ⟶ T.obj (X', Y'))
    (h : a ≫ b ≫ T.map (Prod.mkHom p.hom q.hom) = r.hom ≫ c ≫ d) :
    c ≫ d ≫ T.map (Prod.mkHom p.inv (𝟙 Y')) ≫
        T.map (Prod.mkHom (𝟙 X) q.inv) = r.inv ≫ a ≫ b := by
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [← cancel_epi r.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [← T.map_comp, prod_comp, Iso.hom_inv_id, ← prod_id,
    T.map_id, Category.comp_id]

private theorem mapIso_cancel_left {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z : D}
    (b : F.obj Y ⟶ Z) (c : F.obj X ⟶ Z) (h : b = F.map e.inv ≫ c) :
    F.map e.hom ≫ b = c := by
  rw [h, ← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

private theorem projection_comparison_of_squares
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (F : C₂ ⥤ C₁) (G : C₁ ⥤ C₂) (adj : F ⊣ G)
    (F' : D₂ ⥤ D₁) (G' : D₁ ⥤ D₂) (adj' : F' ⊣ G')
    (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (S₁ : D₁ × D₁ ⥤ D₁) (S₂ : D₂ × D₂ ⥤ D₂)
    (p : F ⋙ E₁ ≅ E₂ ⋙ F') (q : G ⋙ E₂ ≅ E₁ ⋙ G')
    (c₁ : Functor.uncurry.obj T₁ ⋙ E₁ ≅ E₁.prod E₁ ⋙ S₁)
    (c₂ : Functor.uncurry.obj T₂ ⋙ E₂ ≅ E₂.prod E₂ ⋙ S₂)
    (δ : (Functor.postcompose₂.obj F).obj T₂ ⟶
      (((Functor.whiskeringLeft₂ C₁).obj F).obj F).obj T₁)
    (δ' : S₂ ⋙ F' ≅ F'.prod F' ⋙ S₁)
    (hδ : ∀ M N,
      E₁.map ((δ.app M).app N) ≫ c₁.hom.app (F.obj M, F.obj N) ≫
          S₁.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app ((T₂.obj M).obj N) ≫ F'.map (c₂.hom.app (M, N)) ≫
          δ'.hom.app (E₂.obj M, E₂.obj N))
    (hCounit : ∀ A, adj'.counit.app (E₁.obj A) =
      F'.map (q.inv.app A) ≫ p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A))
    (K : C₁) (L : C₂) :
    E₂.map (adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L))) ≫
        q.hom.app ((T₁.obj K).obj (F.obj L)) ≫
        G'.map (c₁.hom.app (K, F.obj L)) ≫
        G'.map (S₁.map (Prod.mkHom (𝟙 (E₁.obj K)) (p.hom.app L))) =
      c₂.hom.app (G.obj K, L) ≫
        S₂.map (Prod.mkHom (q.hom.app K) (𝟙 (E₂.obj L))) ≫
        derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K) (E₂.obj L) := by
  let d := Functor.curry.map δ'.hom ≫
    (Functor.curryObjProdComp F' F'
      S₁).hom
  let tX := curryComparison E₁
    T₁ S₁
    c₁.hom
  let tY := curryComparison E₂
    T₂ S₂
    c₂.hom
  have hs : ∀ M N,
      F'.map ((tY.app M).app N) ≫
        (d.app (E₂.obj M)).app
          (E₂.obj N) ≫
        ((Functor.curry.obj S₁).map
          (p.inv.app M)).app _ ≫
        ((Functor.curry.obj S₁).obj _).map
          (p.inv.app N) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        (tX.app _).app _ := by
    intro M N
    change F'.map
        (c₂.hom.app (M, N)) ≫
      (δ'.hom.app
        (E₂.obj M,
          E₂.obj N) ≫ 𝟙 _) ≫
      S₁.map (Prod.mkHom (p.inv.app M) (𝟙 _)) ≫
      S₁.map (Prod.mkHom (𝟙 _) (p.inv.app N)) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        c₁.hom.app
          (F.obj M, F.obj N)
    simp only [Category.comp_id]
    exact tensorSquare_right S₁
      (p.app M) (p.app N)
      (p.app
        ((T₂.obj M).obj N))
      (E₁.map ((δ.app M).app N))
      (c₁.hom.app
        (F.obj M, F.obj N))
      (F'.map (c₂.hom.app (M, N)))
      (δ'.hom.app
        (E₂.obj M, E₂.obj N))
      (hδ M N)
  have hc (A : C₁) :
      F'.map (q.hom.app A) ≫ adj'.counit.app (E₁.obj A) =
        p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A) :=
    mapIso_cancel_left F' (q.app A) _ _ (hCounit A)
  have h := Adjunction.rightAdjointProjectionMap_mate
    adj adj'
    (T₂ := Functor.curry.obj S₁) (S₂ := Functor.curry.obj S₂)
    (U := E₂) (V := E₁)
    δ d tY tX p.inv
    q.hom hs hc K L
  have hh := congrArg (fun q ↦ q ≫ G'.map
    (S₁.map (Prod.mkHom (𝟙 (E₁.obj K))
      (p.hom.app L)))) h
  dsimp only [tX, tY, curryComparison] at hh
  change (E₂.map ((adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L)))) ≫
      q.hom.app _ ≫
      G'.map (c₁.hom.app
        (K, F.obj L))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) =
    (c₂.hom.app (G.obj K, L) ≫
      S₂.map (Prod.mkHom (q.hom.app K) (𝟙 _)) ≫
      derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K)
        (E₂.obj L) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.inv.app L)))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) at hh
  simp only [Category.assoc, ← G'.map_comp,
    ← S₁.map_comp, prod_comp, Category.id_comp, Iso.inv_hom_id_app,
    ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at hh
  simpa only [Functor.id_obj, G'.map_comp] using hh

private theorem third_conjunct {P Q R S : Prop} (h : P ∧ Q ∧ R ∧ S) : R :=
  h.2.2.1

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Comparing the two normalized monoidal witnesses elaborates the sheaf tensor constraints.
/-- The chosen ordinary tensor maps obey all symmetric-monoidal coherence diagrams.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: these are exactly the maps chosen from internal_section_tensor_comparison,
whose proof checks the naturality, associator, unitors and symmetry on local pure
tensors. The regular-unit comparison fixes local scalars, so the unit diagrams
are the scalar action laws. Local generation extends each equality to the sheaf. -/
theorem ordinary_monoidal (X : Scheme.{u}) :
    (∀ (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N'),
      (equivalence Λ X).functor.map (f ⊗ₘ g) ≫
          (ordinaryTensorComparison Λ X M' N').hom =
        (ordinaryTensorComparison Λ X M N).hom ≫
          ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g)) ∧
    (∀ M N P : internalModules Λ X,
      (ordinaryTensorComparison Λ X (M ⊗ N) P).hom ≫
          (ordinaryTensorComparison Λ X M N).hom ▷ (equivalence Λ X).functor.obj P ≫
          (α_ _ _ _).hom =
        (equivalence Λ X).functor.map (α_ M N P).hom ≫
          (ordinaryTensorComparison Λ X M (N ⊗ P)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryTensorComparison Λ X N P).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X (𝟙_ _) M).hom ≫
          (ordinaryUnitComparison Λ X).hom ▷ (equivalence Λ X).functor.obj M ≫
          (λ_ _).hom = (equivalence Λ X).functor.map (λ_ M).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X M (𝟙_ _)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryUnitComparison Λ X).hom ≫
          (ρ_ _).hom = (equivalence Λ X).functor.map (ρ_ M).hom) ∧
    (∀ M N : internalModules Λ X,
      (ordinaryTensorComparison Λ X M N).hom ≫ (β_ _ _).hom =
        (equivalence Λ X).functor.map (β_ M N).hom ≫
          (ordinaryTensorComparison Λ X N M).hom) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  refine Exists.elim h.2 (fun e h₁ ↦ ?_)
  refine Exists.elim h₁ (fun e₀ hs ↦ ?_)
  have he : e = ordinaryTensorComparison Λ X := by
    funext M N
    exact (ordinaryTensorComparison_existsUnique Λ X M N).unique (hs.1 M N)
      (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec
  have he₀ : e₀ = ordinaryUnitComparison Λ X :=
    (ordinaryUnitComparison_existsUnique Λ X).unique hs.2.1
      (ordinaryUnitComparison_existsUnique Λ X).exists.choose_spec
  have hc := And.intro hs.2.2.1 (And.intro hs.2.2.2.1
    (And.intro hs.2.2.2.2.1 (And.intro hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1)))
  simp only [← he, ← he₀, equivalence] at hc ⊢
  -- The kernel checks this existing proof directly; elaborator conversion unfolds the
  -- large sheaf associator a second time and exceeds the single-file compilation limit.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hc
      | Lean.throwError "missing coherence proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The actual module-object proper projection arrow, the adjoint of counit after delta.
Source: Stacks 0B56 (auxiliary; not a blueprint node). -/
def internalProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ Y).obj ((internalDerivedPushforward Λ f).obj K)).obj L ⟶
      (internalDerivedPushforward Λ f).obj
        (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((internalDelta Λ f).app ((internalDerivedPushforward Λ f).obj K)).app L ≫
      (((CondensedRing.derivedTensor Λ X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app K)).app
          ((internalDerivedPullback Λ f).obj L)))

/-- The precise ringed projection mate alpha, in the dependency's uncurried interface.
Source: Stacks 0B56 (auxiliary; not a blueprint node). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) (L : DerivedCategory (modules Λ Y)) :
    (tensor Λ Y).obj ((derivedPushforward Λ f).obj K, L) ⟶
      (derivedPushforward Λ f).obj ((tensor Λ X).obj (K, (derivedPullback Λ f).obj L)) :=
  derivedProjectionFormulaMate (derivedPullback Λ f) (derivedPushforward Λ f)
    (derivedAdjunction Λ f) (tensor Λ Y) (tensor Λ X) (tensorPullComparison Λ f) K L

/-- Equality of the actual oplax tensor natural transformations under comparison.
Inverting this equation identifies the actual lax maps as well.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the normalized underived maps both send s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). Apply this equality to flat-term K-flat
representatives and totalize with the same signs. The representative square in
tensorPullComparison_existsUnique and uniqueness of two-variable derived tensor
in lem-weil-pbc-site-derived-tensor-descent give the equation on every pair. -/
theorem delta_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) := by
  exact third_conjunct (section_derived_tensor_normalization Λ f) M N

-- The comparison instances contain large sheaf tensor constraints.
/-- The module-object proper projection is the precise ringed projection mate alpha.
This statement makes no invertibility assertion about the projection arrow.
Source: Stacks 0B56 (auxiliary; not a blueprint node).
Proof: derived_homEquiv identifies the specified Hom bijection and counit, and
delta_comparison identifies its tensor arrow. Their composite therefore has the
same adjoint transpose, which is exactly derivedProjectionFormulaMate used in
ringedProjectionMateExact. Naturality and unit normalization follow from the same
identifications and the adjunction triangle identities. -/
theorem projection_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
          (K, (internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ X).functor.obj K))
          ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app
          ((internalDerivedPushforward Λ f).obj K, L) ≫
        (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K)
          (𝟙 ((derivedEquivalence Λ Y).functor.obj L))) ≫
        projection Λ f ((derivedEquivalence Λ X).functor.obj K)
          ((derivedEquivalence Λ Y).functor.obj L) := by
  exact projection_comparison_of_squares
    (internalDerivedPullback Λ f) (internalDerivedPushforward Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (derivedPullback Λ f) (derivedPushforward Λ f) (derivedAdjunction Λ f)
    (derivedEquivalence Λ X).functor (derivedEquivalence Λ Y).functor
    (CondensedRing.derivedTensor Λ X) (CondensedRing.derivedTensor Λ Y)
    (tensor Λ X) (tensor Λ Y) (derivedPullComparison Λ f) (derivedPushComparison Λ f)
    (tensorComparison Λ X) (tensorComparison Λ Y) (internalDelta Λ f)
    (tensorPullComparison Λ f) (delta_comparison Λ f)
    ((sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.2.1) K L

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
