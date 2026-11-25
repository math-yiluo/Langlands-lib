/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Unbounded localization of finite clopen module gluing

Source: Stacks Project, derived.tex, Tags 015F and 05RU, finite-clopen application
(blueprint: lem-pur-clopen-unbounded-derived-localization).

The selected module data below are the fully specified sectionwise gluing data of the
recorded dependency. No arbitrary derived equivalence replaces their normalization.
-/

@[expose] public noncomputable section

set_option linter.checkUnivs false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v w s a b c d

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.ProEt.ClopenLocalization

/-- The recorded module category in a universe containing the small site and index set.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) RingCat.{u}) :=
  ringedSiteModules.{max v w (t + 1)} R

/-- The existing Mathlib abelian structure, with both site-size witnesses explicit.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance modulesAbelian {X : Scheme.{t}} (R : Sheaf (topology X) RingCat.{u}) :
    Abelian (Modules.{t, u, v, w} R) := by
  letI := AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify.{t, max v w} X
  letI := AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective.{t, max v w} X
  exact SheafOfModules.instAbelian R

/-- The standard unbounded localization, with its full morphism universe.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance hasDerived {X : Scheme.{t}} (R : Sheaf (topology X) RingCat.{u}) :
    HasDerivedCategory.{max u (v + 1) (w + 1) (t + 2)} (Modules.{t, u, v, w} R) :=
  HasDerivedCategory.standard (Modules.{t, u, v, w} R)

/-- The existing restriction, with no change to sections or scalar actions.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    Modules.{t, u, v, w} R ⥤ Modules.{t, u, v, w} ((clopenRingRestriction j).obj R) :=
  clopenModuleRestriction j R

/-- Additivity inherited from sectionwise restriction.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance restrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    (restriction.{t, u, v, w} j R).Additive := clopenModuleRestriction_additive j R

/-- Exactness of restriction used in the degreewise and localized functors.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization).
Proof: the module-gluing argument computes kernels on sections and cokernels after
sheafification; restriction to the open slice commutes with both constructions.
This is step 1 of the node, and uses no sectionwise surjectivity of epimorphisms. -/
theorem restriction_exact {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (restriction.{t, u, v, w} j R) ∧
      PreservesFiniteColimits (restriction.{t, u, v, w} j R) := by
  constructor
  · let Ri := (clopenRingRestriction j).obj R
    let V := SheafOfModules.forget.{max v w (t + 1)} Ri ⋙
      PresheafOfModules.toPresheaf Ri.obj
    have : PreservesFiniteLimits (restriction.{t, u, v, w} j R ⋙ V) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{max v w (t + 1)} R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ
            AddCommGrpCat.{max v w (t + 1)}).obj
              (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ V
  · let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).IsContinuous
        (topology X) (topology Y) := isContinuous_overPullback j
    let ψ : R ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).sheafPushforwardContinuous
        RingCat (topology X) (topology Y)).obj ((clopenRingRestriction j).obj R) :=
      ⟨Functor.whiskerRight (NatTrans.op adj.counit) R.obj⟩
    let a : restriction.{t, u, v, w} j R ⊣
        SheafOfModules.pushforward.{max v w (t + 1)} ψ :=
      SheafOfModules.pushforwardPushforwardAdj adj (𝟙 _) ψ (by rfl) (by
      ext U : 2
      change R.obj.map _ ≫ R.obj.map _ = 𝟙 _
      change R.obj.map (adj.counit.app (((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).obj U.unop))).op ≫
        R.obj.map (((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale j)).map (adj.unit.app U.unop))).op = 𝟙 _
      rw [← Functor.map_comp, ← op_comp]
      exact (congrArg (fun f ↦ R.obj.map f.op)
        (adj.left_triangle_components U.unop)).trans (R.obj.map_id _))
    have := a.leftAdjoint_preservesColimits
    infer_instance

attribute [local irreducible] SheafOfModules.pushforward

/-- The finite-limit part of the preceding exactness assertion.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (restriction.{t, u, v, w} j R) := (restriction_exact.{t, u, v, w} j R).1

/-- The finite-colimit part of the preceding exactness assertion.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteColimits (restriction.{t, u, v, w} j R) := (restriction_exact.{t, u, v, w} j R).2

/-- Degreewise restriction of unbounded complexes.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev complexRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :=
  (restriction.{t, u, v, w} j R).mapHomologicalComplex (.up ℤ)

/-- The existing exact-functor localization of restriction.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    DerivedCategory (Modules.{t, u, v, w} R) ⥤
      DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction j).obj R)) :=
  (restriction.{t, u, v, w} j R).mapDerivedCategory

private theorem additive_of_coordinates {J : Type*} {B : J → Type*} {D : Type*}
    [∀ k, Category (B k)] [Category D] [∀ k, Preadditive (B k)] [Preadditive D]
    (r : D ⥤ ∀ k, B k) [r.Faithful] (i : J) (F : B i ⥤ D)
    (e : F ⋙ r ⋙ Pi.eval B i ≅ 𝟭 _)
    (hz : ∀ k, k ≠ i → ∀ N, IsZero ((F ⋙ r ⋙ Pi.eval B k).obj N))
    (hr : ∀ k, (r ⋙ Pi.eval B k).Additive) : F.Additive := by
  have := Functor.additive_of_iso e.symm
  constructor
  intro M N f g
  apply r.map_injective
  funext k
  let := hr k
  change (F ⋙ r ⋙ Pi.eval B k).map (f + g) =
    (r ⋙ Pi.eval B k).map (F.map f + F.map g)
  rw [Functor.map_add (r ⋙ Pi.eval B k)]
  by_cases hki : k = i
  · subst k
    exact Functor.map_add (F ⋙ r ⋙ Pi.eval B i) (f := f) (g := g)
  · exact (hz k hki N).eq_of_tgt _ _

namespace ComplexAssembly
variable {I : Type s} {A : Type a} {B : I → Type b}
  [Category.{c} A] [∀ i, Category.{d} (B i)] [Preadditive A]
  [∀ i, Preadditive (B i)]

private instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

private local instance evalAdditive (i : I) : (Pi.eval B i).Additive where
  map_add := by intros; rfl

private def assemble : (∀ i, CochainComplex (B i) ℤ) ⥤ CochainComplex (∀ i, B i) ℤ where
  obj K :=
    { X n := fun i ↦ (K i).X n
      d n m := fun i ↦ (K i).d n m
      shape n m h := by funext i; exact (K i).shape n m h
      d_comp_d' n m k _ _ := by funext i; exact (K i).d_comp_d n m k }
  map f :=
    { f n := fun i ↦ (f i).f n
      comm' n m _ := by funext i; exact (f i).comm n m }

private def assembleHomotopy {K L : ∀ i, CochainComplex (B i) ℤ}
    {f g : K ⟶ L} (h : ∀ i, Homotopy (f i) (g i)) :
    Homotopy ((assemble (B := B)).map f) ((assemble (B := B)).map g) where
  hom n m := fun i ↦ (h i).hom n m
  zero n m hnm := by funext i; exact (h i).zero n m hnm
  comm n := by funext i; exact (h i).comm n

private def assembleHomotopyEquiv {K L : ∀ i, CochainComplex (B i) ℤ}
    (e : ∀ i, HomotopyEquiv (K i) (L i)) :
    HomotopyEquiv ((assemble (B := B)).obj K) ((assemble (B := B)).obj L) where
  hom := (assemble (B := B)).map (fun i ↦ (e i).hom)
  inv := (assemble (B := B)).map (fun i ↦ (e i).inv)
  homotopyHomInvId := assembleHomotopy (fun i ↦ (e i).homotopyHomInvId)
  homotopyInvHomId := assembleHomotopy (fun i ↦ (e i).homotopyInvHomId)

private def unassemble : CochainComplex (∀ i, B i) ℤ ⥤ ∀ i, CochainComplex (B i) ℤ :=
  Functor.pi' (fun i ↦ (Pi.eval B i).mapHomologicalComplex (.up ℤ))

private def cG (G : (∀ i, B i) ⥤ A) [G.Additive] :=
  assemble (B := B) ⋙ G.mapHomologicalComplex (.up ℤ)
private def cr (r : A ⥤ ∀ i, B i) [r.Additive] := r.mapHomologicalComplex (.up ℤ) ⋙ unassemble

private def cη (r : A ⥤ ∀ i, B i) (G : (∀ i, B i) ⥤ A)
    [r.Additive] [G.Additive] (η : 𝟭 A ≅ r ⋙ G) : 𝟭 (CochainComplex A ℤ) ≅ cr r ⋙ cG G :=
  NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ η.app (K.X n)) (by
      intro n m _
      exact (η.hom.naturality (K.d n m)).symm)) (by
    intro K L f
    ext n
    exact η.hom.naturality (f.f n))

private def cε (r : A ⥤ ∀ i, B i) (G : (∀ i, B i) ⥤ A)
    [r.Additive] [G.Additive] (ε : G ⋙ r ≅ 𝟭 _) : cG G ⋙ cr r ≅ 𝟭 (∀ i, CochainComplex (B i) ℤ) :=
  NatIso.ofComponents (fun K ↦ Pi.isoMk (fun i ↦
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ Pi.eval B i |>.mapIso
      (ε.app (fun k ↦ (K k).X n))) (by
      intro n m _
      exact (congrFun (ε.hom.naturality (fun k ↦ (K k).d n m)) i).symm))) (by
    intro K L f
    funext i
    ext n
    exact congrFun (ε.hom.naturality (fun k ↦ (f k).f n)) i)

end ComplexAssembly

namespace NormalizedLocalization
open CategoryTheory.Functor CategoryTheory.Category
variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₁)
  (η : 𝟭 C₁ ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 C₂)
  (ht : ∀ X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 _)
  (Q₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [Q₁.IsLocalization W₁]
  (Q₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [Q₂.IsLocalization W₂]
  (F' : D₁ ⥤ D₂) (G' : D₂ ⥤ D₁)
  (φ : Q₁ ⋙ F' ≅ F ⋙ Q₂) (ψ : Q₂ ⋙ G' ≅ G ⋙ Q₁)

include ht W₁ W₂ in
private theorem normalized_localized_equivalence :
    ∃ (η' : 𝟭 D₁ ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 D₂),
      (∀ X, Q₁.map (η.hom.app X) = η'.hom.app (Q₁.obj X) ≫
        G'.map (φ.hom.app X) ≫ ψ.hom.app (F.obj X)) ∧
      (∀ Y, ε'.hom.app (Q₂.obj Y) = F'.map (ψ.hom.app Y) ≫
        φ.hom.app (G.obj Y) ≫ Q₂.map (ε.hom.app Y)) ∧
      (∀ X, F'.map (η'.hom.app X) ≫ ε'.hom.app (F'.obj X) = 𝟙 _) ∧
      (∀ Y, η'.hom.app (G'.obj Y) ≫ G'.map (ε'.hom.app Y) = 𝟙 _) := by
  let e : C₁ ≌ C₂ := ⟨F, G, η, ε, ht⟩
  let adj : F ⊣ G := e.toAdjunction
  let : Localization.Lifting Q₁ W₁ (F ⋙ Q₂) F' := ⟨φ⟩
  let : Localization.Lifting Q₂ W₂ (G ⋙ Q₁) G' := ⟨ψ⟩
  let α : (F ⋙ Q₂) ⋙ G' ≅ Q₁ :=
    Functor.associator .. ≪≫ isoWhiskerLeft F ψ ≪≫ (Functor.associator ..).symm ≪≫
      isoWhiskerRight η.symm Q₁ ≪≫ leftUnitor _
  let β : (G ⋙ Q₁) ⋙ F' ≅ Q₂ :=
    Functor.associator .. ≪≫ isoWhiskerLeft G φ ≪≫ (Functor.associator ..).symm ≪≫
      isoWhiskerRight ε Q₂ ≪≫ leftUnitor _
  let : F'.IsEquivalence := Localization.isEquivalence Q₁ W₁ Q₂ W₂
    (F ⋙ Q₂) F' (G ⋙ Q₁) G' α β
  let : CatCommSq F Q₁ Q₂ F' := ⟨φ.symm⟩
  let : CatCommSq G Q₂ Q₁ G' := ⟨ψ.symm⟩
  let adj' := adj.localization Q₁ W₁ Q₂ W₂ F' G'
  refine ⟨asIso adj'.unit, asIso adj'.counit, ?_, ?_, ?_, ?_⟩
  · intro X
    change _ = adj'.unit.app _ ≫ _ ≫ _
    rw [Adjunction.localization_unit_app]
    change Q₁.map (η.hom.app X) =
      (Q₁.map (η.hom.app X) ≫ ψ.inv.app (F.obj X) ≫ G'.map (φ.inv.app X)) ≫
        G'.map (φ.hom.app X) ≫ ψ.hom.app (F.obj X)
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [assoc, assoc, ← G'.map_comp_assoc, φ.inv_hom_id_app]
    erw [G'.map_id (Q₂.obj (F.obj X))]
    simp only [id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  · intro Y
    change adj'.counit.app _ = _
    rw [Adjunction.localization_counit_app]
    rfl
  · exact adj'.left_triangle_components
  · exact adj'.right_triangle_components
end NormalizedLocalization

namespace ComplexAssembly
attribute [local instance] piPreadditive
variable {I : Type s} {A : Type a} {B : I → Type b}
  [Category.{c} A] [∀ i, Category.{d} (B i)] [Abelian A] [∀ i, Abelian (B i)]

private theorem cG_homotopy_inverts (G : (∀ i, B i) ⥤ A) [G.Additive] :
    (MorphismProperty.pi (fun i ↦
      HomologicalComplex.homotopyEquivalences (B i) (.up ℤ))).IsInvertedBy
        (cG G ⋙ HomotopyCategory.quotient A (.up ℤ)) := by
  intro K L f hf
  choose e he using hf
  have hmap : (cG G).map f = (G.mapHomotopyEquiv
      (assembleHomotopyEquiv e)).hom := by
    dsimp only [cG, Functor.comp_map, Functor.mapHomotopyEquiv]
    congr 1
    change (assemble (B := B)).map f =
      (assemble (B := B)).map (fun i ↦ (e i).hom)
    congr 1
    funext i
    exact (he i).symm
  change IsIso ((HomotopyCategory.quotient A (.up ℤ)).map ((cG G).map f))
  rw [hmap]
  exact HomotopyCategory.quotient_inverts_homotopyEquivalences A (.up ℤ) _
    (G.mapHomotopyEquiv (assembleHomotopyEquiv e)).homotopyEquivalences_hom

private noncomputable def hG [Finite I] (G : (∀ i, B i) ⥤ A) [G.Additive] := Localization.lift
    (cG G ⋙ HomotopyCategory.quotient A (.up ℤ)) (cG_homotopy_inverts G)
    (Functor.pi (fun i ↦ HomotopyCategory.quotient (B i) (.up ℤ)))

end ComplexAssembly

namespace ProductShift
attribute [local instance] ComplexAssembly.piPreadditive
variable {I : Type s} (B : I → Type b) [∀ i, Category.{d} (B i)]
  [∀ i, Preadditive (B i)] [∀ i, HasShift (B i) ℤ]

private def shiftCore : ShiftMkCore (∀ i, B i) ℤ where
  F n := Functor.pi (fun i ↦ shiftFunctor (B i) n)
  zero := NatIso.pi (fun i ↦ shiftFunctorZero (B i) ℤ)
  add n m := NatIso.pi (fun i ↦ shiftFunctorAdd (B i) n m)
  assoc_hom_app n m k X := by
    funext i
    simpa only [NatIso.pi, NatTrans.pi, Functor.pi, Functor.comp_obj,
      Category.comp_id, Pi.comp_apply, Functor.pi, Functor.eqToHom_proj,
      Category.assoc, shiftFunctorAdd', Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app] using shiftFunctorAdd_assoc_hom_app (C := B i) n m k (X i)
  zero_add_hom_app n X := by
    funext i
    simpa only [NatIso.pi, NatTrans.pi, Functor.pi, Pi.comp_apply, Functor.eqToHom_proj] using
      shiftFunctorAdd_zero_add_hom_app (C := B i) n (X i)
  add_zero_hom_app n X := by
    funext i
    simpa only [NatIso.pi, NatTrans.pi, Functor.pi, Pi.comp_apply, Functor.eqToHom_proj] using
      shiftFunctorAdd_add_zero_hom_app (C := B i) n (X i)

private instance productHasShift : HasShift (∀ i, B i) ℤ := hasShiftMk _ _ (shiftCore B)
omit [∀ i, Preadditive (B i)] in
private theorem zero_hom (X : ∀ i, B i) :
    (shiftFunctorZero (∀ i, B i) ℤ).hom.app X =
      fun i ↦ (shiftFunctorZero (B i) ℤ).hom.app (X i) := rfl
omit [∀ i, Preadditive (B i)] in
private theorem shift_obj (n : ℤ) (X : ∀ i, B i) :
    (shiftFunctor (∀ i, B i) n).obj X =
      (Functor.pi (fun i ↦ shiftFunctor (B i) n)).obj X := rfl
omit [∀ i, Preadditive (B i)] in
private theorem add_hom (n m : ℤ) (X : ∀ i, B i) :
    (shiftFunctorAdd (∀ i, B i) n m).hom.app X =
      fun i ↦ (shiftFunctorAdd (B i) n m).hom.app (X i) := rfl

variable [∀ i, ∀ n : ℤ, (shiftFunctor (B i) n).Additive]
private instance shiftAdditive (n : ℤ) : (shiftFunctor (∀ i, B i) n).Additive where
  map_add := by
    intro X Y f g
    funext i
    exact Functor.map_add (shiftFunctor (B i) n)

private instance evalAdditive (i : I) : (Pi.eval B i).Additive where
  map_add := by intros; rfl

variable [∀ i, HasZeroObject (B i)] [∀ i, Pretriangulated (B i)]
open CategoryTheory.Pretriangulated

omit [∀ i, HasShift (B i) ℤ] [∀ i, Pretriangulated (B i)]
  [∀ i, HasZeroObject (B i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (B i) n).Additive] in
private theorem zero_apply {X Y : ∀ i, B i} (i : I) : (0 : X ⟶ Y) i = 0 := rfl

private instance productZero : HasZeroObject (∀ i, B i) where
  zero := ⟨fun i ↦ 0, (IsZero.iff_id_eq_zero _).mpr (by
    funext i
    exact (isZero_zero (B i)).eq_of_src _ _)⟩

private def evalTriangle (T : Triangle (∀ i, B i)) (i : I) : Triangle (B i) :=
  Triangle.mk (T.mor₁ i) (T.mor₂ i) (T.mor₃ i)

private instance productPretriangulated : Pretriangulated (∀ i, B i) where
  distinguishedTriangles := {T | ∀ i, evalTriangle B T i ∈ distTriang (B i)}
  isomorphic_distinguished T₁ hT₁ T₂ e i := by
    exact isomorphic_distinguished _ (hT₁ i) _ (Triangle.isoMk _ _
      ((Pi.eval B i).mapIso (Triangle.π₁.mapIso e))
      ((Pi.eval B i).mapIso (Triangle.π₂.mapIso e))
      ((Pi.eval B i).mapIso (Triangle.π₃.mapIso e))
      (congrFun e.hom.comm₁ i) (congrFun e.hom.comm₂ i) (by
        exact congrFun e.hom.comm₃ i))
  contractible_distinguished X i := by
    let e₀ : (evalTriangle B (contractibleTriangle X) i).obj₃ ≅
        (contractibleTriangle (X i)).obj₃ :=
      (Functor.map_isZero (Pi.eval B i) (isZero_zero _)).isoZero
    apply isomorphic_distinguished _ (contractible_distinguished (X i)) _
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e₀
      (by simp [evalTriangle, contractibleTriangle])
      (by simp [evalTriangle, contractibleTriangle, zero_apply])
      (by simp [evalTriangle, contractibleTriangle, zero_apply])
  distinguished_cocone_triangle f := by
    choose Z g h hT using fun i ↦ distinguished_cocone_triangle (f i)
    exact ⟨Z, g, h, hT⟩
  rotate_distinguished_triangle T := by
    constructor
    · intro h i
      exact (rotate_distinguished_triangle (evalTriangle B T i)).mp (h i)
    · intro h i
      exact (rotate_distinguished_triangle (evalTriangle B T i)).mpr (h i)
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b hab := by
    choose c hc₁ hc₂ using fun i ↦ complete_distinguished_triangle_morphism
      (evalTriangle B T₁ i) (evalTriangle B T₂ i) (hT₁ i) (hT₂ i)
      (a i) (b i) (congrFun hab i)
    exact ⟨c, funext hc₁, funext hc₂⟩

variable {A : Type a} [Category.{c} A] [Preadditive A] [HasShift A ℤ]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [HasZeroObject A] [Pretriangulated A]

@[instance_reducible]
private def familyCommShift (F : ∀ i, A ⥤ B i) [∀ i, (F i).CommShift ℤ] :
    (Functor.pi' F).CommShift ℤ where
  commShiftIso n := NatIso.pi' (fun i ↦ (F i).commShiftIso n)
  commShiftIso_zero := by
    ext X i
    exact congr_app (congrArg Iso.hom ((F i).commShiftIso_zero ℤ)) X
  commShiftIso_add n m := by
    ext X i
    exact congr_app (congrArg Iso.hom ((F i).commShiftIso_add n m)) X

private theorem familyTriangulated (F : ∀ i, A ⥤ B i) [∀ i, (F i).CommShift ℤ]
    [∀ i, (F i).IsTriangulated] :
    letI := familyCommShift B F
    (Functor.pi' F).IsTriangulated := by
  let := familyCommShift B F
  constructor
  intro T hT i
  exact (F i).map_distinguished T hT

private theorem inverseTriangulated (F : A ⥤ ∀ i, B i) (G : (∀ i, B i) ⥤ A)
    [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 A ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 _)
    (ht : ∀ X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 _) :
    ∃ hG : G.CommShift ℤ,
      (letI := hG; G.IsTriangulated) ∧
      (∀ n K, F.map ((hG.commShiftIso n).hom.app K) ≫
        (F.commShiftIso n).hom.app (G.obj K) =
        ε.hom.app ((shiftFunctor (∀ i, B i) n).obj K) ≫
          (shiftFunctor (∀ i, B i) n).map (ε.inv.app K)) := by
  let E : A ≌ ∀ i, B i := ⟨F, G, η, ε, ht⟩
  let := E.commShiftInverse ℤ
  have : E.CommShift ℤ := E.commShift_of_functor ℤ
  have hE : E.IsTriangulated := Equivalence.IsTriangulated.mk' E inferInstance
  refine ⟨E.commShiftInverse ℤ, hE.rightAdjoint_isTriangulated, ?_⟩
  intro n K
  have hh := E.toAdjunction.commShiftIso_hom_app_counit_app_shift ℤ n K
  simp only [Functor.commShiftIso_comp_hom_app] at hh
  change (F.map ((G.commShiftIso n).hom.app K) ≫
    (F.commShiftIso n).hom.app (G.obj K)) ≫
      (shiftFunctor (∀ i, B i) n).map (ε.hom.app K) =
        ε.hom.app ((shiftFunctor (∀ i, B i) n).obj K) at hh
  apply (cancel_mono ((shiftFunctor (∀ i, B i) n).map (ε.hom.app K))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(shiftFunctor (∀ i, B i) n).map_id K]
  erw [Category.comp_id]
  simpa only [Category.assoc] using hh

end ProductShift

namespace CoordinateSums
attribute [local instance] ComplexAssembly.piPreadditive
noncomputable section

/-- Equality transport of categories. Source: Stacks 015F, finite-product argument
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def coordinateTransport {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] {i k : J} (h : i = k) : D i ⥤ D k := by
  subst k
  exact 𝟭 _

/-- Insert a coordinate and zero objects elsewhere. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def coordinateInsertion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] (i : J) : D i ⥤ ∀ k, D k := by
  classical
  exact Functor.pi' (fun k ↦ if h : i = k then coordinateTransport D h
    else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))

private def coordinateProjection {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : 𝟭 (∀ k, D k) ⟶ Pi.eval D i ⋙ coordinateInsertion D i := by
  classical
  apply NatTrans.pi'
  intro k
  change Pi.eval D k ⟶ Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).inv
  · exact 0

private def coordinateInclusion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : Pi.eval D i ⋙ coordinateInsertion D i ⟶ 𝟭 (∀ k, D k) := by
  classical
  apply NatTrans.pi'
  intro k
  change (Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose)))
      ⟶ Pi.eval D k
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).hom
  · exact 0

attribute [local irreducible] coordinateProjection coordinateInclusion

private def coordinateBicone {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    Bicone (fun i ↦ Pi.eval D i ⋙ coordinateInsertion D i) where
  pt := 𝟭 (∀ i, D i)
  π i := coordinateProjection D i
  ι i := coordinateInclusion D i
  ι_π i k := by
    classical
    by_cases h : i = k
    · subst k
      simp only [dite_true, eqToHom_refl]
      apply NatTrans.ext
      funext M l
      by_cases hl : i = l
      · subst l
        simp [coordinateProjection, coordinateInclusion, coordinateInsertion,
          coordinateTransport, NatTrans.pi', Functor.pi', Pi.eval]
      · have hz : IsZero ((coordinateInsertion D i).obj (M i) l) := by
          simpa only [coordinateInsertion, Functor.pi'_obj, dite_eq_right hl, Functor.const_obj_obj]
            using (HasZeroObject.zero (C := D l)).choose_spec
        exact hz.eq_of_src _ _
    · simp only [dite_eq_right h]
      apply NatTrans.ext
      funext M l
      by_cases hi : i = l
      · subst l
        simp [coordinateProjection, coordinateInclusion, NatTrans.pi', Ne.symm h]
        rfl
      · simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
        rfl

private theorem coordinateBicone_total {J : Type*} [Fintype J] (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    ∑ i, (coordinateBicone D).π i ≫ (coordinateBicone D).ι i = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext M k
  rw [NatTrans.app_sum]
  have he {S : Finset J} (f : J → ∀ i, M i ⟶ M i) :
      (∑ i ∈ S, f i) k = ∑ i ∈ S, f i k := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS => simp [Finset.sum_insert hi]
  rw [he]
  change (∑ i, (coordinateProjection D i).app M k ≫
    (coordinateInclusion D i).app M k) = 𝟙 (M k)
  rw [Finset.sum_eq_single k]
  · simp [coordinateProjection, coordinateInclusion, NatTrans.pi',
      coordinateTransport]
  · intro i _ hi
    simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
  · simp

end
end CoordinateSums

namespace CoordinateSums
attribute [local instance] ComplexAssembly.piPreadditive
noncomputable section
open CategoryTheory.Functor

private def transportBicone {C : Type*} [Category C] [HasZeroMorphisms C]
    {J : Type*} {f g : J → C} (b : Bicone f) (e : ∀ i, f i ≅ g i) : Bicone g where
  pt := b.pt
  π i := b.π i ≫ (e i).hom
  ι i := (e i).inv ≫ b.ι i
  ι_π i k := by
    by_cases hik : i = k
    · subst k
      rw [Category.assoc, ← Category.assoc (b.ι i), b.ι_π]
      simp only [dite_true, eqToHom_refl, Category.id_comp, Iso.inv_hom_id]
    · simp only [Category.assoc, ← Category.assoc (b.ι i), b.ι_π, dite_eq_right hik,
        zero_comp, comp_zero]

private def transportBicone_bilimit {C : Type*} [Category C] [Preadditive C]
    {J : Type*} [Fintype J] {f g : J → C} (b : Bicone f) (e : ∀ i, f i ≅ g i)
    (hb : b.IsBilimit) : (transportBicone b e).IsBilimit := by
  apply isBilimitOfTotal
  have ht := IsBilimit.total hb
  simpa only [transportBicone, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_assoc] using ht

private def insertionIso {C : Type*} [Category C] [Preadditive C]
    {J : Type*} (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) (e : ∀ i, D i ⥤ C)
    (he : ∀ i, e i ⋙ E.functor ⋙ Pi.eval D i ≅ 𝟭 _)
    (hz : ∀ i k, k ≠ i → ∀ M, IsZero ((e i ⋙ E.functor ⋙ Pi.eval D k).obj M))
    (i : J) : e i ≅ coordinateInsertion D i ⋙ E.inverse := by
  classical
  have hs : coordinateInsertion D i ⋙ Pi.eval D i ≅ 𝟭 _ := by
    dsimp only [coordinateInsertion]
    refine Functor.pi'CompEval _ i ≪≫ ?_
    simpa only [dite_true, coordinateTransport] using (Iso.refl (𝟭 (D i)))
  let α : e i ⋙ E.functor ≅ coordinateInsertion D i := NatIso.pi' (fun k ↦ by
    by_cases hik : i = k
    · subst k
      exact he i ≪≫ hs.symm
    · exact (Functor.isZero _ (hz i k (Ne.symm hik))).iso
        (Functor.isZero _ (fun M ↦ by
          simpa [coordinateInsertion, hik] using
            (HasZeroObject.zero (C := D k)).choose_spec)))
  exact (Functor.rightUnitor (e i)).symm ≪≫
    Functor.isoWhiskerLeft (e i) E.unitIso ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α E.inverse

private theorem concreteDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙
        (coordinateInsertion D i ⋙ E.inverse)),
      b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
    (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙
        (coordinateInsertion D i ⋙ E.inverse)),
      b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  classical
  let := Fintype.ofFinite J
  let s := coordinateInsertion D
  let e (i : J) := s i ⋙ E.inverse
  constructor
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ (C ⥤ C) :=
      (Functor.whiskeringLeft C (∀ i, D i) (∀ i, D i)).obj E.functor ⋙
        (Functor.whiskeringRight C (∀ i, D i) C).obj E.inverse
    have : H.Additive := inferInstance
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    let b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i) :=
      { pt := 𝟭 _
        π i := E.unitIso.hom ≫ b'.π i
        ι i := b'.ι i ≫ E.unitIso.inv
        ι_π i k := by
          change (b'.ι i ≫ E.unitIso.inv) ≫ (E.unitIso.hom ≫ b'.π k) = _
          rw [Category.assoc, Iso.inv_hom_id_assoc]
          exact b'.ι_π i k }
    refine ⟨b, rfl, ⟨isBilimitOfTotal b ?_⟩⟩
    change ∑ i, (E.unitIso.hom ≫ b'.π i) ≫ (b'.ι i ≫ E.unitIso.inv) = 𝟙 _
    have ht' : ∑ i, b'.π i ≫ b'.ι i = 𝟙 (E.functor ⋙ E.inverse) := ht
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id] using
      congrArg (fun f ↦ E.unitIso.hom ≫ f ≫ E.unitIso.inv) ht'
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ ((∀ i, D i) ⥤ C) :=
      (Functor.whiskeringRight _ _ _).obj E.inverse
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    exact ⟨b', rfl, ⟨isBilimitOfTotal b' ht⟩⟩

end
end CoordinateSums

namespace Degenerate
private theorem zeroComplexes {C : Type*} [Category C] [Preadditive C]
    (h : ∀ M : C, IsZero M) (K : CochainComplex C ℤ) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  exact (h (K.X n)).eq_of_src _ _

private theorem zeroDerived {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (h : ∀ M : C, IsZero M) (K : DerivedCategory C) : IsZero K := by
  let L := (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage K
  exact (Functor.map_isZero DerivedCategory.Q (zeroComplexes h L)).of_iso
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objObjPreimageIso K).symm

private theorem punit {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (h : ∀ M : C, IsZero M) : Nonempty (C ≌ Discrete PUnit.{1}) := by
  apply (equiv_punit_iff_unique C).mpr
  exact ⟨⟨0⟩, fun M N ↦ ⟨{ default := 0, uniq := fun f ↦ (h M).eq_of_src _ _ }⟩⟩

private theorem zeroOfEquiv {C : Type*} [Category C] [HasZeroMorphisms C]
    (e : C ≌ Discrete PUnit.{1}) (M : C) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply e.functor.map_injective
  exact Subsingleton.elim _ _
end Degenerate

open AlgebraicGeometry.Scheme.ProEt
private theorem zeroRingModules
    {X : AlgebraicGeometry.Scheme.{s}} (R : Sheaf (topology X) RingCat.{a})
    (h : ∀ U : X.ProEtᵒᵖ, Subsingleton (R.obj.obj U))
    (M : ringedSiteModules.{b} R) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  ext U x
  have := h U
  have := Module.subsingleton (R.obj.obj U) (M.val.obj U)
  exact Subsingleton.elim _ _

/-- An equivalence with a fixed forward functor, retaining its specified unit and counit.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev FixedEquivalence {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :=
  {e : Σ G : D ⥤ C, (𝟭 C ≅ F ⋙ G) × (G ⋙ F ≅ 𝟭 D) //
    ∀ X, F.map (e.2.1.hom.app X) ≫ e.2.2.hom.app (F.obj X) = 𝟙 _}

namespace FixedEquivalence
variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D}

/-- The inverse in the specified equivalence data. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev inverse (e : FixedEquivalence F) := e.val.1
/-- The unit in the specified equivalence data. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev unitIso (e : FixedEquivalence F) := e.val.2.1
/-- The counit in the specified equivalence data. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev counitIso (e : FixedEquivalence F) := e.val.2.2
/-- The left triangle for the specified equivalence data. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
theorem functor_unitIso_comp (e : FixedEquivalence F) : ∀ X,
    F.map (e.unitIso.hom.app X) ≫ e.counitIso.hom.app (F.obj X) = 𝟙 _ := e.property
end FixedEquivalence

/-- Package an existent, fully specified equivalence without expanding its witnesses.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def FixedEquivalence.ofExists {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    (P : ∀ (G : D ⥤ C), (𝟭 C ≅ F ⋙ G) → (G ⋙ F ≅ 𝟭 D) → Prop)
    (h : ∃ G η ε, P G η ε)
    (ht : ∀ G η ε, P G η ε → ∀ X, F.map (η.hom.app X) ≫
      ε.hom.app (F.obj X) = 𝟙 _) :
    {e : FixedEquivalence F // P e.inverse e.unitIso e.counitIso} := by
  apply Classical.choice
  obtain ⟨G, η, ε, h⟩ := h
  exact ⟨⟨⟨⟨G, η, ε⟩, ht G η ε h⟩, h⟩⟩

section Partition

variable (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
  (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
  (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
  (R : Sheaf (topology X) RingCat.{u})
  (hcomm : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a)

/-- The tuple of component module categories of the recorded gluing theorem.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev Components := ∀ i, Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)

/-- The module equivalence with exactly the specified sectionwise gluing data.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def recordedEquivalence :
    FixedEquivalence (Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)) :=
  (FixedEquivalence.ofExists _ _
    (clopen_ringed_module_gluing.{t, u, v, w,
      max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)
    (fun _ _ _ h ↦ h.2.2.2.2.2.2.2.1)).val

attribute [irreducible] recordedEquivalence
attribute [local irreducible] restriction

/-- The sectionwise gluing inverse, determined by the full section and morphism formulas
of the recorded dependency; only the proofs of its properties may be postponed.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def gluing : Components.{t, u, v, w} X I Y j R ⥤ Modules.{t, u, v, w} R :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).inverse

/-- The specified restriction-of-sections module unit, not an arbitrary automorphism.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def moduleUnit : 𝟭 _ ≅ (Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)) ⋙
    gluing.{t, u, v, w} X I Y j hd hc R hcomm :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).unitIso

/-- The specified projection module counit.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def moduleCounit : gluing.{t, u, v, w} X I Y j hd hc R hcomm ⋙
    Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R) ≅ 𝟭 _ :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).counitIso

/-- The selected zero insertion from the same module-gluing data.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def insertion (i : I) : Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R) ⥤
    Modules.{t, u, v, w} R :=
  CoordinateSums.coordinateInsertion
    (fun k ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j k)).obj R)) i ⋙
      gluing.{t, u, v, w} X I Y j hd hc R hcomm

private theorem moduleTriangle : ∀ M,
    (Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)).map
      ((moduleUnit.{t, u, v, w} X I Y j hd hc R hcomm).hom.app M) ≫
      (moduleCounit.{t, u, v, w} X I Y j hd hc R hcomm).hom.app
        ((Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)).obj M) = 𝟙 _ :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).functor_unitIso_comp

attribute [irreducible] gluing moduleUnit moduleCounit insertion

private def moduleEquivalence : Modules.{t, u, v, w} R ≌
    Components.{t, u, v, w} X I Y j R :=
  ⟨Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R),
    gluing.{t, u, v, w} X I Y j hd hc R hcomm,
    moduleUnit.{t, u, v, w} X I Y j hd hc R hcomm,
    moduleCounit.{t, u, v, w} X I Y j hd hc R hcomm,
    moduleTriangle.{t, u, v, w} X I Y j hd hc R hcomm⟩

private def insertionCoordinate (i k : I) :
    insertion.{t, u, v, w} X I Y j hd hc R hcomm i ⋙
      restriction.{t, u, v, w} (j k) R ≅
    CoordinateSums.coordinateInsertion
      (fun l ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j l)).obj R)) i ⋙
        Pi.eval _ k := by
  let s := CoordinateSums.coordinateInsertion
    (fun l ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j l)).obj R)) i
  unfold insertion
  change (s ⋙ gluing.{t, u, v, w} X I Y j hd hc R hcomm) ⋙
    restriction.{t, u, v, w} (j k) R ≅ s ⋙ Pi.eval _ k
  exact Functor.associator s _ _ ≪≫ Functor.isoWhiskerLeft s
    (Functor.isoWhiskerRight
      (moduleCounit.{t, u, v, w} X I Y j hd hc R hcomm) (Pi.eval _ k))

private def insertionDiagonal (i : I) :
    insertion.{t, u, v, w} X I Y j hd hc R hcomm i ⋙
      restriction.{t, u, v, w} (j i) R ≅ 𝟭 _ := by
  refine insertionCoordinate.{t, u, v, w} X I Y j hd hc R hcomm i i ≪≫ ?_
  dsimp only [CoordinateSums.coordinateInsertion]
  refine Functor.pi'CompEval _ i ≪≫ ?_
  simpa only [dite_true, CoordinateSums.coordinateTransport] using (Iso.refl (𝟭 _))

private theorem insertionOffDiagonal (i k : I) (hki : k ≠ i) (M) :
    IsZero ((insertion.{t, u, v, w} X I Y j hd hc R hcomm i ⋙
      restriction.{t, u, v, w} (j k) R).obj M) := by
  have hz : IsZero ((CoordinateSums.coordinateInsertion
      (fun l ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j l)).obj R)) i).obj M k) := by
    simpa only [CoordinateSums.coordinateInsertion, Functor.pi'_obj,
      dite_eq_right (Ne.symm hki), Functor.const_obj_obj] using
        (HasZeroObject.zero (C := Modules.{t, u, v, w}
          ((clopenRingRestriction (j k)).obj R))).choose_spec
  exact hz.of_iso ((insertionCoordinate.{t, u, v, w} X I Y j hd hc R hcomm i k).app M)

/-- Zero insertion is additive, since it inserts coordinatewise zeros and then applies
an additive gluing functor. Source: Stacks 015F
(blueprint: lem-pur-clopen-unbounded-derived-localization).
Proof (step 1): addition is coordinatewise in the product. Zero insertion preserves
it, and the sectionwise product gluing of the dependency preserves it as well. -/
theorem insertion_additive (i : I) :
    (insertion.{t, u, v, w} X I Y j hd hc R hcomm i).Additive := by
  let E := moduleEquivalence.{t, u, v, w} X I Y j hd hc R hcomm
  have : E.functor.Faithful := E.faithful_functor
  exact additive_of_coordinates E.functor i _
    (insertionDiagonal.{t, u, v, w} X I Y j hd hc R hcomm i)
    (fun k hki M ↦ insertionOffDiagonal.{t, u, v, w} X I Y j hd hc R hcomm i k hki M)
    (fun k ↦ restrictionAdditive.{t, u, v, w} (j k) R)

attribute [instance] insertion_additive

/-- Exactness of insertion, needed for its unbounded localization.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization).
Proof (step 1): the tuple kernel and cokernel have the given kernel and cokernel
in coordinate i and zero elsewhere. The exact gluing equivalence preserves both. -/
theorem insertion_exact (i : I) :
    PreservesFiniteLimits (insertion.{t, u, v, w} X I Y j hd hc R hcomm i) ∧
      PreservesFiniteColimits (insertion.{t, u, v, w} X I Y j hd hc R hcomm i) := by
  have h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (clopen_ringed_module_gluing.{t, u, v, w,
      max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)))
  apply ((Functor.exact_tfae
    (insertion.{t, u, v, w} X I Y j hd hc R hcomm i)).out 2 4).mp
  intro S hS
  apply (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (S.map (insertion.{t, u, v, w} X I Y j hd hc R hcomm i))).mpr
  intro k
  suffices (S.map (insertion.{t, u, v, w} X I Y j hd hc R hcomm i) |>.map
      (restriction.{t, u, v, w} (j k) R)).Exact by
    simpa only [restriction] using this
  by_cases hki : k = i
  · subst k
    exact ShortComplex.exact_of_iso
      (S.mapNatIso (insertionDiagonal.{t, u, v, w} X I Y j hd hc R hcomm i).symm) hS
  · exact ShortComplex.exact_of_isZero_X₂ _
      (insertionOffDiagonal.{t, u, v, w} X I Y j hd hc R hcomm i k hki S.X₂)

/-- Finite limits are preserved by the specified insertion.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance insertionLimits (i : I) :
    PreservesFiniteLimits (insertion.{t, u, v, w} X I Y j hd hc R hcomm i) :=
  (insertion_exact.{t, u, v, w} X I Y j hd hc R hcomm i).1

/-- Finite colimits are preserved by the specified insertion.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
instance insertionColimits (i : I) :
    PreservesFiniteColimits (insertion.{t, u, v, w} X I Y j hd hc R hcomm i) :=
  (insertion_exact.{t, u, v, w} X I Y j hd hc R hcomm i).2

/-- The unbounded complexes over the ambient coefficient sheaf.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev Complexes := CochainComplex (Modules.{t, u, v, w} R) ℤ

/-- The component complex categories, with no boundedness hypothesis.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev ComplexComponents :=
  ∀ i, CochainComplex (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) ℤ

/-- The actual degreewise tuple restriction.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev complexFamily := Functor.pi' (fun i ↦ complexRestriction.{t, u, v, w} (j i) R)

/-- Taking the nth module of each complex in a tuple.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev componentDegree (n : ℤ) := Functor.pi (fun i ↦ HomologicalComplex.eval
  (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) (.up ℤ) n)

/-- The actual restriction on homotopy categories.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev homotopyFamily := Functor.pi' (fun i ↦
  (restriction.{t, u, v, w} (j i) R).mapHomotopyCategory (.up ℤ))

/-- The tuple of homotopy quotient functors.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev componentQuotient := Functor.pi (fun i ↦ HomotopyCategory.quotient
  (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) (.up ℤ))

/-- The ordinary unbounded derived category, in the standard localization universe.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev Derived := DerivedCategory (Modules.{t, u, v, w} R)

/-- The product of the ordinary component derived categories.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev DerivedComponents :=
  ∀ i, DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R))

/-- The tuple of the canonical localization functors.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev componentLocalization := Functor.pi (fun i ↦
  (DerivedCategory.Q : CochainComplex
    (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) ℤ ⥤ _))

/-- The tuple of the canonical exact-functor derived restrictions.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev derivedFamily := Functor.pi' (fun i ↦ derivedRestriction.{t, u, v, w} (j i) R)

/-- The zero insertion localized by the existing exact-functor construction.
Source: Stacks 015F (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev derivedInsertion (i : I) :
    DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) ⥤
      DerivedCategory (Modules.{t, u, v, w} R) :=
  (insertion.{t, u, v, w} X I Y j hd hc R hcomm i).mapDerivedCategory

/-- Shift every component by the same integer, using its existing signed derived shift.
Source: Stacks 05RU (blueprint: lem-pur-clopen-unbounded-derived-localization). -/
abbrev componentShift (n : ℤ) := Functor.pi (fun i ↦ shiftFunctor
  (DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R))) n)

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors

/-- All comparisons of the finite-clopen unbounded localization statement, including
its prescribed module normalization. The existential data and the labeled conjuncts
express the inverse triangulated functor directly on coordinate shifts and tuples
of distinguished triangles,
without selecting a second triangulated structure on any component derived category.
Source: Stacks 015F and 05RU, finite-clopen application
(blueprint: lem-pur-clopen-unbounded-derived-localization). -/
def LocalizationStatement : Prop :=
  ∃ complexGluing : (ComplexComponents.{t, u, v, w} X I Y j R) ⥤ (Complexes.{t, u, v, w} X R),
  ∃ degreeIso : ∀ n : ℤ, complexGluing ⋙ HomologicalComplex.eval (Modules.{t, u, v, w} R) (.up
    ℤ) n ≅
    componentDegree.{t, u, v, w} X I Y j R n ⋙ (gluing.{t, u, v, w} X I Y j hd hc R hcomm),
  ∃ complexUnit : 𝟭 (Complexes.{t, u, v, w} X R) ≅ (complexFamily.{t, u, v, w} X I Y j R) ⋙
      complexGluing,
  ∃ complexCounit : complexGluing ⋙ (complexFamily.{t, u, v, w} X I Y j R) ≅ 𝟭
      (ComplexComponents.{t, u, v, w} X I Y j R),
  ∃ homotopyGluing : (∀ i, HomotopyCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj
      R)) (.up ℤ)) ⥤ HomotopyCategory (Modules.{t, u, v, w} R) (.up ℤ),
  ∃ homotopyUnit : 𝟭 _ ≅ (homotopyFamily.{t, u, v, w} X I Y j R) ⋙ homotopyGluing,
  ∃ homotopyCounit : homotopyGluing ⋙ (homotopyFamily.{t, u, v, w} X I Y j R) ≅ 𝟭 _,
  ∃ homotopyRestrictionFactors : HomotopyCategory.quotient (Modules.{t, u, v, w} R) (.up ℤ) ⋙
      (homotopyFamily.{t, u, v, w} X I Y j R) ≅ (complexFamily.{t, u, v, w} X I Y j R) ⋙
      (componentQuotient.{t, u, v, w} X I Y j R),
  ∃ homotopyGluingFactors : (componentQuotient.{t, u, v, w} X I Y j R) ⋙ homotopyGluing ≅
    complexGluing ⋙ HomotopyCategory.quotient (Modules.{t, u, v, w} R) (.up ℤ),
  ∃ derivedGluing : (DerivedComponents.{t, u, v, w} X I Y j R) ⥤ (Derived.{t, u, v, w} X R),
  ∃ derivedUnit : 𝟭 (Derived.{t, u, v, w} X R) ≅ (derivedFamily.{t, u, v, w} X I Y j R) ⋙
      derivedGluing,
  ∃ derivedCounit : derivedGluing ⋙ (derivedFamily.{t, u, v, w} X I Y j R) ≅ 𝟭
      (DerivedComponents.{t, u, v, w} X I Y j R),
  ∃ restrictionFactors : (DerivedCategory.Q : (Complexes.{t, u, v, w} X R) ⥤ (Derived.{t, u, v, w} X
      R)) ⋙ (derivedFamily.{t, u, v, w} X I Y j R) ≅ (complexFamily.{t, u, v, w} X I Y j R) ⋙
      (componentLocalization.{t, u, v, w} X I Y j R),
  ∃ gluingFactors : (componentLocalization.{t, u, v, w} X I Y j R) ⋙ derivedGluing ≅ complexGluing ⋙
      (DerivedCategory.Q : (Complexes.{t, u, v, w} X R) ⥤ (Derived.{t, u, v, w} X R)),
  ∃ gluingShift : ∀ n : ℤ, componentShift.{t, u, v, w} X I Y j R n ⋙ derivedGluing ≅
    derivedGluing ⋙ shiftFunctor (Derived.{t, u, v, w} X R) n,
  -- differential
  (∀ (K : (ComplexComponents.{t, u, v, w} X I Y j R)) (n m : ℤ),
    (degreeIso n).hom.app K ≫ (gluing.{t, u, v, w} X I Y j hd hc R hcomm).map (fun i ↦ (K i).d n
        m) =
      (complexGluing.obj K).d n m ≫ (degreeIso m).hom.app K) ∧
  -- complexUnit_degree
  (∀ (K : (Complexes.{t, u, v, w} X R)) (n : ℤ),
    (complexUnit.hom.app K).f n ≫ (degreeIso n).hom.app ((complexFamily.{t, u, v, w} X I Y j
        R).obj K) =
      (moduleUnit.{t, u, v, w} X I Y j hd hc R hcomm).hom.app (K.X n)) ∧
  -- complexCounit_degree
  (∀ (K : (ComplexComponents.{t, u, v, w} X I Y j R)) (i : I) (n : ℤ),
    ((complexCounit.hom.app K) i).f n =
      (restriction.{t, u, v, w} (j i) R).map ((degreeIso n).hom.app K) ≫
        ((moduleCounit.{t, u, v, w} X I Y j hd hc R hcomm).hom.app (fun k ↦ (K k).X n)) i) ∧
  -- complex_triangle₁
  (∀ K : (Complexes.{t, u, v, w} X R),
    (complexFamily.{t, u, v, w} X I Y j R).map (complexUnit.hom.app K) ≫ complexCounit.hom.app
        ((complexFamily.{t, u, v, w} X I Y j R).obj K) = 𝟙 _) ∧
  -- complex_triangle₂
  (∀ K : (ComplexComponents.{t, u, v, w} X I Y j R),
    complexUnit.hom.app (complexGluing.obj K) ≫ complexGluing.map
      (complexCounit.hom.app K) = 𝟙 _) ∧
  -- restriction_cohomology
  (∀ (i : I) (m : ℤ), Nonempty
    (complexRestriction.{t, u, v, w} (j i) R ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) m ≅
      HomologicalComplex.homologyFunctor (Modules.{t, u, v, w} R) (.up ℤ) m ⋙ restriction.{t, u,
          v, w} (j i) R)) ∧
  -- insertion_cohomology
  (∀ (i : I) (m : ℤ), Nonempty
    ((insertion.{t, u, v, w} X I Y j hd hc R hcomm i).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (Modules.{t, u, v, w} R) (.up ℤ) m ≅
      HomologicalComplex.homologyFunctor _ (.up ℤ) m ⋙ (insertion.{t, u, v, w} X I Y j hd hc R
          hcomm) i)) ∧
  -- acyclic_iff
  (∀ K : (Complexes.{t, u, v, w} X R), K.Acyclic ↔ ∀ i, ((complexRestriction.{t, u,
      v, w} (j i) R).obj K).Acyclic) ∧
  -- quasiIso_iff
  (∀ (K L : (Complexes.{t, u, v, w} X R)) (f : K ⟶ L),
    QuasiIso f ↔ ∀ i, QuasiIso ((complexRestriction.{t, u, v, w} (j i) R).map f)) ∧
  -- homotopyRestriction_normalization
  (∀ (K : (Complexes.{t, u, v, w} X R)) (i : I),
    (homotopyRestrictionFactors.hom.app K) i =
      ((restriction.{t, u, v, w} (j i) R).mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ∧
  -- homotopyUnit_normalization
  (∀ K : (Complexes.{t, u, v, w} X R),
    (HomotopyCategory.quotient (Modules.{t, u, v, w} R) (.up ℤ)).map (complexUnit.hom.app K) =
      homotopyUnit.hom.app ((HomotopyCategory.quotient (Modules.{t, u, v, w} R) (.up ℤ)).obj K) ≫
        homotopyGluing.map (homotopyRestrictionFactors.hom.app K) ≫
          homotopyGluingFactors.hom.app ((complexFamily.{t, u, v, w} X I Y j R).obj K)) ∧
  -- homotopyCounit_normalization
  (∀ K : (ComplexComponents.{t, u, v, w} X I Y j R),
    homotopyCounit.hom.app ((componentQuotient.{t, u, v, w} X I Y j R).obj K) =
      (homotopyFamily.{t, u, v, w} X I Y j R).map (homotopyGluingFactors.hom.app K) ≫
        homotopyRestrictionFactors.hom.app (complexGluing.obj K) ≫
          (componentQuotient.{t, u, v, w} X I Y j R).map (complexCounit.hom.app K)) ∧
  -- homotopy_triangle₁
  (∀ K, (homotopyFamily.{t, u, v, w} X I Y j R).map (homotopyUnit.hom.app K) ≫
    homotopyCounit.hom.app ((homotopyFamily.{t, u, v, w} X I Y j R).obj K) = 𝟙 _) ∧
  -- homotopy_triangle₂
  (∀ K, homotopyUnit.hom.app (homotopyGluing.obj K) ≫
    homotopyGluing.map (homotopyCounit.hom.app K) = 𝟙 _) ∧
  -- restrictionFactors_normalization
  (∀ (K : (Complexes.{t, u, v, w} X R)) (i : I),
    (restrictionFactors.hom.app K) i =
      (restriction.{t, u, v, w} (j i) R).mapDerivedCategoryFactors.hom.app K) ∧
  -- derivedUnit_normalization
  (∀ K : (Complexes.{t, u, v, w} X R),
    DerivedCategory.Q.map (complexUnit.hom.app K) =
      derivedUnit.hom.app (DerivedCategory.Q.obj K) ≫
        derivedGluing.map (restrictionFactors.hom.app K) ≫
          gluingFactors.hom.app ((complexFamily.{t, u, v, w} X I Y j R).obj K)) ∧
  -- derivedCounit_normalization
  (∀ K : (ComplexComponents.{t, u, v, w} X I Y j R),
    derivedCounit.hom.app ((componentLocalization.{t, u, v, w} X I Y j R).obj K) =
        (derivedFamily.{t, u, v, w} X I Y j R).map (gluingFactors.hom.app K) ≫
      restrictionFactors.hom.app (complexGluing.obj K) ≫
        (componentLocalization.{t, u, v, w} X I Y j R).map (complexCounit.hom.app K)) ∧
  -- derived_triangle₁
  (∀ K : (Derived.{t, u, v, w} X R), (derivedFamily.{t, u, v, w} X I Y j R).map
      (derivedUnit.hom.app K) ≫
    derivedCounit.hom.app ((derivedFamily.{t, u, v, w} X I Y j R).obj K) = 𝟙 _) ∧
  -- derived_triangle₂
  (∀ K : (DerivedComponents.{t, u, v, w} X I Y j R), derivedUnit.hom.app
      (derivedGluing.obj K) ≫
    derivedGluing.map (derivedCounit.hom.app K) = 𝟙 _) ∧
  -- restriction_triangulated
  (∀ i, (derivedRestriction.{t, u, v, w} (j i) R).IsTriangulated) ∧
  -- gluing_shift_zero
  (∀ K : (DerivedComponents.{t, u, v, w} X I Y j R), (gluingShift 0).hom.app K =
    derivedGluing.map (fun i ↦ (shiftFunctorZero (DerivedCategory (Modules.{t, u, v, w}
        ((clopenRingRestriction (j i)).obj R))) ℤ).hom.app (K i)) ≫
      (shiftFunctorZero (Derived.{t, u, v, w} X R) ℤ).inv.app (derivedGluing.obj K)) ∧
  -- gluing_shift_add
  (∀ (n m : ℤ) (K : (DerivedComponents.{t, u, v, w} X I Y j R)), (gluingShift (n
      + m)).hom.app K =
    derivedGluing.map (fun i ↦ (shiftFunctorAdd (DerivedCategory (Modules.{t, u, v, w}
        ((clopenRingRestriction (j i)).obj R))) n m).hom.app (K i)) ≫
      (gluingShift m).hom.app ((componentShift.{t, u, v, w} X I Y j R n).obj K) ≫
        (shiftFunctor (Derived.{t, u, v, w} X R) m).map ((gluingShift n).hom.app K) ≫
          (shiftFunctorAdd (Derived.{t, u, v, w} X R) n m).inv.app (derivedGluing.obj K)) ∧
  -- gluingShift_normalization
  (∀ (n : ℤ) (K : (DerivedComponents.{t, u, v, w} X I Y j R)) (i : I),
    (derivedRestriction.{t, u, v, w} (j i) R).map ((gluingShift n).hom.app K) ≫
        ((derivedRestriction.{t, u, v, w} (j i) R).commShiftIso n).hom.app (derivedGluing.obj K) =
      (derivedCounit.hom.app ((componentShift.{t, u, v, w} X I Y j R n).obj K)) i ≫
        (shiftFunctor (DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj
            R))) n).map ((derivedCounit.inv.app K) i)) ∧
  -- gluing_triangulated
  (∀ T : ∀ i, Pretriangulated.Triangle (DerivedCategory (Modules.{t, u, v, w}
      ((clopenRingRestriction (j i)).obj R))),
    (∀ i, T i ∈ distTriang (DerivedCategory (Modules.{t, u, v, w}
        ((clopenRingRestriction (j i)).obj R)))) →
      Pretriangulated.Triangle.mk
        (derivedGluing.map (fun i ↦ (T i).mor₁))
        (derivedGluing.map (fun i ↦ (T i).mor₂))
        (derivedGluing.map (fun i ↦ (T i).mor₃) ≫
          (gluingShift 1).hom.app (fun i ↦ (T i).obj₁)) ∈ distTriang
              (Derived.{t, u, v, w} X R)) ∧
  -- restriction_insertion
  (∀ i, Nonempty (derivedInsertion.{t, u, v, w} X I Y j hd hc R hcomm i ⋙
      derivedRestriction.{t, u, v, w} (j i) R ≅ 𝟭 _)) ∧
  -- restriction_other_insertion
  (∀ (i k : I), i ≠ k → Nonempty
    (derivedInsertion.{t, u, v, w} X I Y j hd hc R hcomm k ⋙ derivedRestriction.{t, u, v, w} (j
        i) R ≅ (Functor.const (DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j
        k)).obj R)))).obj (0 : (DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j
        i)).obj R)))))) ∧
  -- insertion_restriction_sum
  (∃ b : Bicone (fun i ↦ derivedRestriction.{t, u, v, w} (j i) R ⋙
      (derivedInsertion.{t, u, v, w} X I Y j hd hc R hcomm) i),
    b.pt = 𝟭 (Derived.{t, u, v, w} X R) ∧ Nonempty b.IsBilimit) ∧
  -- gluing_sum
  (∃ b : Bicone (fun i ↦ Pi.eval (fun k ↦ (DerivedCategory (Modules.{t, u, v, w}
      ((clopenRingRestriction (j k)).obj R)))) i ⋙ (derivedInsertion.{t, u, v, w} X I Y j hd hc R
      hcomm) i),
    b.pt = derivedGluing ∧ Nonempty b.IsBilimit) ∧
  -- derived_cohomology
  (∀ (i : I) (m : ℤ), Nonempty
    (derivedRestriction.{t, u, v, w} (j i) R ⋙ DerivedCategory.homologyFunctor _ m ≅
      DerivedCategory.homologyFunctor (Modules.{t, u, v, w} R) m ⋙ restriction.{t, u, v, w} (j
    i) R)) ∧
  -- isZero_iff
  (∀ K : (Derived.{t, u, v, w} X R), IsZero K ↔ ∀ i, IsZero ((derivedRestriction.{t,
      u, v, w} (j i) R).obj K)) ∧
  -- isIso_iff
  (∀ (K L : (Derived.{t, u, v, w} X R)) (f : K ⟶ L),
    IsIso f ↔ ∀ i, IsIso ((derivedRestriction.{t, u, v, w} (j i) R).map f)) ∧
  -- empty_component
  (∀ i, IsEmpty (Y i) →
    (∀ K : CochainComplex (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)) ℤ, IsZero
        K) ∧ Nonempty ((DerivedCategory (Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj
        R))) ≌ Discrete PUnit.{1})) ∧
  -- zero_coefficients
  ((∀ U : X.ProEtᵒᵖ, Subsingleton (R.obj.obj U)) →
    (∀ K : (Complexes.{t, u, v, w} X R), IsZero K) ∧ Nonempty ((Derived.{t, u, v, w} X R) ≌
        Discrete PUnit.{1})) ∧
  -- empty_partition
  (IsEmpty I → IsEmpty X ∧ (∀ K : (Complexes.{t, u, v, w} X R), IsZero K) ∧
    Nonempty ((Derived.{t, u, v, w} X R) ≌ Discrete PUnit.{1}) ∧ Nonempty ((DerivedComponents.{t,
        u, v, w} X I Y j R) ≌ Discrete PUnit.{1}))

/-- Finite-clopen degreewise gluing and its normalized unbounded derived localization.
Source: Stacks 015F and 05RU, the finite-product argument
(blueprint: lem-pur-clopen-unbounded-derived-localization).

Proof, following the node's nine steps:
1. The recorded module equivalence gives additive exact restriction and gluing;
   insertion is exact because kernels and cokernels in a product are coordinatewise.
2. Apply these functors degreewise. Naturality of the module unit and counit for
   differentials gives chain maps. Their module triangle equations hold in every
   degree. Additivity preserves the equation f-g = dh+hd, giving homotopy descent.
3. Exact-functor cohomology comparison gives both displayed cohomology isomorphisms.
   The module equivalence detects zero cohomology and invertible cohomology maps,
   proving acyclicity and quasi-isomorphism detection.
4. The finite product of the component localization functors is a localization
   (lem-sfb-product-localization), including the empty product. Descend degreewise
   restriction and gluing by the localization universal property.
5. Descend the specified degreewise unit and counit and their inverses. Faithfulness
   of precomposition with a localization descends both triangle equations; the
   normalization fields give the exact composites after precomposition.
6. Exact-functor derived restriction is triangulated. For gluing, finite-coordinate
   cone triangles glue to the cone triangle of the glued map: the differential
   matrix is (d, f; 0, -d). The signed shift constraints and their coherences hold
   degreewise and descend by uniqueness of natural-transformation localization.
7. Combine the complex cohomology comparison with the factors through Q and
   descend the natural isomorphism; this includes inverses of quasi-isomorphisms.
8. Localize the module insertion identities. The tuple is the finite biproduct of
   its zero insertions; gluing, an equivalence, preserves this biproduct. This gives
   both bilimit bicones with the identity and gluing as their vertices.
9. Coordinate zeros and coordinate inverses give joint detection. Empty sites and
   zero ring sheaves have only zero modules, hence zero complexes; localizing their
   already invertible maps gives the one-object, one-arrow category. An empty
   covering forces X empty. No boundedness or nonempty-index hypothesis is used. -/
theorem clopen_unbounded_derived_localization :
    LocalizationStatement.{t, u, v, w} X I Y j hd hc R hcomm := by
  classical
  let A := Modules.{t, u, v, w} R
  let B := fun i ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R)
  let r : A ⥤ ∀ i, B i := Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)
  let G : (∀ i, B i) ⥤ A := gluing.{t, u, v, w} X I Y j hd hc R hcomm
  let η : 𝟭 A ≅ r ⋙ G := moduleUnit.{t, u, v, w} X I Y j hd hc R hcomm
  let ε : G ⋙ r ≅ 𝟭 _ := moduleCounit.{t, u, v, w} X I Y j hd hc R hcomm
  have h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (clopen_ringed_module_gluing.{t, u, v, w,
      max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)))
  have hη : ∀ M, r.map (η.hom.app M) ≫ ε.hom.app (r.obj M) = 𝟙 _ :=
    moduleTriangle.{t, u, v, w} X I Y j hd hc R hcomm
  let E : A ≌ ∀ i, B i := ⟨r, G, η, ε, hη⟩
  have : r.Faithful := E.faithful_functor
  have : r.Full := E.full_functor
  have : r.Additive := ⟨fun {M N} f g ↦ by
    funext i
    exact Functor.map_add (restriction.{t, u, v, w} (j i) R)⟩
  have : G.Additive := E.inverse_additive
  let Fc := complexFamily.{t, u, v, w} X I Y j R
  let Gc := ComplexAssembly.cG G
  let ηc : 𝟭 _ ≅ Fc ⋙ Gc := ComplexAssembly.cη r G η
  let εc : Gc ⋙ Fc ≅ 𝟭 _ := ComplexAssembly.cε r G ε
  have hηc : ∀ K, Fc.map (ηc.hom.app K) ≫ εc.hom.app (Fc.obj K) = 𝟙 _ := by
    intro K
    funext i
    apply HomologicalComplex.hom_ext
    intro n
    exact congrFun (hη (K.X n)) i
  have hεc : ∀ K, ηc.hom.app (Gc.obj K) ≫ Gc.map (εc.hom.app K) = 𝟙 _ := by
    intro K
    apply HomologicalComplex.hom_ext
    intro n
    exact E.unit_inverse_comp (fun i ↦ (K i).X n)
  have hcH (i : I) (m : ℤ) :=
    (restriction.{t, u, v, w} (j i) R).mapHomologicalComplexHomologyIso (.up ℤ) m
  have heH (i : I) (m : ℤ) :=
    (insertion.{t, u, v, w} X I Y j hd hc R hcomm i).mapHomologicalComplexHomologyIso (.up ℤ) m
  have hac : ∀ K : CochainComplex A ℤ, K.Acyclic ↔ ∀ i, ((Fc.obj K) i).Acyclic := by
    intro K
    have hsc (i : I) (n : ℤ) : ((Fc.obj K) i).sc n =
        (K.sc n).map (clopenModuleRestriction (j i) R) := by
      change (((restriction.{t, u, v, w} (j i) R).mapHomologicalComplex (.up ℤ)).obj K).sc n = _
      unfold restriction
      rfl
    constructor
    · intro hK i n
      change (((Fc.obj K) i).sc n).Exact
      rw [hsc]
      exact (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (K.sc n)).mp (hK n) i
    · intro hK n
      apply (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (K.sc n)).mpr
      intro i
      rw [← hsc]
      exact hK i n
  have hqi : ∀ (K L : CochainComplex A ℤ) (f : K ⟶ L),
      QuasiIso f ↔ ∀ i, QuasiIso ((Fc.map f) i) := by
    intro K L f
    constructor
    · intro hf i
      have := hf
      exact HomologicalComplex.quasiIso_map_of_preservesHomology f
        (restriction.{t, u, v, w} (j i) R)
    · intro hf
      constructor
      intro n
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have : IsIso (r.map (HomologicalComplex.homologyMap f n)) := by
        apply (isIso_pi_iff _).mpr
        intro i
        have : QuasiIso ((complexRestriction.{t, u, v, w} (j i) R).map f) := hf i
        have hi := (NatIso.isIso_map_iff (hcH i n) f).mp
          ((quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance)
        exact hi
      exact isIso_of_reflects_iso (HomologicalComplex.homologyMap f n) r
  let Qh := HomotopyCategory.quotient A (.up ℤ)
  let Ph := componentQuotient.{t, u, v, w} X I Y j R
  let Fh := homotopyFamily.{t, u, v, w} X I Y j R
  let Gh := ComplexAssembly.hG G
  let φh : Qh ⋙ Fh ≅ Fc ⋙ Ph := NatIso.pi' (fun i ↦
    (restriction.{t, u, v, w} (j i) R).mapHomotopyCategoryFactors (.up ℤ))
  let ψh : Ph ⋙ Gh ≅ Gc ⋙ Qh := Localization.fac _ _ _
  obtain ⟨ηh, εh, hηhn, hεhn, hηht, hεht⟩ :=
    NormalizedLocalization.normalized_localized_equivalence Fc Gc ηc εc hηc
      Qh (HomologicalComplex.homotopyEquivalences A (.up ℤ))
      Ph (MorphismProperty.pi (fun i ↦
        HomologicalComplex.homotopyEquivalences (B i) (.up ℤ))) Fh Gh φh ψh
  let Qd := (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
  let Pd := componentLocalization.{t, u, v, w} X I Y j R
  let Fd := derivedFamily.{t, u, v, w} X I Y j R
  have hGqi : (MorphismProperty.pi (fun i ↦
      HomologicalComplex.quasiIso (B i) (.up ℤ))).IsInvertedBy (Gc ⋙ Qd) := by
    intro K L f hf
    change IsIso (Qd.map (Gc.map f))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mpr
    apply (hqi _ _ _).mpr
    intro i
    let F := Gc ⋙ Fc ⋙ Pi.eval (fun i ↦ CochainComplex (B i) ℤ) i
    let α : F ≅ Pi.eval (fun i ↦ CochainComplex (B i) ℤ) i :=
      Functor.isoWhiskerRight εc (Pi.eval _ i)
    have : QuasiIso (f i) := hf i
    apply (quasiIso_iff_of_arrow_mk_iso
      (F.map f) (f i) (Arrow.isoOfNatIso α (Arrow.mk f))).mpr
    infer_instance
  let Gd := Localization.lift (Gc ⋙ Qd) hGqi Pd
  let φd : Qd ⋙ Fd ≅ Fc ⋙ Pd := NatIso.pi' (fun i ↦
    (restriction.{t, u, v, w} (j i) R).mapDerivedCategoryFactors)
  let ψd : Pd ⋙ Gd ≅ Gc ⋙ Qd := Localization.fac _ _ _
  obtain ⟨ηd, εd, hηdn, hεdn, hηdt, hεdt⟩ :=
    NormalizedLocalization.normalized_localized_equivalence Fc Gc ηc εc hηc
      Qd (HomologicalComplex.quasiIso A (.up ℤ))
      Pd (MorphismProperty.pi (fun i ↦ HomologicalComplex.quasiIso (B i) (.up ℤ)))
      Fd Gd φd ψd
  let D := fun i ↦ DerivedCategory (B i)
  let := ProductShift.productHasShift D
  let := ProductShift.productZero D
  let := ProductShift.shiftAdditive D
  let := ProductShift.productPretriangulated D
  let : Fd.CommShift ℤ := ProductShift.familyCommShift D
    (fun i ↦ derivedRestriction.{t, u, v, w} (j i) R)
  have : Fd.IsTriangulated := ProductShift.familyTriangulated D
    (fun i ↦ derivedRestriction.{t, u, v, w} (j i) R)
  obtain ⟨hGs, hGt, hGn⟩ := ProductShift.inverseTriangulated D Fd Gd ηd εd hηdt
  let := hGs
  let gs (n : ℤ) := Gd.commShiftIso n
  have gs0 : ∀ K, (gs 0).hom.app K = Gd.map
      (fun i ↦ (shiftFunctorZero (D i) ℤ).hom.app (K i)) ≫
        (shiftFunctorZero (DerivedCategory A) ℤ).inv.app (Gd.obj K) := by
    intro K
    rw [show gs 0 = Functor.CommShift.isoZero Gd ℤ from Gd.commShiftIso_zero ℤ]
    simp only [Functor.CommShift.isoZero_hom_app, ProductShift.zero_hom, D, B]
  have gsadd : ∀ n m K, (gs (n + m)).hom.app K =
      Gd.map (fun i ↦ (shiftFunctorAdd (D i) n m).hom.app (K i)) ≫
      (gs m).hom.app ((componentShift.{t, u, v, w} X I Y j R n).obj K) ≫
      (shiftFunctor (DerivedCategory A) m).map ((gs n).hom.app K) ≫
      (shiftFunctorAdd (DerivedCategory A) n m).inv.app (Gd.obj K) := by
    intro n m K
    rw [show gs (n + m) = Functor.CommShift.isoAdd (gs n) (gs m) from
      Gd.commShiftIso_add n m]
    simp only [Functor.CommShift.isoAdd_hom_app, ProductShift.add_hom,
      ProductShift.shift_obj, componentShift, D, B]
  let Ed : DerivedCategory A ≌ ∀ i, D i := ⟨Fd, Gd, ηd, εd, hηdt⟩
  have : Fd.Full := Ed.full_functor
  have : Fd.Faithful := Ed.faithful_functor
  have : Gd.Additive := by
    have : Fd.Additive := ⟨fun {M N} f g ↦ by
      funext i
      exact Functor.map_add (derivedRestriction.{t, u, v, w} (j i) R)⟩
    exact Ed.inverse_additive
  have hdH (i : I) (n : ℤ) :=
    ((restriction.{t, u, v, w} (j i) R).mapDerivedCategoryHomologyFunctorIso n).symm
  have hdZ : ∀ K : DerivedCategory A, IsZero K ↔ ∀ i, IsZero ((Fd.obj K) i) := by
    intro K
    constructor
    · intro hK i
      exact Functor.map_isZero (derivedRestriction.{t, u, v, w} (j i) R) hK
    · intro hK
      rw [IsZero.iff_id_eq_zero]
      apply Fd.map_injective
      funext i
      exact (hK i).eq_of_src _ _
  have hdI : ∀ (K L : DerivedCategory A) (f : K ⟶ L),
      IsIso f ↔ ∀ i, IsIso ((Fd.map f) i) := by
    intro K L f
    constructor
    · intro hf i
      exact inferInstanceAs (IsIso ((derivedRestriction.{t, u, v, w} (j i) R).map f))
    · intro hf
      have : IsIso (Fd.map f) := (isIso_pi_iff _).mpr hf
      exact isIso_of_reflects_iso f Fd
  let hei := insertionDiagonal.{t, u, v, w} X I Y j hd hc R hcomm
  let ei := derivedInsertion.{t, u, v, w} X I Y j hd hc R hcomm
  have heiD (i : I) : ei i ⋙ derivedRestriction.{t, u, v, w} (j i) R ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (hei i) ≪≫ Functor.mapDerivedCategoryIdIso _
  have hez (i k : I) (hik : i ≠ k) (K : D k) :
      IsZero ((ei k ⋙ derivedRestriction.{t, u, v, w} (j i) R).obj K) := by
    let F := insertion.{t, u, v, w} X I Y j hd hc R hcomm k ⋙
      restriction.{t, u, v, w} (j i) R
    have hF (M) : IsZero (F.obj M) := by
      exact insertionOffDiagonal.{t, u, v, w} X I Y j hd hc R hcomm k i hik M
    have : IsZero (F.mapDerivedCategory.obj K) :=
      F.isZero_mapDerivedCategory_obj K (fun n ↦ hF _)
    exact this.of_iso ((Functor.mapDerivedCategoryCompIso _ _).app K)
  have hempty := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hindex := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear h
  let := Fintype.ofFinite I
  let eiso (i : I) := CoordinateSums.insertionIso D Ed ei heiD
    (fun i k hki K ↦ hez k i hki K) i
  obtain ⟨⟨b₀, hb₀, hbil₀⟩, ⟨c₀, hc₀, hcil₀⟩⟩ :=
    CoordinateSums.concreteDecomposition D Ed
  let b := CoordinateSums.transportBicone b₀
    (fun i ↦ Functor.isoWhiskerLeft (derivedRestriction.{t, u, v, w} (j i) R)
      (eiso i).symm)
  have hb : Nonempty b.IsBilimit :=
    ⟨CoordinateSums.transportBicone_bilimit b₀ _ hbil₀.some⟩
  let c := CoordinateSums.transportBicone c₀
    (fun i ↦ Functor.isoWhiskerLeft (Pi.eval D i) (eiso i).symm)
  have hcb : Nonempty c.IsBilimit :=
    ⟨CoordinateSums.transportBicone_bilimit c₀ _ hcil₀.some⟩
  refine ⟨Gc, (fun _ ↦ Iso.refl _), ηc, εc, Gh, ηh, εh, φh, ψh,
    Gd, ηd, εd, φd, ψd, gs, ?_, ?_, ?_, hηc, hεc,
    (fun i n ↦ ⟨hcH i n⟩), (fun i n ↦ ⟨heH i n⟩), hac, hqi,
    (fun _ _ ↦ rfl), hηhn, hεhn, hηht, hεht, (fun _ _ ↦ rfl),
    hηdn, hεdn, hηdt, hεdt, (fun _ ↦ inferInstance), gs0, gsadd, ?_, ?_,
    (fun i ↦ ⟨heiD i⟩), ?_, ⟨b, hb₀, hb⟩, ⟨c, hc₀, hcb⟩,
    (fun i n ↦ ⟨hdH i n⟩), hdZ, hdI, ?_, ?_, ?_⟩
  · intro K n m
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · intro K n
    exact Category.comp_id _
  · intro K i n
    dsimp only [Iso.refl_hom, NatTrans.id_app]
    erw [(restriction.{t, u, v, w} (j i) R).map_id]
    exact (Category.id_comp _).symm
  · intro n K i
    exact congrFun (hGn n K) i
  · intro T hT
    let T' : Pretriangulated.Triangle (∀ i, D i) :=
      Pretriangulated.Triangle.mk (fun i ↦ (T i).mor₁) (fun i ↦ (T i).mor₂)
        (fun i ↦ (T i).mor₃)
    exact hGt.map_distinguished T' hT
  · intro i k hik
    exact ⟨(Functor.isZero _ (hez i k hik)).iso
      (Functor.isZero _ (fun K ↦ isZero_zero _))⟩
  · intro i hi
    let e := (hempty i hi).some
    have hz := Degenerate.zeroOfEquiv e
    exact ⟨Degenerate.zeroComplexes hz,
      Degenerate.punit (Degenerate.zeroDerived hz)⟩
  · intro hR
    have hz := zeroRingModules R hR
    exact ⟨Degenerate.zeroComplexes hz,
      Degenerate.punit (Degenerate.zeroDerived hz)⟩
  · intro hI
    obtain ⟨hX, ⟨e⟩⟩ := hindex hI
    have hz := Degenerate.zeroOfEquiv e
    refine ⟨hX, Degenerate.zeroComplexes hz,
      Degenerate.punit (Degenerate.zeroDerived hz), ?_⟩
    have := hI
    exact Degenerate.punit (fun K ↦ (IsZero.iff_id_eq_zero K).mpr (by
      funext i
      exact isEmptyElim i))

end Partition

end AlgebraicGeometry.Scheme.ProEt.ClopenLocalization
