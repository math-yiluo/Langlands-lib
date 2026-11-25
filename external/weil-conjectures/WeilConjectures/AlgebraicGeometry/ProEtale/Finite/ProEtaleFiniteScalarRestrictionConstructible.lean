/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite scalar restriction preserves pro-etale constructibility

The coefficient map is arbitrary; no surjectivity or flatness is imposed.
The intrinsic constant-ring module category and its existing exact restriction functor
are used throughout. The witness statements retain each original local trivialization cover.

## References

* Stacks Tags 03DA, 03D2, 093I, 093Q, 09AJ, 010N and 015F
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{w}} {R S : Sheaf J RingCat.{w}}
  (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (a₀ : R₀ ⟶ S₀) (a : R ⟶ S) (comm : α ≫ a.hom = a₀ ≫ β)
  (P : _root_.PresheafOfModules.{t} S₀)

include comm in
set_option backward.isDefEq.respectTransparency false in
private theorem scalarRestrictionSheafification : Nonempty
    ((PresheafOfModules.sheafification α).obj
      ((PresheafOfModules.restrictScalars a₀).obj P) ≅
    (SheafOfModules.restrictScalars a).obj
      ((PresheafOfModules.sheafification β).obj P)) := by
  let Q := (PresheafOfModules.sheafification β).obj P
  let η := (PresheafOfModules.sheafificationAdjunction β).unit.app P
  let g : (PresheafOfModules.restrictScalars a₀).obj P ⟶
      (PresheafOfModules.restrictScalars α).obj
        ((SheafOfModules.restrictScalars a).obj Q).val :=
    PresheafOfModules.homMk (CategoryTheory.toSheafify J P.presheaf) (fun U r m ↦ by
      let := (P.obj U).isModule
      let := (Q.val.obj U).isModule
      have h := (η.app U).hom.map_smul ((a₀.app U).hom r) m
      have hc := ConcreteCategory.congr_hom (congr_app comm U) r
      change (a.hom.app U).hom ((α.app U).hom r) =
        (β.app U).hom ((a₀.app U).hom r) at hc
      change (CategoryTheory.toSheafify J P.presheaf).app U
          (((a₀.app U).hom r) • (show P.obj U from m)) =
        ((a.hom.app U).hom ((α.app U).hom r)) •
          (show Q.val.obj U from (CategoryTheory.toSheafify J P.presheaf).app U m)
      rw [hc]
      exact h)
  let f := (PresheafOfModules.sheafificationHomEquiv α
    (P := (PresheafOfModules.restrictScalars a₀).obj P)
    (F := (SheafOfModules.restrictScalars a).obj Q)).symm g
  have hf : (SheafOfModules.toSheaf R).map f = 𝟙 _ := by
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ _).injective
    simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rfl
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact ⟨asIso f⟩

end

private theorem constantModelRestriction (X : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] (a : A →+* B)
    (U : X.ProEt) (M : ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :
    Nonempty ((SheafOfModules.restrictScalars.{u + 1}
      (⟨Functor.whiskerLeft (Over.forget U).op
        (Functor.whiskerRight
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1})).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩)).obj
        (proEtaleConstantModuleSheafOver X B U M) ≅
      proEtaleConstantModuleSheafOver X A U
        ((ModuleCat.restrictScalars.{u + 1} a.ulift.{u + 1, u + 1}).obj M)) := by
  let := (proEtaleConstantRingUnit_over_locallyBijective X A U).1
  let := (proEtaleConstantRingUnit_over_locallyBijective X A U).2
  let := (proEtaleConstantRingUnit_over_locallyBijective X B U).1
  let := (proEtaleConstantRingUnit_over_locallyBijective X B U).2
  let : EssentiallySmall.{u + 1} (Over U) := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  let : ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let α := Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let β := Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let a₀ := Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight ((Functor.const X.ProEtᵒᵖ).map
      (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let a' : (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing X A)).over U) ⟶
      (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing X B)).over U) :=
    ⟨Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom a.ulift.{u + 1, u + 1})).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩
  have h : α ≫ a'.hom = a₀ ≫ β := by
    ext V r
    exact ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map
          (CommRingCat.ofHom a.ulift.{u + 1, u + 1})))
        ((Over.forget U).op.obj V)) r |>.symm
  obtain ⟨e⟩ := scalarRestrictionSheafification α β a₀ a' h
    (proEtaleConstantModulePresheaf (Over U) B M)
  exact ⟨e.symm⟩

private theorem constantDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) _).map a ≫
        proEtaleConstantDirectImageMap f _ B =
      proEtaleConstantDirectImageMap f _ A ≫
        (proEtaleSheafDirectImage f _).map
          ((constantSheaf (ProEt.topology X) _).map a) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    (((proEtaleSheafDirectImage f _).obj
      ((constantSheaf (ProEt.topology X) _).obj B)).property)
  have hA := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((proEtaleSheafDirectImage f _).obj ((constantSheaf (ProEt.topology X) _).obj A)))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  have hB := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj B)
    ((proEtaleSheafDirectImage f _).obj ((constantSheaf (ProEt.topology X) _).obj B)))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)))
  change toSheafify (ProEt.topology Y) _ ≫
      sheafifyMap (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a) ≫
      (proEtaleConstantDirectImageMap f _ B).hom =
    toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (sheafifyMap (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  rw [show toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ B).hom = _ from hB]
  rw [← Category.assoc, show toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ A).hom = _ from hA]
  exact (congrArg (Functor.whiskerLeft (proEtaleBaseChange f).op)
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map a)))

private theorem constantInverse_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    proEtaleConstantInverseImageMap f _ A ≫
        (constantSheaf (ProEt.topology X) _).map a =
      (proEtaleSheafInverseImage f _).map
        ((constantSheaf (ProEt.topology Y) _).map a) ≫
          proEtaleConstantInverseImageMap f _ B := by
  dsimp only [proEtaleConstantInverseImageMap]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).counit.naturality
    ((constantSheaf (ProEt.topology X) _).map a)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Category.assoc, ← hn,
    ← Category.assoc, ← Functor.map_comp, ← constantDirect_naturality,
    Functor.map_comp, Category.assoc]

private noncomputable def pullbackRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : Type u) [CommRing A] [CommRing B] (a : A →+* B)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    proEtaleConstantModulePullback f A
        ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F) ≅
      (proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj
        (proEtaleConstantModulePullback f B F) := by
  have := constantComparison_isIso f A
  have := constantComparison_isIso f B
  let cA := asIso (proEtaleCoefficientInverseImageMap f A)
  let cB := asIso (proEtaleCoefficientInverseImageMap f B)
  let ay := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom a.ulift.{u + 1, u + 1})
  let ax := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom a.ulift.{u + 1, u + 1})
  have h : cA.hom ≫ ax =
      (proEtaleSheafInverseImage f CommRingCat).map ay ≫ cB.hom :=
    constantInverse_naturality f (CommRingCat.ofHom a.ulift.{u + 1, u + 1})
  have := (proEtaleRingRestrictionPullbackApp_properties f _ _ _ _ ay ax cA cB h).2 F
  exact asIso (proEtaleRingRestrictionPullbackApp f _ _ _ _ ay ax cA cB h F)

private noncomputable abbrev localizedRestriction (X : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] (a : A →+* B) (U : X.ProEt) :=
  SheafOfModules.restrictScalars.{u + 1}
    (R := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)).over U)
    (R' := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X B)).over U)
    ⟨Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom a.ulift.{u + 1, u + 1})).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩

/-- Every chosen stratum cover and its constant module models still trivialize the
scalar-restricted sheaf. This records the unchanged witnesses in constructibility. -/
theorem proEtaleFiniteScalarRestriction_sameTrivializations
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (F : proEtaleRingModules X (proEtaleConstantRing X B))
    (S : Stratification X) (i : Fin S.n)
    (I : Type (u + 1)) (U : I → (S.domain i).ProEt)
    (f : ∀ j : I, U j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (_hc : Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain i)).coverings _)
    (M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} B))
    (_ht : ∀ j : I, Nonempty
      ((proEtaleConstantModulePullback (S.immersion i) B F).over (U j) ≅
        proEtaleConstantModuleSheafOver (S.domain i) B (U j) (M j))) :
    ∀ j : I, Nonempty
      ((proEtaleConstantModulePullback (S.immersion i) A
        ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)).over (U j) ≅
        proEtaleConstantModuleSheafOver (S.domain i) A (U j)
          ((ModuleCat.restrictScalars.{u + 1} a.ulift.{u + 1, u + 1}).obj (M j))) := by
  intro j
  obtain ⟨e⟩ := _ht j
  let E := localizedRestriction (S.domain i) A B a (U j)
  let ep := (SheafOfModules.overFunctor _ (U j)).mapIso
    (pullbackRestrictionIso (S.immersion i) A B a F)
  let eo : ((proEtaleRingRestrictScalars
      ((constantSheaf (ProEt.topology (S.domain i)) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj
      (proEtaleConstantModulePullback (S.immersion i) B F)).over (U j) ≅
      E.obj ((proEtaleConstantModulePullback (S.immersion i) B F).over (U j)) := Iso.refl _
  obtain ⟨ec⟩ := constantModelRestriction (S.domain i) A B a (U j) (M j)
  exact ⟨ep ≪≫ eo ≪≫ E.mapIso e ≪≫ ec⟩

/-- The locally constant and finite-stalk conditions hold on the very same strata. -/
theorem proEtaleFiniteScalarRestriction_sameStratification
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (F : proEtaleRingModules X (proEtaleConstantRing X B)) (S : Stratification X)
    (_hS : ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) B
        (proEtaleConstantModulePullback (S.immersion i) B F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) B)
          (proEtaleConstantModulePullback (S.immersion i) B F))) :
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A
          ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A
            ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F))) := by
  classical
  intro i
  obtain ⟨I, U, f, hc, ht⟩ := (_hS i).1
  choose M hM using ht
  have htr := proEtaleFiniteScalarRestriction_sameTrivializations
    X A B a F S i I U f hc M hM
  refine ⟨⟨I, U, f, hc, fun j ↦ ⟨_, htr j⟩⟩, ?_⟩
  intro Ω _ _ y
  let e := (geometricRingModuleStalkFunctor y (proEtaleConstantRing (S.domain i) A)).mapIso
    (pullbackRestrictionIso (S.immersion i) A B a F)
  have : Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) B)
      (proEtaleConstantModulePullback (S.immersion i) B F)) := (_hS i).2 Ω y
  have : Finite ((geometricRingModuleStalkFunctor y
      (proEtaleConstantRing (S.domain i) A)).obj
      ((proEtaleRingRestrictScalars
        ((constantSheaf (ProEt.topology (S.domain i)) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj
        (proEtaleConstantModulePullback (S.immersion i) B F))) := ‹_›
  exact Finite.of_injective e.toLinearEquiv e.toLinearEquiv.injective

private theorem constructibleOfIso (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    {F G : proEtaleRingModules X (proEtaleConstantRing X A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf X A F) :
    IsConstructibleProEtaleModuleSheaf X A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  have := constantComparison_isIso (S.immersion i) A
  let E := proEtaleRingModulePullback (S.immersion i)
    (proEtaleConstantRing X A) (proEtaleConstantRing (S.domain i) A)
    (asIso (proEtaleCoefficientInverseImageMap (S.immersion i) A))
  let ei : proEtaleConstantModulePullback (S.immersion i) A F ≅
      proEtaleConstantModulePullback (S.immersion i) A G := E.mapIso e
  refine ⟨?_, ?_⟩
  · obtain ⟨I, U, f, hc, hT⟩ := (hS i).1
    refine ⟨I, U, f, hc, fun j ↦ ?_⟩
    obtain ⟨M, ⟨eM⟩⟩ := hT j
    exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso ei.symm ≪≫ eM⟩⟩
  · intro Ω _ _ y
    have : Finite ((geometricRingModuleStalkFunctor y
        (proEtaleConstantRing (S.domain i) A)).obj
        (proEtaleConstantModulePullback (S.immersion i) A F)) := (hS i).2 Ω y
    let ey := (geometricRingModuleStalkFunctor y
      (proEtaleConstantRing (S.domain i) A)).mapIso ei.symm
    exact Finite.of_injective ey.toLinearEquiv ey.toLinearEquiv.injective

/-- Finite scalar restriction is exact, preserves constructible sheaves and bounded
constructibility, commutes naturally with every cohomology functor, and preserves and
reflects cohomology vanishing in every degree. -/
theorem proEtaleFiniteScalarRestriction_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) ∧
    PreservesFiniteColimits (proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) ∧
    (∀ F : proEtaleRingModules X (proEtaleConstantRing X B),
      IsConstructibleProEtaleModuleSheaf X B F →
      IsConstructibleProEtaleModuleSheaf X A
        ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)) ∧
    (∀ q : ℤ, Nonempty
      ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)) ⋙
          DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X A)) q ≅
        DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X B)) q ⋙
          proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1})))) ∧
    (∀ (L : DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X B))) (q : ℤ),
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X B)) q).obj L)) ∧
    (∀ L : DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X B)),
      DerivedCategory.TStructure.t.bounded L →
      (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) q).obj L)) →
      DerivedCategory.TStructure.t.bounded
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L) ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L))) := by
  let aX := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom a.ulift.{u + 1, u + 1})
  let R := proEtaleRingRestrictScalars aX
  let : PreservesFiniteLimits R := proEtaleRingRestrictScalars_preservesFiniteLimits aX
  let : PreservesFiniteColimits R := proEtaleRingRestrictScalars_preservesFiniteColimits aX
  let forgetA := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  let : (R ⋙ forgetA).Faithful := inferInstanceAs (SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X B))).Faithful
  let : R.Faithful := Functor.Faithful.of_comp R forgetA
  have hc (F : proEtaleRingModules X (proEtaleConstantRing X B))
      (hF : IsConstructibleProEtaleModuleSheaf X B F) :
      IsConstructibleProEtaleModuleSheaf X A (R.obj F) := by
    obtain ⟨S, hn, hS⟩ := hF
    exact ⟨S, hn, proEtaleFiniteScalarRestriction_sameStratification X A B a F S hS⟩
  let D := R.mapDerivedCategory.{u + 2, u + 2}
  let e (q : ℤ) : DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X B)) q ⋙ R ≅
      D ⋙ DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q :=
    R.mapDerivedCategoryHomologyFunctorIso.{u + 2, u + 2} q
  have hz (L : DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X B))) (q : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj (D.obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X B)) q).obj L) := by
    constructor
    · intro h
      have h' := h.of_iso ((e q).app L)
      rw [IsZero.iff_id_eq_zero] at h' ⊢
      exact R.map_injective (by simpa using h')
    · intro h
      exact (R.map_isZero h).of_iso ((e q).symm.app L)
  refine ⟨proEtaleRingRestrictScalars_preservesFiniteLimits aX,
    proEtaleRingRestrictScalars_preservesFiniteColimits aX, hc,
    fun q ↦ ⟨(e q).symm⟩, hz, ?_⟩
  intro L hL hC
  refine ⟨?_, fun q ↦ constructibleOfIso X A ((e q).app L) (hc _ (hC q))⟩
  obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hL
  constructor
  · refine ⟨l, (DerivedCategory.isGE_iff _ l).2 fun q hq ↦ ?_⟩
    exact (hz L q).2 ((DerivedCategory.isGE_iff L l).1 hl q hq)
  · refine ⟨r, (DerivedCategory.isLE_iff _ r).2 fun q hq ↦ ?_⟩
    exact (hz L q).2 ((DerivedCategory.isLE_iff L r).1 hr q hq)

end AlgebraicGeometry.Scheme
