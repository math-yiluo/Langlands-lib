/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.Point.Over
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Section maps that are isomorphisms on all geometric stalks

Source: Stacks Project, Tags 03PT and 0GKC, stalkwise-isomorphism step.
(blueprint: lem-weil-pbc-etale-section-germ-iso).
-/

@[expose] public section

universe u w v u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

private noncomputable def restrictionStalkIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [LocallySmall.{w} C] (Φ : J.Point.{w}) {U : C} (a : Φ.fiber.obj U)
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
    (G : Sheaf J A) : (Φ.over a).sheafFiber.obj (G.over U) ≅ Φ.sheafFiber.obj G := by
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber a
  let F := e.functor ⋙ Over.forget (Φ.fiber.elementsMk U a)
  have : F.Initial := inferInstance
  change colimit ((Functor.Elements.π (Φ.over a).fiber).op ⋙ (G.over U).obj) ≅
    colimit ((Functor.Elements.π Φ.fiber).op ⋙ G.obj)
  change colimit (F.op ⋙ (Functor.Elements.π Φ.fiber).op ⋙ G.obj) ≅ _
  exact Functor.Final.colimitIso F.op _

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionStalkIso_germ
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [LocallySmall.{w} C] (Φ : J.Point.{w}) {U : C} (a : Φ.fiber.obj U)
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
    (G : Sheaf J A) :
    (Φ.over a).toPresheafFiber (Over.mk (𝟙 U))
        ⟨a, by
          rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
          simp⟩ (G.over U).obj ≫
      (restrictionStalkIso Φ a G).hom = Φ.toPresheafFiber U a G.obj := by
  dsimp only [restrictionStalkIso, toPresheafFiber]
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber a
  let F := e.functor ⋙ Over.forget (Φ.fiber.elementsMk U a)
  exact Functor.Final.ι_colimitIso_hom F.op
    ((Functor.Elements.π Φ.fiber).op ⋙ G.obj)
    (op ((Φ.over a).fiber.elementsMk (Over.mk (𝟙 U)) ⟨a, by
      rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
      simp⟩))

set_option backward.isDefEq.respectTransparency false in
private theorem constantUnitGerm_isIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [LocallySmall.{w} C] (Φ : J.Point.{w})
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
    [HasSheafify J A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)]
    (M : A) (U : C) (a : Φ.fiber.obj U) :
    IsIso ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫
      Φ.toPresheafFiber U a ((constantSheaf J A).obj M).obj) := by
  have h : (Φ.presheafFiberConstIso M).inv =
      Φ.toPresheafFiber U a ((Functor.const Cᵒᵖ).obj M) := by
    apply (cancel_mono (Φ.presheafFiberConstIso M).hom).mp
    simp
  change IsIso ((CategoryTheory.toSheafify J _).app (op U) ≫
    Φ.toPresheafFiber U a (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj M)))
  rw [← Φ.toPresheafFiber_naturality, ← h]
  infer_instance

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- If a linear map into neighbourhood sections induces a bijection at every geometric
point of that neighbourhood, its adjunct is a constant-sheaf trivialization.

Source: Stacks Project, Tag 0GKC, conclusion by Tag 03PT
(blueprint: lem-weil-pbc-etale-section-germ-iso).

Proof: The section map defines a morphism from the constant sheaf on the localized site.
At a lifted point the stalk of restriction is the original stalk: the functor forgetting
the chosen map to the neighbourhood is initial on pointed neighbourhoods. The stalk of
the constant sheaf is its module value, compatibly with its constant sections. Thus the
hypothesis says that every stalk of the adjunct is invertible. The conservative family
of geometric points, localized at U and lifted to the coefficient universe, detects its
invertibility. Take the inverse isomorphism. No finiteness or nonemptiness is needed. -/
theorem exists_constant_iso_of_bijective_section_germs
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : S.Etale) (M : ModuleCat.{u + 1} Λ) (f : M ⟶ G.obj.obj (op U))
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (.of Ω) ⟶ U.left),
      Function.Bijective (f ≫ (pointSmallEtale (a ≫ U.hom)).toPresheafFiber U
        (Over.homMk a rfl) G.obj)) :
    Nonempty (G.over U ≅
      (constantSheaf (S.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  let φ := ((constantSheafAdj (S.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} Λ) Over.mkIdTerminal).homEquiv M (G.over U)).symm f
  have hfLift {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
      (a : (pointSmallEtale s).fiber.obj U) :
      Function.Bijective (f ≫ (pointSmallEtale s).toPresheafFiber U a G.obj) := by
    obtain ⟨b, hb, rfl⟩ := Over.homMk_surjective a
    change Spec (.of Ω) ⟶ U.left at b
    change b ≫ U.hom = s at hb
    subst s
    exact hf Ω b
  have hP := S.isConservativeFamilyOfPoints_ulift_pointSmallEtale
  have hPU := hP.over U
  have hφ : IsIso φ := by
    apply ((hPU.jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)).isIso_iff φ).2
    rintro ⟨-, ⟨⟨Φ, a⟩⟩⟩
    rcases Φ with ⟨-, ⟨x⟩⟩
    let Ψ := S.uliftPointSmallEtale x
    let ψ := Ψ.over a
    let I : Over U := Over.mk (𝟙 U)
    let b : ψ.fiber.obj I := ⟨a, by
          rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
          change Ψ.fiber.map (𝟙 U) a = a
          simp⟩
    let e := CategoryTheory.GrothendieckTopology.Point.restrictionStalkIso Ψ a G
    have hunit := CategoryTheory.GrothendieckTopology.Point.constantUnitGerm_isIso ψ M I b
    have hadj : (toSheafify (S.smallEtaleTopology.over U)
        ((Functor.const (Over U)ᵒᵖ).obj M)).app (op I) ≫ φ.hom.app (op I) = f := by
      have hh := constantSheafAdj_homEquiv_apply (S.smallEtaleTopology.over U)
        (ModuleCat.{u + 1} Λ) Over.mkIdTerminal M (G.over U) φ
      exact hh.symm.trans (Equiv.apply_symm_apply _ _)
    have hcomp : (toSheafify (S.smallEtaleTopology.over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)).app (op I) ≫
        ψ.toPresheafFiber I b ((constantSheaf _ _).obj M).obj ≫
        ψ.sheafFiber.map φ ≫ e.hom = f ≫ Ψ.toPresheafFiber U a G.obj := by
      change _ ≫ ψ.toPresheafFiber I b _ ≫ ψ.presheafFiber.map φ.hom ≫ e.hom = _
      rw [← Category.assoc (ψ.toPresheafFiber I b _), ψ.toPresheafFiber_naturality]
      rw [← Category.assoc, ← Category.assoc, hadj, Category.assoc]
      exact congrArg (fun q ↦ f ≫ q)
        (CategoryTheory.GrothendieckTopology.Point.restrictionStalkIso_germ Ψ a G)
    have hfg : IsIso (f ≫ Ψ.toPresheafFiber U a G.obj) := by
      let Φ₀ := pointSmallEtale (S.algClosurePoint x)
      let e₀ := (Φ₀.uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G
      have he₀ : Ψ.toPresheafFiber U a G.obj ≫ e₀.hom =
          Φ₀.toPresheafFiber U a.down G.obj := by
        exact Functor.Final.ι_colimitIso_hom
          (Functor.Elements.uliftEquivalence.{u + 1} Φ₀.fiber).functor.op
          ((Functor.Elements.π Φ₀.fiber).op ⋙ G.obj) (op (Ψ.fiber.elementsMk U a))
      have hf₀ : Function.Bijective (f ≫ Φ₀.toPresheafFiber U a.down G.obj) :=
        hfLift (S.algClosurePoint x) a.down
      have : IsIso (f ≫ Ψ.toPresheafFiber U a G.obj ≫ e₀.hom) := by
        rw [he₀]
        exact (ConcreteCategory.isIso_iff_bijective _).mpr hf₀
      exact IsIso.of_isIso_comp_right _ e₀.hom
    have : IsIso ((toSheafify (S.smallEtaleTopology.over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)).app (op I) ≫
        ψ.toPresheafFiber I b ((constantSheaf _ _).obj M).obj ≫
        ψ.sheafFiber.map φ ≫ e.hom) := hcomp ▸ hfg
    have : IsIso (ψ.sheafFiber.map φ ≫ e.hom) :=
      IsIso.of_isIso_comp_left
        ((toSheafify (S.smallEtaleTopology.over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)).app (op I) ≫
          ψ.toPresheafFiber I b ((constantSheaf _ _).obj M).obj)
        (ψ.sheafFiber.map φ ≫ e.hom)
    exact IsIso.of_isIso_comp_right _ e.hom
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry.Scheme
