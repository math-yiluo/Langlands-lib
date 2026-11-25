/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleGeometricPointSectionsStalkNatural
import WeilConjectures.AlgebraicGeometry.EtaleConstantTrivializationPullback
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant

/-!
# Inverse image over a geometric point is constant

Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph
(blueprint: lem-weil-pbc-etale-geometric-fibre-inverse-image-constant).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph
(blueprint: lem-weil-pbc-etale-geometric-fibre-inverse-image-constant).
The inverse image along `h ≫ s` is naturally the constant sheaf of the geometric stalk.
The isomorphism at `Spec Ω` sends each pulled-back pointed section to its germ,
fixing the canonical identification. The family is compatible with every further
morphism over `Ω`.
This compatibility is expressed on constant-presheaf generators: pulling a generator
back through the inverse-image unit and its composition comparison gives the generator
with the same stalk value on the source. Sheafification makes this equivalent to the
usual square with the canonical inverse-image comparison for constant sheaves.
The composition comparison is the unit-preserving witness of
`etaleSetInverseImageCompositionUnits`, whose uniqueness makes the choice immaterial.

Proof:
1. Put `G = s⁻¹F`. By lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant,
   the constant sheaf of the global sections of `G` is canonically `G`.
2. The same lemma identifies these sections with the stalk at the identity point.
   By lem-weil-pbc-sets-etale-inverse-image-stalk-germ this is the stalk of `F` at `s`,
   compatibly with germs of pulled-back sections.
3. Pull this identification back along `h`. Use
   lem-weil-pbc-sets-etale-inverse-image-composition-units to compare the iterated
   inverse image with that along `h ≫ s`, and
   lem-weil-pbc-sets-etale-inverse-image-constant-sheaf to pull back the constant sheaf.
4. Naturality in `F` follows from the naturality of all three comparisons.
   For `v : V → U`, associativity of the composition comparison and the fact that
   the constant-sheaf comparison preserves constant generators give the displayed
   equation. Its uniqueness extends the equality from generators to sheaf morphisms,
   giving naturality in `U` and in every further `Ω`-morphism. -/
theorem etaleGeometricFibreInverseImageConstant
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)),
      Scheme.etaleSetPullback (h ≫ s) ≅
        (Scheme.pointSmallEtale s).sheafFiber ⋙
          constantSheaf U.smallEtaleTopology (Type (u + 1)),
      (∀ (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (W : S.Etale)
        (t : (Scheme.pointSmallEtale s).fiber.obj W)
        (a : Scheme.Etale.mk (𝟙 (Spec (.of Ω))) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s)).obj W)
        (σ : F.obj.obj (op W)),
        a.left ≫ CategoryTheory.Limits.pullback.fst W.hom (𝟙 (Spec (.of Ω)) ≫ s) =
          t.left →
        ((α (Spec (.of Ω)) (𝟙 _)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
          (((Scheme.etaleSetPullback (𝟙 (Spec (.of Ω)) ≫ s)).obj F).obj.map a.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s))
              (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
              ((Spec (.of Ω)).smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op W) σ)) =
        (toSheafify (Spec (.of Ω)).smallEtaleTopology
          ((Functor.const (Spec (.of Ω)).Etaleᵒᵖ).obj
            ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
              (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
              ((Scheme.pointSmallEtale s).toPresheafFiber W t F.obj σ)) ∧
      ∀ (U V : Scheme.{u}) (h : U ⟶ Spec (.of Ω)) (v : V ⟶ U)
        (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
        (W : U.Etale) (e : (Scheme.pointSmallEtale s).sheafFiber.obj F),
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S U V (h ≫ s) v).hom.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
            (((α U h).inv.app F).hom.app (op W)
              ((toSheafify U.smallEtaleTopology
                ((Functor.const U.Etaleᵒᵖ).obj
                  ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app (op W) e))) =
        (((α V (v ≫ h)).inv.app F ≫
          eqToHom (congrArg
            (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
            (Category.assoc v h s))).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
          ((toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj
              ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e) := by
  classical
  obtain ⟨c, hc⟩ := etaleGeometricPointSectionsStalkNatural S Ω s
  let P := Spec (.of Ω)
  let L := Scheme.etaleSetPullback (𝟙 P ≫ s)
  let C := constantSheaf P.smallEtaleTopology (Type (u + 1))
  let hT : CategoryTheory.Limits.IsTerminal (Scheme.Etale.mk (𝟙 P)) :=
    CategoryTheory.Limits.IsTerminal.ofUniqueHom
      (fun W ↦ MorphismProperty.Over.homMk W.hom)
      (fun W f ↦ by
        apply MorphismProperty.Over.Hom.ext
        have hf : f.left ≫ 𝟙 P = W.hom := f.w
        change f.left = W.hom
        exact (Category.comp_id f.left).symm.trans hf)
  let A₀ := constantSheafAdj P.smallEtaleTopology (Type (u + 1))
    CategoryTheory.Limits.terminalIsTerminal
  have : ∀ G : Sheaf P.smallEtaleTopology (Type (u + 1)),
      IsIso (A₀.counit.app G) := fun G ↦
    (Scheme.spec_algClosed_etale_sheaf_constant Ω G).1
  have : IsIso A₀.counit := NatIso.isIso_of_isIso_app _
  let τ := CategoryTheory.Limits.terminalIsTerminal.uniqueUpToIso hT
  let Riso := (sheafSections P.smallEtaleTopology (Type (u + 1))).mapIso τ.op
  let ff := A₀.fullyFaithfulROfIsIsoCounit.ofIso Riso.symm
  have := ff.full
  have := ff.faithful
  let A := constantSheafAdj P.smallEtaleTopology (Type (u + 1)) hT
  let δ : L ⋙ (sheafSections P.smallEtaleTopology (Type (u + 1))).obj
    (op (Scheme.Etale.mk (𝟙 P))) ⋙ C ≅ L := asIso (Functor.whiskerLeft L A.counit)
  let β : L ≅ (Scheme.pointSmallEtale s).sheafFiber ⋙ C :=
    δ.symm ≪≫ Functor.isoWhiskerRight c C
  obtain ⟨α, hα, hcompat⟩ :=
    etaleConstantTrivializationPullback S P s (Scheme.pointSmallEtale s).sheafFiber β
  refine ⟨α, ?_, hcompat⟩
  intro F W t a σ ha
  rw [hα]
  dsimp [β]
  let x := ((L.obj F).obj.map a.op)
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 P ≫ s))
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
      (P.smallGrothendieckTopology @Etale)).unit.app F).hom.app
        (op W) σ)
  have hinv :
      (((δ.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 P)))) x) =
        (toSheafify P.smallEtaleTopology
          ((Functor.const P.Etaleᵒᵖ).obj ((L.obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 P)))))).app (op (Scheme.Etale.mk (𝟙 P))) x := by
    apply (CategoryTheory.injective_of_mono
      ((δ.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 P)))))
    have hi := congrArg (fun q ↦ q.hom.app (op (Scheme.Etale.mk (𝟙 P))))
      (δ.app F).inv_hom_id
    have hie := congrArg (fun q ↦ q x) hi
    dsimp at hie
    refine hie.trans ?_
    change x = ((A.counit.app (L.obj F)).hom.app (op (Scheme.Etale.mk (𝟙 P))))
      ((toSheafify P.smallEtaleTopology
        ((Functor.const P.Etaleᵒᵖ).obj ((L.obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 P)))))).app (op (Scheme.Etale.mk (𝟙 P))) x)
    simp only [Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.id_obj,
      constantSheafAdj_counit_app, ObjectProperty.FullSubcategory.comp_hom,
      sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift,
      Category.comp_id, Functor.const_obj_obj, A]
    have hg := congrArg (fun q ↦ q.app (op (Scheme.Etale.mk (𝟙 P))))
      (toSheafify_sheafifyLift P.smallEtaleTopology
        ((constantPresheafAdj (Type (u + 1)) hT).counit.app (L.obj F).obj)
        (L.obj F).property)
    have hge := congrArg (fun q ↦ q x) hg
    dsimp at hge
    have hself : hT.from (Scheme.Etale.mk (𝟙 P)) = 𝟙 _ :=
      hT.hom_ext _ _
    change _ = (L.obj F).obj.map (hT.from (Scheme.Etale.mk (𝟙 P))).op x at hge
    rw [hself] at hge
    have hm := congrArg (fun q ↦ q x)
      ((L.obj F).obj.map_id (op (Scheme.Etale.mk (𝟙 P))))
    exact hm.symm.trans hge.symm
  change ((C.map (c.hom.app F)).hom.app (op (Scheme.Etale.mk (𝟙 P))))
    (((δ.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 P)))) x) = _
  rw [hinv]
  have hn := congrArg (fun q ↦ q.app (op (Scheme.Etale.mk (𝟙 P))))
    (toSheafify_naturality P.smallEtaleTopology
      ((Functor.const P.Etaleᵒᵖ).map (c.hom.app F)))
  have he := congrArg (fun q ↦ q x) hn
  dsimp [C, constantSheaf] at he ⊢
  rw [← he]
  exact congrArg (fun z ↦ (toSheafify P.smallEtaleTopology
    ((Functor.const P.Etaleᵒᵖ).obj ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
      (op (Scheme.Etale.mk (𝟙 P))) z) (hc F W t a σ ha)

end AlgebraicGeometry
