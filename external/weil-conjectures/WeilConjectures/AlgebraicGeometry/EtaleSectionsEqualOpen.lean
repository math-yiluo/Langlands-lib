/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenExistence

/-! # The open locus where two étale sheaf sections agree

Source: Stacks Project, Étale Cohomology, Lemma 59.39.1 (Tag 09XM), applied over an
étale object of the base scheme (blueprint: lem-weil-pbc-etale-sections-equal-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 09XM
(blueprint: lem-weil-pbc-etale-sections-equal-open).
There is a unique open in the domain of an étale object on which two sections agree,
characterized by their restrictions along every scheme morphism. Restriction along
`a` is the inverse-image adjunction unit followed by restriction along `(a, id)`.

Proof:
1. On the étale site of `V.left`, the presheaf assigning a singleton where the two
   sections agree and the empty set elsewhere is a subsheaf of the final sheaf.
   Restriction preserves agreement; the equalizer sheaf axiom of
   situation-conventions glues the local singleton sections.
2. By lem-weil-pbc-etale-subsheaf-final-open (Tag 04HV), this subsheaf is represented
   by an open `W`. It has the required property for étale test objects. Two candidate
   opens are equal by testing their own open immersions and obtaining both inclusions.
3. By def-weil-pbc-geometric-stalks and
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ (Tag 03Q1), a geometric point
   lies in `W` exactly when the two germs agree. Thus equality after an arbitrary
   pullback forces every point of the test scheme into `W`, giving factorization.
   Conversely, unit restriction compatibility from
   lem-weil-pbc-sets-etale-inverse-image-composition-units pulls equality on `W`
   back to `W ×_S T`; the map `(a, id)` factors through this fibre product. -/
theorem existsUnique_etaleSections_equal_open (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) (s t : F.obj.obj (op V)) :
    ∃! W : V.left.Opens, ∀ (T : Scheme.{u}) (a : T ⟶ V.left),
      (∃ b : T ⟶ W.toScheme, b ≫ W.ι = a) ↔
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) s) =
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) t) := by
  obtain ⟨W, hW⟩ := exists_etaleSections_equal_open S F V s t
  refine ⟨W, hW, ?_⟩
  intro W' hW'
  apply le_antisymm
  · obtain ⟨b, hb⟩ := (hW W'.toScheme W'.ι).mpr
      ((hW' W'.toScheme W'.ι).mp ⟨𝟙 _, Category.id_comp _⟩)
    intro x hx
    have heq := congrArg (fun f : W'.toScheme ⟶ V.left ↦ f ⟨x, hx⟩) hb
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at heq
    change (b ⟨x, hx⟩).val = x at heq
    rw [← heq]
    exact (b ⟨x, hx⟩).property
  · obtain ⟨b, hb⟩ := (hW' W.toScheme W.ι).mpr
      ((hW W.toScheme W.ι).mp ⟨𝟙 _, Category.id_comp _⟩)
    intro x hx
    have heq := congrArg (fun f : W.toScheme ⟶ V.left ↦ f ⟨x, hx⟩) hb
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at heq
    change (b ⟨x, hx⟩).val = x at heq
    rw [← heq]
    exact (b ⟨x, hx⟩).property

end AlgebraicGeometry
