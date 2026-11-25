/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSections
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.RightDerivedPairSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Etale Cohomology, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-exact)

Proof: The two open immersions form a cover, and their intersection is their pullback.
The sheaf condition makes the section map injective, with image the kernel of the
difference of restrictions (etale_mayerVietoris_sections). An injective sheaf restricts
surjectively along the monomorphism U ∩ V → U, by extending a morphism from its free
abelian representable sheaf (injective_sheaf_mono_restriction, Stacks Tag 093X).
Thus every intersection section is the difference of a lifted U-section and zero.
The generic rightDerived_pair_sequence applies this short exact section sequence to
injective resolutions, takes homology, and supplies natural connecting transformations
and the three exactness assertions. For the initial injection, evaluation preserves
finite limits, so its degree-zero augmentation is an isomorphism. Naturality of this
augmentation in the evaluation functor (rightDerived_zero_transformation) transports
the proved section injection to the displayed right derived restriction maps. -/
theorem etale_mayerVietoris_exact (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
∃ δ : ∀ n : ℕ,
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived (n + 1),
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Function.Injective (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map (MorphismProperty.Over.homMk
            (A := Scheme.Etale.mk U.ι) (B := Scheme.Etale.mk (𝟙 X))
            U.ι (Category.comp_id U.ι)).op)).rightDerived 0).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived 0).app F
            x)) ∧
        (∀ n : ℕ,
          Function.Exact (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived n).app F
            x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived n).app F
            x))
            (fun x => ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u +
            1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ∧
          Function.Exact (fun (x :
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n).obj F ×
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n).obj F) =>
            ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ((δ n).app F) ∧
          Function.Exact ((δ n).app F)
            (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u
            + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived (n +
            1)).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived (n +
            1)).app F x))) := by
  let ev (W : X.Etale) :=
    sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op W)
  let rU : Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk U.ι (Category.comp_id U.ι)
  let rV : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk V.ι (Category.comp_id V.ι)
  let kU : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (X.homOfLE_ι inf_le_left)
  let kV : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk V.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (X.homOfLE_ι inf_le_right)
  let res {W W' : X.Etale} (f : W ⟶ W') : ev W' ⟶ ev W :=
    Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      ((evaluation _ _).map f.op)
  have hkU : Mono kU := by
    have : Mono ((Scheme.Etale.forget X ⋙ Over.forget X).map kU) :=
      inferInstanceAs (Mono (X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    exact (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map this
  obtain ⟨δ, hδ⟩ := rightDerived_pair_sequence
    (ev (Scheme.Etale.mk (𝟙 X))) (ev (Scheme.Etale.mk U.ι))
    (ev (Scheme.Etale.mk V.ι)) (ev (Scheme.Etale.mk (U ⊓ V).ι))
    (res rU) (res rV) (res kU) (res kV)
    (fun I _ => (etale_mayerVietoris_sections X U V hcover I).1)
    (fun I _ => (etale_mayerVietoris_sections X U V hcover I).2) (by
      intro I hI y
      have : Injective I := hI
      obtain ⟨x, hx⟩ := injective_sheaf_mono_restriction.{u + 1, u, u + 1}
        X.smallEtaleTopology I kU y
      refine ⟨(x, 0), ?_⟩
      change I.obj.map kU.op x - I.obj.map kV.op 0 = y
      simpa only [map_zero, sub_zero] using hx)
  refine ⟨δ, fun F => ⟨?_, hδ F⟩⟩
  have : PreservesFiniteLimits (ev (Scheme.Etale.mk (𝟙 X))) := inferInstance
  have : PreservesFiniteLimits (ev (Scheme.Etale.mk U.ι)) := inferInstance
  have : PreservesFiniteLimits (ev (Scheme.Etale.mk V.ι)) := inferInstance
  let εX := (ev (Scheme.Etale.mk (𝟙 X))).toRightDerivedZero.app F
  let εU := (ev (Scheme.Etale.mk U.ι)).toRightDerivedZero.app F
  let εV := (ev (Scheme.Etale.mk V.ι)).toRightDerivedZero.app F
  have hU := rightDerived_zero_transformation (res rU) F
  have hV := rightDerived_zero_transformation (res rV) F
  have hεX : Function.Surjective εX :=
    (AddCommGrpCat.epi_iff_surjective εX).mp inferInstance
  have hεU : Function.Injective εU :=
    (AddCommGrpCat.mono_iff_injective εU).mp inferInstance
  have hεV : Function.Injective εV :=
    (AddCommGrpCat.mono_iff_injective εV).mp inferInstance
  intro x y hxy
  obtain ⟨x', rfl⟩ := hεX x
  obtain ⟨y', rfl⟩ := hεX y
  apply congrArg εX
  apply (etale_mayerVietoris_sections X U V hcover F).1
  apply Prod.ext
  · apply hεU
    calc
      εU ((res rU).app F x') = ((res rU).rightDerived 0).app F (εX x') :=
        (ConcreteCategory.congr_hom hU x').symm
      _ = ((res rU).rightDerived 0).app F (εX y') := congrArg Prod.fst hxy
      _ = εU ((res rU).app F y') := ConcreteCategory.congr_hom hU y'
  · apply hεV
    calc
      εV ((res rV).app F x') = ((res rV).rightDerived 0).app F (εX x') :=
        (ConcreteCategory.congr_hom hV x').symm
      _ = ((res rV).rightDerived 0).app F (εX y') := congrArg Prod.snd hxy
      _ = εV ((res rV).app F y') := ConcreteCategory.congr_hom hV y'


end AlgebraicGeometry.Etale
