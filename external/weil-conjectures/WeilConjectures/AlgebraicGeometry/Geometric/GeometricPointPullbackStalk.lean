/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf

/-!
# Global sections at a geometric point and pullback stalks

Source: literature/stacks-project/etale-cohomology.tex, Tags 04JQ, 04JN and 03Q1 (3)
(blueprint: lem-weil-pbc-geometric-point-pullback-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem globalSections_addCommGrp_isEquivalence
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence := by
  let J := (Spec (.of Ω)).smallEtaleTopology
  let U := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let adj := constantSheafAdj J AddCommGrpCat.{u + 1} terminalIsTerminal
  have : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    have : IsIso ((constantSheafAdj J (Type (u + 1))
        terminalIsTerminal).counit.app ((sheafCompose J U).obj F)) :=
      (spec_algClosed_etale_sheaf_constant Ω ((sheafCompose J U).obj F)).1
    have : IsIso ((sheafCompose J U).map (adj.counit.app F)) := by
      rw [← constantSheafAdj_counit_w J U F terminalIsTerminal]
      infer_instance
    exact isIso_of_reflects_iso _ (sheafCompose J U)
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : ((sheafSections J AddCommGrpCat.{u + 1}).obj
      (op (⊤_ (Spec (.of Ω)).Etale))).IsEquivalence :=
    adj.toEquivalence.isEquivalence_inverse
  exact Functor.isEquivalence_of_iso ((sheafSections J AddCommGrpCat.{u + 1}).mapIso
    (terminalIsTerminal.uniqueUpToIso (isTerminalEtalePoint (k := Ω))).symm.op)

private theorem identity_stalk_isIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)) F.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
  let I := Etale.mk (𝟙 (Spec (.of Ω)))
  let xI : Φ.fiber.obj I := Over.homMk (𝟙 _) (Category.comp_id _)
  let U := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let G := (sheafCompose (Spec (.of Ω)).smallEtaleTopology U).obj F
  have : IsIso (Φ.toPresheafFiber I xI (F.obj ⋙ U)) :=
    (isIso_iff_bijective _).2 (spec_algClosed_etale_sheaf_constant Ω G).2
  have : IsIso (U.map (Φ.toPresheafFiber I xI F.obj)) := by
    rw [← Φ.toPresheafFiber_presheafFiberCompIso_hom_app U I xI F.obj]
    infer_instance
  exact isIso_of_reflects_iso _ U

/-- On the spectrum of an algebraically closed field, global sections are an exact
 equivalence for abelian sheaves and for sheaves of modules over any coefficient ring.
 For a geometric point of any scheme, global sections of its inverse image are naturally
 isomorphic to its stalk.

 Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3).
 (blueprint: lem-weil-pbc-geometric-point-pullback-stalk).

 Proof:
 1. `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant` identifies a sheaf of
    sets on `Spec Ω` with the constant sheaf of its global sections. Its canonical
    restriction maps respect addition and scalar multiplication, giving the same
    natural counit isomorphism for abelian sheaves and module sheaves.
 2. `Spec Ω` is connected. By `lem-weil-pbc-constant-sheaf-sections-connected`, the
    unit from an abelian group to the global sections of its constant sheaf is an
    isomorphism. The same map is linear for modules. Thus constant sheaf and global
    sections are quasi-inverse; an equivalence of abelian categories is exact.
 3. Apply the identity-point stalk clause of the constancy lemma to the inverse image
    of `G`: its global sections identify naturally with its stalk at `id (Spec Ω)`.
 4. `lem-weil-pbc-inverse-image-stalk-germ`, applied to `y` and the identity point,
    identifies that stalk naturally with `G_y`. Compose the two natural isomorphisms.
-/
theorem geometricPoint_pullback_stalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence ∧
    PreservesFiniteLimits
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
    PreservesFiniteColimits
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
    (∀ (Λ : Type (u + 1)) [Ring Λ],
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence ∧
      PreservesFiniteLimits
        ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
      PreservesFiniteColimits
        ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω))))))) ∧
    (∀ (Y : Scheme.{u}) (y : Spec (.of Ω) ⟶ Y),
      Nonempty (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} y ⋙
        (sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω))))) ≅
        (pointSmallEtale y).sheafFiber)) := by
  have hA := globalSections_addCommGrp_isEquivalence Ω
  refine ⟨hA, inferInstance, inferInstance, ?_, ?_⟩
  · intro Λ _
    have : ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence :=
      (constantSheafAdj (Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).isEquivalence_right_of_isEquivalence_left
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro Y y
    let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
    let τ := Functor.whiskerLeft
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (Φ.toPresheafFiberNatTrans (Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _)))
    have : IsIso τ := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro F
      exact identity_stalk_isIso Ω F
    obtain ⟨c, _⟩ := AlgebraicGeometry.inverseImage_stalk_germ y (𝟙 (Spec (.of Ω)))
    exact ⟨Functor.isoWhiskerLeft (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} y)
      (asIso τ) ≪≫ c ≪≫ (eqToIso (by simp only [Category.id_comp]))⟩

end AlgebraicGeometry.Scheme
