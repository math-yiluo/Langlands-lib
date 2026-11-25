/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonSectionFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonSectionAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction

/-!
# Sections of the etale-to-pro-etale inverse image

## References

* Sites, Tags 03CB and 03CC
* Stacks Project, Tag 0GLZ, paragraph `F = epsilon_* a(F)`
* Tag 099R
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The restriction in the sections formula: the inverse-image unit at the identity
etale object followed by the canonical composition and terminal-object transport. -/
noncomputable def proEtaleComparisonSectionRestriction {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) {Y Z : X.ProEt} (g : Z ⟶ Y) :
    ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) →
      ((Scheme.etaleSetPullback Z.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Z.left))) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
    (Y.left.smallGrothendieckTopology @Etale)
    (Z.left.smallGrothendieckTopology @Etale)).unit.app
      ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
    (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv

/-- The usual identification at an etale object, written as a map before asserting
bijectivity: pull a section back by the unit and restrict along the diagonal. -/
noncomputable def proEtaleComparisonEtaleSection {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    F.obj.obj (op U) →
      ((Scheme.etaleSetPullback U.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 U.left))) := by
  letI : (MorphismProperty.Over.pullback @Etale ⊤ U.hom).IsContinuous
      (X.smallGrothendieckTopology @Etale)
      (U.left.smallGrothendieckTopology @Etale) :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.hom
  exact fun s ↦
    ((Scheme.etaleSetPullback U.hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp))
        (by simp) : Scheme.Etale.mk (𝟙 U.left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj U).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ U.hom) (Type (u + 1))
        (X.smallGrothendieckTopology @Etale)
        (U.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s)

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonEtaleSection_eq
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    proEtaleComparisonEtaleSection F U = (etaleSetTerminalRestriction F U).hom := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ U.hom).IsContinuous
      (X.smallGrothendieckTopology @Etale)
      (U.left.smallGrothendieckTopology @Etale) :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.hom
  let ρ := Classical.choose (etaleSetInverseImageRestriction U.hom)
  let d : Scheme.Etale.mk (𝟙 U.left) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) (by simp)
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ U.hom) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    (U.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U)
  suffices h : η ≫ ((Scheme.etaleSetPullback U.hom).obj F).obj.map d.op =
      (etaleSetTerminalRestriction F U).hom by
    funext s
    exact ConcreteCategory.congr_hom h s
  apply (cancel_mono ((ρ.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 U.left))))).1
  rw [Category.assoc, (ρ.hom.app F).hom.naturality d.op, ← Category.assoc]
  have hu : η ≫ (ρ.hom.app F).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj U)) =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.hom
        inferInstance trivial).counit.app U).op := by
    ext t
    exact Classical.choose_spec (etaleSetInverseImageRestriction U.hom) F U t
  rw [hu]
  change F.obj.map _ ≫ F.obj.map _ = _
  simp only [ρ, etaleSetTerminalRestriction, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [d, MorphismProperty.Over.mapPullbackAdj]

/--
The sheaf functor `A` realizes the prescribed section values through `e`. The first
identity specifies its restrictions, and the second specifies its action on sheaves.
Thus the prescribed presheaf is a sheaf, not merely its sheafification. The natural
isomorphism `p` identifies it with the comparison inverse image. The last two clauses
identify the comparison unit at every etale object with the usual section bijection. -/
theorem proEtaleComparisonPullbackSections (X : Scheme.{u}) :
    ∃ A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
        Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      ∃ e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
        (A.obj F).obj.obj (op Y) ≃
          ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 Y.left))),
      ∃ p : Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) ≅ A,
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
        e F Z ((A.obj F).obj.map g.op s) =
          proEtaleComparisonSectionRestriction F g (e F Y s)) ∧
      (∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
        (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
        e F' Y ((A.map ψ).hom.app (op Y) s) =
          ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
            (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s)) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale),
        Function.Bijective (proEtaleComparisonEtaleSection F U)) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (U : X.Etale) (s : F.obj.obj (op U)),
        e F ((Scheme.toProEt X).obj U)
          ((p.hom.app F).hom.app (op ((Scheme.toProEt X).obj U))
            (((Scheme.proEtaleSiteComparison X).unit.app F).hom.app (op U) s)) =
          proEtaleComparisonEtaleSection F U s) := by
  obtain ⟨A, e, hres, hfun⟩ := proEtaleComparisonSectionFunctor X
  obtain ⟨adj, hunit⟩ := proEtaleComparisonSectionAdjunction X A e hres hfun
  refine ⟨A, e, (Scheme.proEtaleSiteComparison X).leftAdjointUniq adj,
    hres, hfun, ?_, ?_⟩
  · intro F U
    rw [comparisonEtaleSection_eq]
    exact (ConcreteCategory.bijective_of_isIso (etaleSetTerminalRestriction F U).hom)
  · intro F U s
    have hu := Adjunction.unit_leftAdjointUniq_hom_app
      (Scheme.proEtaleSiteComparison X) adj F
    have hs := congrArg (fun f ↦ f.hom.app (op U) s) hu
    change e F ((Scheme.toProEt X).obj U) _ = _
    exact (congrArg (e F ((Scheme.toProEt X).obj U)) hs).trans (hunit F U s)

end AlgebraicGeometry
