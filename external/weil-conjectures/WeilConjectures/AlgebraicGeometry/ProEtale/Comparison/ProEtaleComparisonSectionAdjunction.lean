/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonSectionUnitUniversal

/-! # The adjunction for the section-valued comparison sheaf

## References

* Stacks Project, Tag 0GLZ (the adjunction construction and final paragraph)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A functor `A` whose sections over `Y` are naturally the terminal sections of the étale
pullback of `F` to `Y` is left adjoint to restriction along `toProEt X`, with unit given on
étale `U` by the diagonal section. -/
theorem proEtaleComparisonSectionAdjunction (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s))
    : ∃ adj : A ⊣ (Scheme.toProEt X).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X),
    ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (U : X.Etale) (s : F.obj.obj (op U)),
      letI : (MorphismProperty.Over.pullback @Etale ⊤ U.hom).IsContinuous
          (X.smallGrothendieckTopology @Etale)
          (U.left.smallGrothendieckTopology @Etale) :=
        Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.hom
      e F ((Scheme.toProEt X).obj U)
        ((adj.unit.app F).hom.app (op U) s) =
        ((Scheme.etaleSetPullback U.hom).obj F).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) (by simp) :
            Scheme.Etale.mk (𝟙 U.left) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj U).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ U.hom) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s) := by
  let R := (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let η := proEtaleComparisonSectionUnit X A e hres hfun
  let E (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :=
    Equiv.ofBijective (fun f : A.obj F ⟶ G ↦ η.app F ≫ R.map f)
      (proEtaleComparisonSectionUnit_bijective X A e hres hfun F G)
  let h : Adjunction.CoreHomEquiv A R := {
    homEquiv := E
    homEquiv_naturality_left_symm := by
      intro F' F G f g
      apply (E F' G).injective
      erw [Equiv.apply_symm_apply]
      change f ≫ g = η.app F' ≫ R.map (A.map f ≫ (E F G).symm g)
      have hn : f ≫ η.app F = η.app F' ≫ R.map (A.map f) := η.naturality f
      rw [R.map_comp, ← Category.assoc, ← hn, Category.assoc]
      change f ≫ g = f ≫ (E F G) ((E F G).symm g)
      erw [Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro F G G' f g
      change η.app F ≫ R.map (f ≫ g) = (η.app F ≫ R.map f) ≫ R.map g
      rw [R.map_comp, Category.assoc]
  }
  let adj := Adjunction.mkOfHomEquiv h
  refine ⟨adj, ?_⟩
  intro F U s
  have hu : adj.unit.app F = η.app F := by
    change η.app F ≫ R.map (𝟙 (A.obj F)) = η.app F
    rw [R.map_id]
    exact Category.comp_id _
  rw [hu]
  change e F ((Scheme.toProEt X).obj U)
    ((e F ((Scheme.toProEt X).obj U)).symm
      _) = _
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry
