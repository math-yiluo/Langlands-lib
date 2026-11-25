/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Constant coefficients and the inverse-image unit

Source: Stacks Project, Tag 03Q1 (2), (4), and Tag 0A5G.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The constant-sheaf pullback comparison sends the adjunction unit to composition
with the first projection, in the description of constant sheaves by continuous maps.
Source: Stacks Project Tags 03Q1 (2), (4), and 0A5G.
(blueprint: theorem-finite-etale-covers-proper-henselian--3)

Proof: Construct the natural transformation from the constant sheaf on Y to the
pushforward of the continuous-map sheaf on Y₀ by composition with the first
projection. Apply the constant-sheaf adjunction on Y and then the terminal-object
comparison for pushforward. On a constant m, its value is the constant function m,
by the unit identity for the continuous-map comparison. The same calculation on Y₀
computes the adjunct of that comparison. Uniqueness of the left adjoint identifies
the two adjuncts, and injectivity of the adjunction Hom equivalence gives equality
of the sheaf morphisms. Evaluation at W and g gives the claimed formula. This uses
no finiteness hypothesis on M. Empty objects and the trivial group are covered by
the same constant-function calculation. -/
theorem constant_pullback_unit_continuousMap
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M]
    (W : Y.Etale)
    (g : ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)).obj.obj (op W)) :
    (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y₀ M).hom.hom.app
      (op (i.Etale.obj W))
      (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
        (AddCommGrpCat.of M)).hom.hom.app (op (i.Etale.obj W))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of M))).hom.app (op W) g)) =
      ((Scheme.Etale.constantSheafIsoContinuousMapSheaf Y M).hom.hom.app (op W) g).comp
        (pullback.fst W.hom i).base.hom := by
  classical
  let A := AddCommGrpCat.{u + 1}
  let F := i.Etale
  let G := (constantSheaf Y.smallEtaleTopology A).obj (AddCommGrpCat.of M)
  let CM₀ := Scheme.Etale.continuousMapSheaf Y₀ M
  let cs := (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y M).hom
  let cs₀ := (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y₀ M).hom
  let c := (Scheme.upperStarConstantSheafIso A i).app (AddCommGrpCat.of M)
  let adj := upperStarLowerStarAdjunction A i
  let adjY := constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal
  let adj₀ := constantSheafAdj Y₀.smallEtaleTopology A terminalIsTerminal
  let ψ := lowerStarCompSheafSectionsTerminalIso A i
  let adjT := (adjY.comp adj).ofNatIsoRight ψ
  let κ : G ⟶ (lowerStar A i).obj CM₀ := ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun := fun s ↦ (cs.hom.app V s).comp (pullback.fst V.unop.hom i).base.hom
      map_zero' := by ext z; simp
      map_add' := by
        intro s t
        ext z
        change (show C(V.unop.left, M) from cs.hom.app V (s + t)).toFun _ = _
        rw [map_add]
        rfl }
    naturality V U a := by
      ext s
      apply ContinuousMap.ext
      intro z
      have hn := ConcreteCategory.congr_hom (cs.hom.naturality a) s
      simp only [ConcreteCategory.comp_apply] at hn
      change (show C(U.unop.left, M) from cs.hom.app U (G.obj.map a s)).toFun _ =
        (show C(V.unop.left, M) from cs.hom.app V s).toFun
          ((pullback.fst V.unop.hom i) ((F.map a.unop).left z))
      rw [hn]
      change (show C(V.unop.left, M) from cs.hom.app V s).toFun
        (a.unop.left ((pullback.fst U.unop.hom i) z)) = _
      congr 1
      exact (congrArg (fun h ↦ h z) (i.etale_map_left_comp_fst a.unop)).symm }⟩
  have huniq : adjT.homEquiv _ _ c.hom = adj₀.unit.app (AddCommGrpCat.of M) := by
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app adjT adj₀ _
  have hcomp : adjT.homEquiv _ _ (c.hom ≫ cs₀) = adj₀.homEquiv _ _ cs₀ := by
    rw [adjT.homEquiv_naturality_right, huniq, adj₀.homEquiv_unit]
  have hκ : adjY.homEquiv _ _ κ ≫ ψ.hom.app CM₀ = adj₀.homEquiv _ _ cs₀ := by
    dsimp only [adjY, adj₀]
    simp only [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app]
    ext m
    apply ContinuousMap.ext
    intro z
    have hY := congrArg (fun η ↦ η.app (op (⊤_ Y.Etale)) m)
      (Scheme.Etale.toSheafify_constantSheafToContinuousMapSheaf Y M)
    have h₀ := congrArg (fun η ↦ η.app (op (⊤_ Y₀.Etale)) m)
      (Scheme.Etale.toSheafify_constantSheafToContinuousMapSheaf Y₀ M)
    change cs.hom.app (op (⊤_ Y.Etale))
      ((toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of M))).app (op (⊤_ Y.Etale)) m) =
        ContinuousMap.const _ m at hY
    change cs₀.hom.app (op (⊤_ Y₀.Etale))
      ((toSheafify Y₀.smallEtaleTopology
        ((Functor.const Y₀.Etaleᵒᵖ).obj (AddCommGrpCat.of M))).app (op (⊤_ Y₀.Etale)) m) =
        ContinuousMap.const _ m at h₀
    have hy := congrArg (fun f : C((⊤_ Y.Etale).left, M) ↦
      CM₀.obj.map (PreservesTerminal.iso i.Etale).op.inv
        (f.comp (pullback.fst (⊤_ Y.Etale).hom i).base.hom)) hY
    exact (congrArg (fun f : C((⊤_ Y₀.Etale).left, M) ↦ f z) hy).trans
      (congrArg (fun f : C((⊤_ Y₀.Etale).left, M) ↦ f z) h₀).symm
  have h : κ = adj.homEquiv _ _ (c.hom ≫ cs₀) := by
    apply (adjY.homEquiv _ _).injective
    apply (cancel_mono (ψ.hom.app CM₀)).mp
    rw [hκ]
    rw [← hcomp]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    rfl
  have hh := congrArg (fun k ↦ k.hom.app (op W) g) h
  simp only [adj.homEquiv_unit] at hh
  exact hh.symm

end AlgebraicGeometry.Etale
