/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyInjective
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
/-- The extension-by-zero/sheafification functor is faithful.
Source: Stacks Project, Sheaves Lemma 00A7 (4).
Proof: the extension presheaf is separated. On an open admitting a map to W,
there is only one summand, and separation is separation of the input sheaf;
on any other open the direct sum is zero. The sheafification unit is locally
injective, hence injective for this separated presheaf. Naturality of this unit
therefore reflects equality of extended morphisms back to presheaf morphisms.
Evaluating on the unique summand recovers the input morphism.
(blueprint: lem-sc-module-extension-by-zero-unit-mono-faithful-aux) -/
theorem extensionByZero_faithful (X : RingedSpace.{u}) (W : Opens X) :
    (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).Faithful := by
  classical
  let R := moduleRings X
  let P := SheafOfModules.extensionByZeroPresheaf.{u} R W
  let J := Opens.grothendieckTopology X
  have hsep (G : SheafOfModules.{u} (R.over W)) :
      Presieve.IsSeparated J ((P.obj G).presheaf ⋙ forget AddCommGrpCat.{u}) := by
    intro V S hS a x y hx hy
    change DirectSum (V ⟶ W) (fun ψ => G.val.obj (op (Over.mk ψ))) at x y
    apply DirectSum.ext
    intro φ
    let T := (Sieve.overEquiv (Over.mk φ)).symm S
    have hT : T ∈ (J.over W) (Over.mk φ) := by
      exact J.overEquiv_symm_mem_over (Over.mk φ) S hS
    apply G.isSheaf.isSeparated (Over.mk φ) T hT
    intro B f hf
    obtain ⟨B, ψ, rfl⟩ := B.mk_surjective
    obtain ⟨b, h, rfl⟩ := Over.homMk_surjective f
    change B ⟶ V at b
    change b ≫ φ = ψ at h
    subst ψ
    let : DecidableEq (B ⟶ W) := Classical.decEq _
    have hxy := (hx b hf).trans (hy b hf).symm
    have ex (z : DirectSum (V ⟶ W)
        (fun ψ => G.val.obj (op (Over.mk ψ)))) :
        z = DirectSum.of (fun ψ : V ⟶ W => G.val.obj (op (Over.mk ψ))) φ (z φ) := by
      apply DirectSum.ext
      intro ψ
      have he : ψ = φ := Subsingleton.elim _ _
      subst ψ
      simp only [DirectSum.of_eq_same]
    change SheafOfModules.extensionByZeroPresheafRestrictAdd R W G b.op x =
      SheafOfModules.extensionByZeroPresheafRestrictAdd R W G b.op y at hxy
    rw [ex x, ex y] at hxy
    dsimp only [SheafOfModules.extensionByZeroPresheafRestrictAdd] at hxy
    erw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of] at hxy
    erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at hxy
    have hi := (DirectSum.of_injective
      (β := fun ψ : B ⟶ W => G.val.obj (op (Over.mk ψ))) (b ≫ φ)) hxy
    convert hi using 1 <;> rfl
  constructor
  intro G H f g hfg
  let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let Q := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj : L ⊣ Q := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have hi := (Presheaf.isLocallyInjective_iff_injective_of_separated J
    (toSheafify J (P.obj H).presheaf) (hsep H)).mp inferInstance
  have hn : P.map f ≫ adj.unit.app (P.obj H) = P.map g ≫ adj.unit.app (P.obj H) := by
    calc
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map f)) :=
        (adj.unit_naturality (P.map f)).symm
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map g)) :=
        congrArg (fun t => adj.unit.app (P.obj G) ≫ Q.map t) hfg
      _ = _ := adj.unit_naturality (P.map g)
  have hp : P.map f = P.map g := by
    ext V s
    apply hi V
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun t => (PresheafOfModules.toPresheaf R.obj).map t) hn) V) s
  ext V s
  have he := congrArg (fun t => (t.app (op V.unop.left)).hom
    (DirectSum.of (fun ψ : V.unop.left ⟶ W => G.val.obj (op (Over.mk ψ)))
      V.unop.hom s)) hp
  dsimp [P, SheafOfModules.extensionByZeroPresheaf, SheafOfModules.extensionByZeroPresheafHom,
    SheafOfModules.extensionByZeroPresheafHomApp] at he
  erw [DirectSum.lmap_of, DirectSum.lmap_of] at he
  exact (DirectSum.of_injective
    (β := fun φ : V.unop.left ⟶ W => H.val.obj (op (Over.mk φ))) V.unop.hom) he
end AlgebraicGeometry
