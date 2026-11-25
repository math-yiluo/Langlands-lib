/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Reflection of exactness by ringed-slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8G
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Sheafification is injective on each single summand, by local injectivity of
its unit and separatedness of the original sheaf on the slice (Stacks 0E8G). -/
private theorem sheafification_single_injective
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) (U : C)
    (G : SheafOfModules.{max u v} (R.over U)) (V : C) [DecidableEq (V ⟶ U)] (φ : V ⟶ U)
    (x y : G.val.obj (Opposite.op (Over.mk φ)))
    (h : (toSheafify J ((extensionByZeroPresheaf R U).obj G).presheaf).app (Opposite.op V)
        (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      (toSheafify J ((extensionByZeroPresheaf R U).obj G).presheaf).app (Opposite.op V)
        (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y)) :
    x = y := by
  classical
  let P := ((extensionByZeroPresheaf R U).obj G).presheaf
  let S := Presheaf.equalizerSieve (F := P)
    (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x)
    (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y)
  have hS : S ∈ J V := Presheaf.equalizerSieve_mem J (toSheafify J P) _ _ h
  let T := (Sieve.overEquiv (Over.mk φ)).symm S
  have hT : T ∈ (J.over U) (Over.mk φ) :=
    J.overEquiv_symm_mem_over (Over.mk φ) S hS
  apply G.isSheaf.isSeparated (Over.mk φ) T hT
  intro B f hf
  obtain ⟨B, ψ, rfl⟩ := B.mk_surjective
  obtain ⟨b, hb, rfl⟩ := Over.homMk_surjective f
  change B ⟶ V at b
  change b ≫ φ = ψ at hb
  subst ψ
  have he : P.map b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
    P.map b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y) := hf
  change extensionByZeroPresheafRestrictAdd R U G b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
    extensionByZeroPresheafRestrictAdd R U G b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y) at he
  dsimp only [extensionByZeroPresheafRestrictAdd] at he
  erw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of] at he
  erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at he
  exact (DirectSum.of_injective
    (β := fun ψ : B ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) (b ≫ φ)) he

/-- The sheafified direct-sum extension from a ringed slice is faithful.

Source: Stacks Project, Modules on Sites, Tag 0E8G.
Proof: include each section in its indexed summand and use naturality of the
module sheafification unit. Equality of the extended maps gives equality of
the sheafified sections in that summand. The preceding local-injectivity
argument and separatedness of the original slice sheaf recover their equality. -/
private theorem ringedSliceExtension_faithful
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) (U : C) :
    (extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)).Faithful := by
  classical
  let P := extensionByZeroPresheaf.{max u v} R U
  let L := PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
  let Q := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj : L ⊣ Q := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  constructor
  intro G H f g hfg
  have hn : P.map f ≫ adj.unit.app (P.obj H) = P.map g ≫ adj.unit.app (P.obj H) := by
    calc
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map f)) :=
        (adj.unit_naturality (P.map f)).symm
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map g)) :=
        congrArg (fun t ↦ adj.unit.app (P.obj G) ≫ Q.map t) hfg
      _ = _ := adj.unit_naturality (P.map g)
  ext V s
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun t ↦ (PresheafOfModules.toPresheaf R.obj).map t) hn)
      (Opposite.op V.unop.left))
    (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) V.unop.hom s)
  apply sheafification_single_injective J R U H V.unop.left V.unop.hom
  change (toSheafify J (P.obj H).presheaf).app (Opposite.op V.unop.left)
      ((extensionByZeroPresheafHomApp R U f (Opposite.op V.unop.left)).hom
        (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ)))
          V.unop.hom s)) =
    (toSheafify J (P.obj H).presheaf).app (Opposite.op V.unop.left)
      ((extensionByZeroPresheafHomApp R U g (Opposite.op V.unop.left)).hom
        (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ)))
          V.unop.hom s)) at he
  dsimp only [extensionByZeroPresheafHomApp] at he
  erw [DirectSum.lmap_of, DirectSum.lmap_of] at he
  exact he

/-- Exactness after the sheafified direct-sum extension detects exactness on the slice.

Source: Stacks Project, Modules on Sites, Tag 0E8G
(auxiliary; not a blueprint node).

Proof: At (V, φ), inject a section of G into the φ summand of its direct-sum
extension and then sheafify. These maps commute with restrictions. If the
image is zero, the module and underlying-set sheafification comparisons and
local injectivity of the sheafification unit give a covering sieve on V
where the restricted direct-sum section is zero. Projecting to the φ-coordinate
after restriction shows that the original section vanishes on the corresponding
cover in the slice. Sheaf separatedness makes it zero. An empty covering sieve
also works: a sheaf has just one section there. Thus this natural unit is monic,
and L(G) = 0 implies G = 0.
The preservation theorem makes L exact. Factor S.f through ker S.g and let H
be the cokernel of this factorization. Exactness of L identifies L(H) with
the analogous quotient for the extended complex. The hypothesis makes that
quotient zero, so H = 0 by the monic unit. The factorization is therefore epic,
which is precisely S.Exact. Equivalently the monic natural unit makes L faithful,
and Mathlib's Functor.reflects_exact_of_faithful supplies the last step. -/
theorem ringedSliceExtension_reflects_exact
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (ringedSiteModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U)))
    (hS : let R := (sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
      let L := extensionByZeroPresheaf.{max u v} R U ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
      imageSubobject (L.map S.f) = kernelSubobject (L.map S.g)) :
    S.Exact := by
  classical
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
  let L := extensionByZeroPresheaf.{max u v} R U ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
  let : L.Faithful := by
    dsimp [L, R]
    exact ringedSliceExtension_faithful J R U
  let : (extensionByZeroPresheaf.{max u v} R U).PreservesZeroMorphisms := by
    constructor
    intro G H
    ext V s
    change (DirectSum.lmap (R := R.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ ((0 : G ⟶ H).val.app (Opposite.op (Over.mk φ))).hom)) s = 0
    induction s using DirectSum.induction_on with
    | zero => exact map_zero _
    | of φ x =>
      rw [DirectSum.lmap_of]
      change DirectSum.of (fun ψ : V.unop ⟶ U ↦ H.val.obj (Opposite.op (Over.mk ψ)))
        φ (0 : H.val.obj (Opposite.op (Over.mk φ))) = 0
      exact map_zero _
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have hmap : (S.map L).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    exact hS
  exact L.reflects_exact_of_faithful S hmap

end SheafOfModules
