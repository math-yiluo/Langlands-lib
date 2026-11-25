/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorPresentation
import WeilConjectures.RingTheory.FiniteMapColimitDescent

/-!
# Finiteness descent on an affine open over an affine base open

Source: Stacks Project, Limits, proof of Tag 01ZO, affine calculation, and Algebra,
Tag 07RG (blueprint: lem-weil-pbc-descend-finite-affine-base-piece).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine calculation in finiteness descent, with a common affine base open.

Source: Stacks Project, Limits, proof of Tag 01ZO, and Algebra, Tag 07RG
(blueprint: lem-weil-pbc-descend-finite-affine-base-piece).

Proof: Pull back the affine base open `W` to the upper tail above `k`. Affine
transitions make all these opens affine; their limit is the corresponding open of
`c.pt`, by open pullback pasting and the affine-transition limit theorem. Its
coordinate ring is the directed colimit of the stage coordinate rings, by the
Spec adjunction. The inverse image of `V` at `k` is affine, since its projection
to `V` is affine. Its inverse image under the assumed affine morphism at `k`
is affine too. Write their rings as `B` and `C`, over the ring `A` of the
pullback of `W` at `k`. Local finite type says that `B → C` is finite type.
Pullback pasting and the affine spectrum tensor-product isomorphism identify
later restrictions with Spec of `A_i ⊗ B → A_i ⊗ C`, compatibly with transition
maps; the limit restriction is the analogous map over `colim A_i`. Its
finiteness gives finiteness of that ring map. Tag 07RG gives finiteness at some
stage. Translate this back across the affine-spectrum comparison to obtain the
required finite restriction. This calculation works also when `V` or `W` is empty:
the corresponding coordinate rings are zero rings and the morphisms are finite.
-/
theorem exists_isFinite_morphismRestrict_baseChange_affine_base_piece
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans hkj)).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom (D.map (homOfLE (hk.trans hkj)).op)) ⁻¹ᵁ V)) := by
  classical
  have : IsDirected {i : I // k ≤ i} (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨l, i.property.trans hil⟩, hil, hjl⟩⟩
  obtain ⟨F, B, C, aB, aC, H⟩ :=
    exists_affine_base_piece_tensor_presentation D c hc i₀ k hk X₀ Y₀ f₀
      haffine V hV W hW hVW
  let : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
  let : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
  obtain ⟨φ, hft, ⟨elim⟩, estage⟩ := H
  let : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
  have hlim : (Algebra.TensorProduct.map
      (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).Finite := by
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)).mp
      ((MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) elim).mp hfinite)
  obtain ⟨j, hj, hjfin⟩ :=
    RingHom.exists_finite_tensorProductMap_of_colimit F ⟨k, le_rfl⟩ B C φ hft hlim
  let : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
    (CommRingCat.Hom.hom (F.map (homOfLE hj))).toAlgebra
  obtain ⟨e⟩ := estage j
  refine ⟨j.val, j.property, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj j)) φ).toRingHom)).mpr
    hjfin

end AlgebraicGeometry
