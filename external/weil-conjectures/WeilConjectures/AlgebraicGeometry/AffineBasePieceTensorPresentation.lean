/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.AffineOpenDirectedRingSystem
import WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorComparison

/-!
# Tensor-product presentation of an affine base piece

Source: Stacks Project, Limits, proof of Tag 01ZO, the affine reduction, with
Tags 01YX and 01YW (blueprint: lem-weil-pbc-affine-base-piece-tensor-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Present all base changes of an affine piece by one finite type algebra map.

Source: Stacks Project, Limits, proof of Tag 01ZO, affine reduction, and
Tags 01YX and 01YW (blueprint: lem-weil-pbc-affine-base-piece-tensor-presentation).

Proof: On the directed upper tail above `k`, pull back `W` along every transition
to the initial stage. These are affine because the transitions are affine. Use
their coordinate rings for `F`, with transition maps induced by pullback of
sections. Restrict the limiting cone to this tail and to these base opens.
Open pullback pasting and the limit universal property identify its limit with
the inverse image of `W` in `c.pt`. The Spec adjunction identifies this affine
limit with Spec of `colimit F`, compatibly with the projection to the `k`-th
base open. Put `B = Γ(V_k)` and `C = Γ(f_k⁻¹(V_k))`. Both are affine: the
projection to `V` is affine, and `f_k` is affine. The map `φ : B → C` induced
by the restriction is finite type, by base change, restriction, and the affine
criterion for local finite type. The inclusion `V_k → W_k` and its composite
with this restriction give `aB` and `aC`, and commutativity gives the algebra
map `φ`. For every later index, paste the original pullback squares and the
open restriction squares to identify its restriction with the base change of
`f_k|V_k` along `W_j → W_k`. The affine-spectrum pullback isomorphisms give
Spec of `id ⊗ φ` on source and target. Their compatibility with the morphism
follows by equality of both pullback projections. The same construction using
the affine limit comparison gives the displayed arrow isomorphism at the
limit. These constructions include empty opens, whose rings are zero rings;
no nonemptiness of an open or quasi-separatedness of the original base is used.
-/
theorem exists_affine_base_piece_tensor_presentation
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
    : ∃ (F : {i : I // k ≤ i} ⥤ CommRingCat.{u})
      (B C : CommRingCat.{u})
      (aB : F.obj ⟨k, le_rfl⟩ →+* B) (aC : F.obj ⟨k, le_rfl⟩ →+* C),
      letI : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
      letI : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
      ∃ φ : B →ₐ[F.obj ⟨k, le_rfl⟩] C, φ.FiniteType ∧
        (letI : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
          (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
        Nonempty
          (Arrow.mk
            ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V)) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map
                (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)))) ∧
        (∀ j : {i : I // k ≤ i},
          letI : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
            (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
          Nonempty
            (Arrow.mk
              ((((Over.pullback (D.map (homOfLE (hk.trans j.property)).op)).map f₀).left)
                ∣_ ((pullback.fst Y₀.hom
                  (D.map (homOfLE (hk.trans j.property)).op)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map
                  (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj j)) φ).toRingHom)))) := by
  let d := D.map (homOfLE hk).op
  have hWk : IsAffineOpen (d ⁻¹ᵁ W) := hW.preimage d
  obtain ⟨F, e0, hi, eL, hL⟩ :=
    exists_affineOpen_ringSystem_of_isLimit D c hc k (d ⁻¹ᵁ W) hWk
  obtain ⟨B, C, aB, aC, φ, hφ, hcomp⟩ :=
    exists_affine_base_piece_tensor_comparison d X₀ Y₀ f₀ haffine V hV W hVW
      (F.obj ⟨k, le_rfl⟩) e0
  let := aB.toAlgebra
  let := aC.toAlgebra
  refine ⟨F, B, C, aB, aC, φ, hφ, ?_, ?_⟩
  · let aL : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
    have h := hcomp c.pt (c.π.app (op k)) (colimit F) aL eL hL
    have heq : c.π.app (op k) ≫ d = c.π.app (op i₀) :=
      c.w (homOfLE hk).op
    rw [heq] at h
    exact h
  · intro j
    let aj : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
      (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
    obtain ⟨ej, hej⟩ := hi j
    have h := hcomp (D.obj (op j.val)) (D.map (homOfLE j.property).op)
      (F.obj j) aj ej hej
    have heq : D.map (homOfLE j.property).op ≫ d =
        D.map (homOfLE (hk.trans j.property)).op := by
      rw [← D.map_comp]
      congr 1
    rw [heq] at h
    exact h

end AlgebraicGeometry
