/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects
import WeilConjectures.AlgebraicGeometry.AffineEtaleFiniteDiagramArrows

/-!
# Finite affine étale diagram descent

Source: Stacks Project, Étale Cohomology 0EYL and Limits 01ZM.
(blueprint: lem-weil-pbc-affine-etale-finite-diagram-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL, qcqs case; Limits 01ZM,
01YZ, 01Z6, and 07RP.

Proof:
1. Each affine étale object is finitely presented over the qcqs limit. Descend its
   structure morphism by 01ZM. On the base-change tail, 01YZ identifies its limit
   with the original affine object. By 01Z6 a later model is affine, and by 07RP a
   still later model is étale. Affine and étale base change preserve these properties.
2. Do this for the target and the finitely many sources. Directedness supplies a
   common stage, including when there are no sources. The q-pullback squares give
   isomorphisms between their v-images and the original objects.
3. Conjugate each arrow by these isomorphisms. Apply 01ZM(2) to descend each arrow
   between the finitely presented models, and choose a common later stage.
   The q-pullback squares identify their v-images with the resulting base changes.
   Pullback uniqueness and naturality of q give the displayed arrow equalities.
   No surjectivity is asserted or used.
(blueprint: lem-weil-pbc-affine-etale-finite-diagram-descent). -/
theorem affineEtale_finite_diagram_descent
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
    (h2 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))))
    : ∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
          (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
          (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
          ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a := by
  classical
  intro n A B f
  let X : Fin (n + 1) → c.pt.FullAffineEtale := Fin.cases A B
  obtain ⟨i, Xi, hXi⟩ := affineEtale_common_models D c hc (n + 1) X
  have he : ∀ a : Fin (n + 1), Nonempty ((v i).obj (Xi a) ≅ X a) := by
    intro a
    obtain ⟨r, hr⟩ := hXi a
    let e := (h2 i (Xi a)).isoPullback ≪≫ hr.isoPullback.symm
    refine ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk e ?_)⟩
    change ((h2 i (Xi a)).isoPullback.hom ≫ hr.isoPullback.inv) ≫
      (X a).obj.hom = ((v i).obj (Xi a)).obj.hom
    rw [Category.assoc, hr.isoPullback_inv_snd, (h2 i (Xi a)).isoPullback_hom_snd]
  let e := fun a ↦ Classical.choice (he a)
  let Ai := Xi 0
  let Bi : Fin n → (D.obj (op i)).FullAffineEtale := fun a ↦ Xi a.succ
  let t : (v i).obj Ai ≅ A := e 0
  let s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a := fun a ↦ e a.succ
  let g : ∀ a : Fin n, (v i).obj (Bi a) ⟶ (v i).obj Ai :=
    fun a ↦ (s a).hom ≫ f a ≫ t.inv
  obtain ⟨j, _, Aj, Bj, fi, _, _, _, _, t', s', heq⟩ :=
    affineEtale_model_arrows D c hc v q h2 i n Ai Bi g
  refine ⟨j, Aj, Bj, fi, t' ≪≫ t, (fun a ↦ s' a ≪≫ s a), ?_⟩
  intro a
  change (v j).map (fi a) ≫ t'.hom ≫ t.hom =
    (s' a).hom ≫ (s a).hom ≫ f a
  rw [← Category.assoc, heq a]
  simp [g, Category.assoc]


end AlgebraicGeometry.Scheme
