/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.CompactCoproductFiniteThickSupport
import WeilConjectures.CategoryTheory.CompactObjectsThick

/-!
# Finite thick approximation of a connecting component

Source: Stacks Project, Derived Categories, Tag 09SP, with the stage notation of
Tag 09SN (blueprint: lem-sc-compact-triangle-connecting-approximation).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Approximate the connecting component across one distinguished triangle by a finite
thick object. Source: Stacks Project, Derived Categories, Tag 09SP, induction step
up to (but excluding) the exactness correction.
(blueprint: lem-sc-compact-triangle-connecting-approximation).

Proof: factor the connecting map from K into Z[1] through F[1], with F a finite
sum of shifts of generators, using compactness and preservation of coproducts by
shift. Complete K → F[1] to a distinguished triangle F → K' → K → F[1].
The triangle axiom supplies a morphism to Z → Y → W → Z[1]. The object K'
is compact because F and K are compact, and compact objects are closed under
shifts, finite sums and distinguished triangles (Stacks, Tag 09QH):
shifts preserve coproducts, finite sums interchange with the compact-Hom comparison,
and for a distinguished triangle the comparison maps form a morphism of exact
five-term Hom sequences. Direct sums of abelian groups preserve exactness; the
four comparisons for the two compact terms and their shifts are bijective, so the
five lemma makes the comparison for the third term bijective. Apply the factorization
property of Y to K' → Y. Complete F → K' → Q' to a triangle F → Q' → Q → F[1].
The triangle axiom gives maps K → Q → W whose composite has the same connecting
component as f. Taking the union of the finite generator sets puts F and Q' in
one finite thick envelope; closure under cones puts Q there as well.
This only identifies connecting components: the difference from f can be nonzero
and must still be lifted to Y and factored separately. -/
theorem compact_triangle_connecting_approximation
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    {I : Type w} (E : I → C) (hcompact : ∀ i : I, IsCompactObject (E i))
    (T : Triangle C) (hT : T ∈ distTriang C)
    (hZ : ∃ (J : Type w) (i : J → I) (m : J → ℤ),
      Nonempty (T.obj₁ ≅ ∐ fun j : J ↦ (E (i j))⟦m j⟧))
    (hY : ∀ (K : C), IsCompactObject K → ∀ (f : K ⟶ T.obj₂),
      ∃ (S : Finset I) (Q : C) (a : K ⟶ Q) (b : Q ⟶ T.obj₂),
        (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope Q ∧
          a ≫ b = f)
    (K : C) (hK : IsCompactObject K) (f : K ⟶ T.obj₃) :
    ∃ (S : Finset I) (Q : C) (a : K ⟶ Q) (b : Q ⟶ T.obj₃),
      (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope Q ∧
        (a ≫ b) ≫ T.mor₃ = f ≫ T.mor₃ := by
  classical
  let R : ObjectProperty C := fun K ↦ IsCompactObject K
  obtain ⟨hRtri, hRret⟩ := compactObjects_isThick (C := C)
  let : R.IsTriangulated := hRtri
  let : R.IsStableUnderRetracts := hRret
  obtain ⟨J, i, m, ⟨e⟩⟩ := hZ
  let e' : T.obj₁⟦(1 : ℤ)⟧ ≅ ∐ fun j : J ↦ (E (i j))⟦m j + 1⟧ :=
    (shiftFunctor C (1 : ℤ)).mapIso e ≪≫
      (asIso (sigmaComparison (shiftFunctor C (1 : ℤ))
        (fun j : J ↦ (E (i j))⟦m j⟧))).symm ≪≫
      Sigma.mapIso (fun j ↦ ((shiftFunctorAdd C (m j) (1 : ℤ)).app (E (i j))).symm)
  obtain ⟨S, Q₀, α, β, hQ₀, hαβ⟩ :=
    compact_coproduct_finite_thick_support E i (fun j ↦ m j + 1) K hK
      (f ≫ T.mor₃ ≫ e'.hom)
  let P := (ObjectProperty.singleton
    (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope
  have hPR : P ≤ R := by
    refine (ObjectProperty.triangEnvelope_le_iff
      (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val))
      (Q := R)).mpr ?_
    refine ObjectProperty.singleton_le_iff.mpr ?_
    let A := fun i : {i : I // i ∈ S} ↦ E i.val
    apply R.prop_of_iso ((biproduct.isoCoproduct A).symm ≪≫ biproduct.isoProduct A).symm
    exact R.prop_product (fun i ↦ hcompact i.val)
  let F := Q₀⟦(-1 : ℤ)⟧
  let eF : F⟦(1 : ℤ)⟧ ≅ Q₀ := (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by decide)).app Q₀
  let g : K ⟶ F⟦(1 : ℤ)⟧ := α ≫ eF.inv
  let d : F⟦(1 : ℤ)⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧ := eF.hom ≫ β ≫ e'.inv
  let a₀ : F ⟶ T.obj₁ := (shiftFunctor C (1 : ℤ)).preimage d
  have hgd : g ≫ a₀⟦(1 : ℤ)⟧' = f ≫ T.mor₃ := by
    rw [Functor.map_preimage]
    dsimp [g, d]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hαβ]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hF : P F := P.le_shift (-1 : ℤ) _ hQ₀
  obtain ⟨K', p, q, hTK⟩ := distinguished_cocone_triangle₂ g
  let TK := Triangle.mk p q g
  have hK' : IsCompactObject K' :=
    R.ext_of_isTriangulatedClosed₂ TK hTK (hPR F hF) hK
  obtain ⟨b₀, hp, hq⟩ := complete_distinguished_triangle_morphism₂ TK T hTK hT a₀ f hgd
  obtain ⟨S', Q', α', β', hQ', hα'β'⟩ := hY K' hK' b₀
  obtain ⟨Q, b₁, c₁, hTQ⟩ := distinguished_cocone_triangle (p ≫ α')
  let TQ := Triangle.mk (p ≫ α') b₁ c₁
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism TK TQ hTK hTQ
    (𝟙 F) α' (by
      change p ≫ α' = 𝟙 F ≫ (p ≫ α')
      rw [Category.id_comp])
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism TQ T hTQ hT
    a₀ β' (by
      change (p ≫ α') ≫ β' = a₀ ≫ T.mor₁
      rw [Category.assoc, hα'β']
      exact hp)
  let U := S ∪ S'
  let PU := (ObjectProperty.singleton
    (∐ fun i : {i : I // i ∈ U} ↦ E i.val)).triangEnvelope
  have hFU : PU F := finite_thick_mono E Finset.subset_union_left F hF
  have hQ'U : PU Q' := finite_thick_mono E Finset.subset_union_right Q' hQ'
  have hQ : PU Q := PU.ext_of_isTriangulatedClosed₃ TQ hTQ hFU hQ'U
  refine ⟨U, Q, a, b, hQ, ?_⟩
  rw [Category.assoc, ← hb₂, ← Category.assoc, ← ha₂]
  change (g ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 F)) ≫ a₀⟦(1 : ℤ)⟧' = f ≫ T.mor₃
  simpa only [Functor.map_id, Category.comp_id] using hgd

end CategoryTheory
