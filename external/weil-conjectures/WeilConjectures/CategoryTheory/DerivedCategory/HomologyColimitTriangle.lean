/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Colimits of homology along a functor of distinguished triangles

Let `𝒜` be an abelian category in which colimits of shape `I` exist and are exact.
Let `T : C' ⥤ Triangle (DerivedCategory 𝒜)` be a functor whose values are distinguished
triangles, `B : I ⥤ C'` and `c : Cocone B`. If, in every degree, the homology functors send
the images of `c` under two of the three projections `Triangle.π₁`, `Triangle.π₂`,
`Triangle.π₃` to colimit cocones, then the same holds for the third projection.

This is a "five lemma for colimits": the long exact homology sequences of the triangles
`T.obj X` assemble into a functor `C' ⥤ ComposableArrows 𝒜 5`; the colimit of the
sequences over `I` is exact because colimits of shape `I` are exact, and the comparison
morphism to the sequence at `c.pt` is an isomorphism by the five lemma.

## Main results

* `ComposableArrows.nonempty_isColimit_mapCocone_evaluation`: the general five lemma for
  colimits of exact sequences.
* `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₁`,
  `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₂`,
  `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₃`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]

namespace ComposableArrows

/-- The pointwise colimit of a diagram of exact sequences is exact when colimits of the
given shape are exact. -/
lemma exact_flip_comp_colim {J : Type*} [Category* J] [HasColimitsOfShape J A]
    [HasExactColimitsOfShape J A] {n : ℕ} (G : J ⥤ ComposableArrows A n)
    (hG : ∀ j, (G.obj j).Exact) : ComposableArrows.Exact (G.flip ⋙ colim) := by
  have hc : ComposableArrows.IsComplex G.flip :=
    ⟨fun i hi => by
      ext j
      exact (hG j).toIsComplex.zero i hi⟩
  have h (i : ℕ) (hi : i + 2 ≤ n) : (ComposableArrows.sc G.flip hc i hi).Exact :=
    (ShortComplex.exact_iff_evaluation _).2 fun j => (hG j).exact i hi
  exact ⟨⟨fun i hi => ((ComposableArrows.sc G.flip hc i hi).map colim).zero⟩,
    fun i hi => (h i hi).map colim⟩

/-- Five lemma for colimits: let `S : C' ⥤ ComposableArrows A n` be a functor with exact
values, `B : I ⥤ C'` and `c : Cocone B`, where colimits of shape `I` in `A` are exact.
If the evaluations of `S` at `k`, `k + 1`, `k + 3`, `k + 4` send `c` to colimit cocones,
then so does the evaluation at `k + 2`. -/
lemma nonempty_isColimit_mapCocone_evaluation {C' I : Type*} [Category* C'] [Category* I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] {n : ℕ}
    (S : C' ⥤ ComposableArrows A n) (hS : ∀ X, (S.obj X).Exact) {B : I ⥤ C'} (c : Cocone B)
    (k : ℕ) (hk : k + 4 ≤ n)
    (h₀ : Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj ⟨k, by lia⟩).mapCocone c)))
    (h₁ : Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj ⟨k + 1, by lia⟩).mapCocone c)))
    (h₃ : Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj ⟨k + 3, by lia⟩).mapCocone c)))
    (h₄ : Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj ⟨k + 4, by lia⟩).mapCocone c))) :
    Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj ⟨k + 2, by lia⟩).mapCocone c)) := by
  let φ : (B ⋙ S).flip ⋙ colim (J := I) ⟶ S.obj c.pt :=
    { app i := colimit.desc ((B ⋙ S).flip.obj i) ((S ⋙ (evaluation _ A).obj i).mapCocone c)
      naturality i i' f := colimit.hom_ext fun j => by simp }
  have hφ (i : Fin (n + 1)) :
      Nonempty (IsColimit ((S ⋙ (evaluation _ A).obj i).mapCocone c)) ↔ IsIso (φ.app i) :=
    (colimit.isColimit ((B ⋙ S).flip.obj i)).nonempty_isColimit_iff_isIso_desc
  rw [hφ] at h₀ h₁ h₃ h₄ ⊢
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' hk
    (exact_flip_comp_colim (B ⋙ S) fun j => hS _) (hS c.pt) φ k (k + 1) (k + 2) (k + 3) (k + 4)
    rfl rfl rfl rfl rfl inferInstance h₁ h₃ inferInstance

end ComposableArrows

end CategoryTheory

namespace DerivedCategory

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {C' : Type*} [Category* C']

/-- The six-term homology sequence of `T.obj X`, functorial in `X : C'`. -/
noncomputable def homologySequenceComposableArrows₅Functor
    (T : C' ⥤ Triangle (DerivedCategory 𝒜)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    C' ⥤ ComposableArrows 𝒜 5 where
  obj X := (homologyFunctor 𝒜 0).homologySequenceComposableArrows₅ (T.obj X) n₀ n₁ h
  map f := ComposableArrows.homMk₅
    (((homologyFunctor 𝒜 0).shift n₀).map (T.map f).hom₁)
    (((homologyFunctor 𝒜 0).shift n₀).map (T.map f).hom₂)
    (((homologyFunctor 𝒜 0).shift n₀).map (T.map f).hom₃)
    (((homologyFunctor 𝒜 0).shift n₁).map (T.map f).hom₁)
    (((homologyFunctor 𝒜 0).shift n₁).map (T.map f).hom₂)
    (((homologyFunctor 𝒜 0).shift n₁).map (T.map f).hom₃)
    ((CommSq.mk (T.map f).comm₁).map ((homologyFunctor 𝒜 0).shift n₀)).w
    ((CommSq.mk (T.map f).comm₂).map ((homologyFunctor 𝒜 0).shift n₀)).w
    ((homologyFunctor 𝒜 0).homologySequenceδ_naturality (T.map f) n₀ n₁ h).symm
    ((CommSq.mk (T.map f).comm₁).map ((homologyFunctor 𝒜 0).shift n₁)).w
    ((CommSq.mk (T.map f).comm₂).map ((homologyFunctor 𝒜 0).shift n₁)).w
  map_id X := by
    refine ComposableArrows.hom_ext₅ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  map_comp f g := by
    refine ComposableArrows.hom_ext₅ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

lemma homologySequenceComposableArrows₅Functor_obj_exact
    (T : C' ⥤ Triangle (DerivedCategory 𝒜)) (hT : ∀ X, T.obj X ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C') :
    ((homologySequenceComposableArrows₅Functor T n₀ n₁ h).obj X).Exact :=
  (homologyFunctor 𝒜 0).homologySequenceComposableArrows₅_exact _ (hT X) n₀ n₁ h

variable {I : Type*} [Category* I] [HasColimitsOfShape I 𝒜] [HasExactColimitsOfShape I 𝒜]

/-- If the homology functors send the images of `c` under `π₁` and `π₂` to colimit
cocones in all degrees, the same holds for `π₃`. -/
theorem nonempty_isColimit_homologyFunctor_mapCocone_π₃
    (T : C' ⥤ Triangle (DerivedCategory 𝒜)) (hT : ∀ X, T.obj X ∈ distTriang _)
    {B : I ⥤ C'} (c : Cocone B)
    (h₁ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₁).mapCocone c))))
    (h₂ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₂).mapCocone c)))) (n : ℤ) :
    Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone ((T ⋙ Triangle.π₃).mapCocone c))) :=
  ComposableArrows.nonempty_isColimit_mapCocone_evaluation
    (homologySequenceComposableArrows₅Functor T n (n + 1) rfl)
    (homologySequenceComposableArrows₅Functor_obj_exact T hT n (n + 1) rfl) c 0 (by lia)
    (h₁ n) (h₂ n) (h₁ (n + 1)) (h₂ (n + 1))

/-- If the homology functors send the images of `c` under `π₂` and `π₃` to colimit
cocones in all degrees, the same holds for `π₁`. -/
theorem nonempty_isColimit_homologyFunctor_mapCocone_π₁
    (T : C' ⥤ Triangle (DerivedCategory 𝒜)) (hT : ∀ X, T.obj X ∈ distTriang _)
    {B : I ⥤ C'} (c : Cocone B)
    (h₂ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₂).mapCocone c))))
    (h₃ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₃).mapCocone c)))) (n : ℤ) :
    Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone ((T ⋙ Triangle.π₁).mapCocone c))) :=
  ComposableArrows.nonempty_isColimit_mapCocone_evaluation
    (homologySequenceComposableArrows₅Functor T (n - 1) n (by lia))
    (homologySequenceComposableArrows₅Functor_obj_exact T hT (n - 1) n (by lia)) c 1 (by lia)
    (h₂ (n - 1)) (h₃ (n - 1)) (h₂ n) (h₃ n)

/-- If the homology functors send the images of `c` under `π₁` and `π₃` to colimit
cocones in all degrees, the same holds for `π₂`. This follows from the case of `π₁`
applied to the rotated triangles. -/
theorem nonempty_isColimit_homologyFunctor_mapCocone_π₂
    (T : C' ⥤ Triangle (DerivedCategory 𝒜)) (hT : ∀ X, T.obj X ∈ distTriang _)
    {B : I ⥤ C'} (c : Cocone B)
    (h₁ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₁).mapCocone c))))
    (h₃ : ∀ n, Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone
      ((T ⋙ Triangle.π₃).mapCocone c)))) (n : ℤ) :
    Nonempty (IsColimit ((homologyFunctor 𝒜 n).mapCocone ((T ⋙ Triangle.π₂).mapCocone c))) :=
  nonempty_isColimit_homologyFunctor_mapCocone_π₁ (T ⋙ rotate _)
    (fun X => rot_of_distTriang _ (hT X)) c h₃
    (fun m => (h₁ (m + 1)).map fun hc => by
      exact IsColimit.mapCoconeEquiv (c := (T ⋙ Triangle.π₁).mapCocone c)
        ((homologyFunctor 𝒜 0).shiftIso 1 m (m + 1) (by lia)).symm hc) n

end DerivedCategory
