/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Affine weakly contractible pro-etale hypercovers

Source: Stacks Project, proetale.tex, Tag 09A1, clause (2); sites.tex, Tags 090K, 090L
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- A qcqs object of the small pro-etale site has a hypercover with affine weakly
contractible terms. Source: Stacks Project, Tag 09A1 (2), and Tags 090K, 090L
(auxiliary; not a blueprint node).

The simplicial object takes values in the slice over `W`, so all its operators commute
with the augmentation. Weak contractibility is tested on sheaves on the full site of `X`.
The matching limits are formed in the slice over `W`. Yoneda preserves these finite
limits, giving exactly the matching sheaves over `h_W`: degree zero is `h_W`, degree
one is the fibre product over `h_W`, and higher degrees use the boundary multicospan.

Proof:
1. Work in the qcqs subsite, using
   lem-weil-pbc-proetale-qcqs-finite-family-geometry. Every object has a singleton cover
   by an affine weakly contractible object, by
   lem-weil-pbc-proetale-qc-affine-contractible-cover; affines are qcqs.
2. Apply lem-weil-pbc-site-finite-basis-hypercover-existence to obtain finite families
   of such objects in every degree. The qcqs inclusion preserves the slice matching
   limits and their covering maps, so this is a family hypercover in the full site.
3. Take the finite disjoint union in each degree. The geometry lemma identifies its
   representable sheaf with the coproduct of the component representables. Apply
   lem-weil-pbc-site-hypercover-disjoint-union. Operators are induced componentwise by
   the coproduct universal property, which also proves the simplicial identities.
   The resulting matching maps are epimorphisms, including the augmentation in degree zero.
4. Evaluation on a finite disjoint union is the product of the component evaluations.
   An epimorphism of full-site sheaves is surjective at each weakly contractible component;
   choose a lift in each factor. The finite product map is surjective. For an empty
   family both products are singletons. Thus the disjoint unions remain weakly contractible.
-/
theorem exists_affine_weaklyContractible_hypercover
    (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    ∃ U : SimplicialObject (Over W),
      (∀ n : ℕ, IsAffine (U _⦋n⦌).left.left) ∧
      (∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left))) ∧
      Epi ((topology X).yoneda.map (U _⦋0⦌).hom) ∧
      (∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌),
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋1⦌ ⟶ c.pt,
          (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) ∧
      (∀ n : ℕ, ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) := by
  obtain ⟨U, hAff, hComp, hzero, hone, hhigher⟩ :=
    exists_affine_hypercover_geometry X W
  refine ⟨U, hAff, ?_, hzero, hone, hhigher⟩
  exact weaklyContractible_of_components X W U hComp

end AlgebraicGeometry.Scheme.ProEt
