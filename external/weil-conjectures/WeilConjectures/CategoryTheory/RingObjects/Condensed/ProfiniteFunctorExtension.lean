/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.Extend

/-!
# Comparing functors by finite profinite tests

Source: Bhatt--Scholze, proof of Lemma 2.2.8, passage to finite-quotient limits.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Profinite

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism on finite profinite spaces extends uniquely to functors that
preserve the canonical finite-quotient presentations.

Source: Bhatt--Scholze, proof of Lemma 2.2.8
(blueprint: new-lem-zl-profinite-functor-extension).

Proof: each canonical finite-quotient cone is initial among all finite tests of its
apex. Thus each image apex is a limit over all its finite tests. The given finite
isomorphisms induce mutually inverse maps between these two limits. Naturality is
checked after every finite-test projection, where it is functoriality. -/
theorem functor_iso_of_finite {C : Type v} [Category.{w} C]
    (G H : Profinite.{u} ⥤ C)
    (hG : ∀ S : Profinite.{u}, Nonempty (IsLimit (G.mapCone S.asLimitCone)))
    (hH : ∀ S : Profinite.{u}, Nonempty (IsLimit (H.mapCone S.asLimitCone)))
    (e : FintypeCat.toProfinite ⋙ G ≅ FintypeCat.toProfinite ⋙ H) :
    Nonempty (G ≅ H) := by
  classical
  let g (S : Profinite.{u}) : IsLimit (Extend.cone G S) :=
    Extend.isLimitCone S.asLimitCone G S.asLimit (hG S).some
  let h (S : Profinite.{u}) : IsLimit (Extend.cone H S) :=
    Extend.isLimitCone S.asLimitCone H S.asLimit (hH S).some
  let d (S : Profinite.{u}) :=
    Functor.isoWhiskerLeft (StructuredArrow.proj S FintypeCat.toProfinite) e
  let g' (S : Profinite.{u}) :=
    (IsLimit.postcomposeHomEquiv (d S) (Extend.cone G S)).symm (g S)
  let iso (S : Profinite.{u}) : G.obj S ≅ H.obj S :=
    (g' S).conePointUniqueUpToIso (h S)
  have hi (S : Profinite.{u}) (A : FintypeCat.{u})
      (k : S ⟶ FintypeCat.toProfinite.obj A) :
      (iso S).hom ≫ H.map k = G.map k ≫ e.hom.app A :=
    (g' S).conePointUniqueUpToIso_hom_comp (h S) (StructuredArrow.mk k)
  refine ⟨NatIso.ofComponents iso ?_⟩
  intro S T f
  apply (h T).hom_ext
  intro i
  change (G.map f ≫ (iso T).hom) ≫ H.map i.hom =
    ((iso S).hom ≫ H.map f) ≫ H.map i.hom
  rw [Category.assoc, hi, ← Category.assoc, ← G.map_comp,
    Category.assoc, ← H.map_comp, hi]

end Profinite
