/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Gluing ring actions from the affine basis

Source: Stacks Project, Tag 009O (sheaves on a basis); the affine-basis gluing in
Tags 01LX and 0897.
(blueprint: lem-weil-pbc-affine-basis-ring-action-gluing).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry

/-- Compatible actions on the affine basis extend uniquely to a natural ring action.

Source: Stacks Project, Tag 009O, applied to the affine basis; Tags 01LX and 0897.
(blueprint: lem-weil-pbc-affine-basis-ring-action-gluing).

Proof: Form the Type-valued presheaf P(U) = R(U) times F(U). The maps
(r,x) to tau(U)(r)(x) on affine opens are natural by the hypothesis. Apply
TopCat.Sheaf.restrictHomEquivHom to extend this natural transformation into
the underlying sheaf of sets of F. Its affine components are the prescribed
maps by extend_hom_app. Hence its evaluation a(U,r,x) satisfies naturality
and restricts to tau(V)(r|V)(x|V) on every affine V contained in U.
For a fixed r, check that a(U,r,-) is additive and preserves zero by restricting
to each affine V; there these are the additive-endomorphism identities of tau(V).
Similarly, check zero, addition, unit and multiplication in r on the affine
basis. These checks make a(U,-,-) a ring homomorphism to additive endomorphisms.
Separatedness proves each global identity from its local check. Naturality of
the extended map proves naturality of the actions, and extend_hom_app gives
affine agreement. Any other natural action with the same affine components
has the same restriction on all affine subopens, so separatedness proves
uniqueness. Affine subopens cover every open, including the empty one; no
intersection is assumed affine and no compactness is required. -/
theorem affineBasis_ringAction_gluing
    (X : Scheme.{u}) (R : TopCat.Sheaf RingCat.{u} X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (tau : ∀ U : X.affineOpens,
      R.obj.obj (op U.val) →+* AddMonoid.End (F.obj.obj (op U.val)))
    (htau : ∀ (U V : X.affineOpens) (i : U.val ⟶ V.val)
      (r : R.obj.obj (op V.val)) (x : F.obj.obj (op V.val)),
      F.obj.map i.op (tau V r x) =
        tau U (R.obj.map i.op r) (F.obj.map i.op x)) :
    ∃! sigma : ∀ U : X.Opens,
      R.obj.obj (op U) →+* AddMonoid.End (F.obj.obj (op U)),
      (∀ (U V : X.Opens) (i : U ⟶ V)
        (r : R.obj.obj (op V)) (x : F.obj.obj (op V)),
        F.obj.map i.op (sigma V r x) =
          sigma U (R.obj.map i.op r) (F.obj.map i.op x)) ∧
      (∀ U : X.affineOpens, sigma U.val = tau U) := by
  classical
  have hext (U : X.Opens) (x y : F.obj.obj (op U))
      (h : ∀ (V : X.affineOpens) (i : V.val ⟶ U),
        F.obj.map i.op x = F.obj.map i.op y) : x = y := by
    apply TopCat.Presheaf.IsSheaf.section_ext F.property
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset hz
    exact ⟨V, hVU, hzV, h ⟨V, hV⟩ (homOfLE hVU)⟩
  let P : X.Opensᵒᵖ ⥤ Type u :=
    { obj := fun U => R.obj.obj U × F.obj.obj U
      map := fun i => ↾fun p => (R.obj.map i p.1, F.obj.map i p.2)
      map_id := by intro U; ext p <;> simp
      map_comp := by intro U V W i j; ext p <;> simp [Functor.map_comp] }
  let FT := (sheafCompose _ (forget AddCommGrpCat.{u})).obj F
  have hb : TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : X.affineOpens => U.val)) := by
    convert X.isBasis_affineOpens using 1
    ext U
    simp
  let beta : (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙ P ⟶
      (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙ FT.obj :=
    { app := fun U => ↾fun p => tau U.unop p.1 p.2
      naturality := by
        intro U V i
        ext p
        exact (htau V.unop U.unop i.unop.hom p.1 p.2).symm }
  let alpha := TopCat.Sheaf.restrictHomEquivHom P FT hb beta
  let a (U : X.Opens) (r : R.obj.obj (op U)) (x : F.obj.obj (op U)) : F.obj.obj (op U) :=
    alpha.app (op U) (r, x)
  have hnat (U V : X.Opens) (i : U ⟶ V) (r : R.obj.obj (op V))
      (x : F.obj.obj (op V)) :
      F.obj.map i.op (a V r x) = a U (R.obj.map i.op r) (F.obj.map i.op x) := by
    exact (congrArg (fun k : P.obj (op V) ⟶ FT.obj.obj (op U) =>
      k (r, x)) (alpha.naturality i.op)).symm
  have haff (U : X.affineOpens) (r : R.obj.obj (op U.val))
      (x : F.obj.obj (op U.val)) : a U.val r x = tau U r x := by
    change (TopCat.Sheaf.restrictHomEquivHom P FT hb beta).app (op U.val) (r, x) = _
    rw [TopCat.Sheaf.extend_hom_app]
    rfl
  have hlocal (U : X.Opens) (V : X.affineOpens) (i : V.val ⟶ U)
      (r : R.obj.obj (op U)) (x : F.obj.obj (op U)) :
      F.obj.map i.op (a U r x) =
        tau V (R.obj.map i.op r) (F.obj.map i.op x) := by
    rw [hnat, haff]
  let sigma (U : X.Opens) : R.obj.obj (op U) →+* AddMonoid.End (F.obj.obj (op U)) :=
    { toFun := fun r =>
        { toFun := a U r
          map_zero' := by
            apply hext U
            intro V i
            rw [hlocal]
            simp
          map_add' := by
            intro x y
            apply hext U
            intro V i
            rw [hlocal]
            simp only [map_add, hlocal] }
      map_zero' := by
        ext x
        change a U 0 x = 0
        apply hext U
        intro V i
        rw [hlocal]
        simp
      map_add' := by
        intro r s
        ext x
        change a U (r + s) x = a U r x + a U s x
        apply hext U
        intro V i
        rw [hlocal]
        simp only [map_add, hlocal]
        rfl
      map_one' := by
        ext x
        change a U 1 x = x
        apply hext U
        intro V i
        rw [hlocal]
        simp
      map_mul' := by
        intro r s
        ext x
        apply hext U
        intro V i
        change F.obj.map i.op (a U (r * s) x) = F.obj.map i.op (a U r (a U s x))
        rw [hlocal, hlocal, hlocal]
        simp }
  refine ⟨sigma, ⟨hnat, ?_⟩, ?_⟩
  · intro U
    ext r x
    exact haff U r x
  · intro sigma' hsigma'
    funext U
    ext r x
    apply hext U
    intro V i
    rw [hsigma'.1, hsigma'.2]
    exact (hlocal U V i r x).symm

end AlgebraicGeometry
