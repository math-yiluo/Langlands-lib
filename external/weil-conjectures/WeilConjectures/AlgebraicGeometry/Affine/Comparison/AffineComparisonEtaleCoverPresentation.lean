/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.CategoryTheory.Pro.Generating
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-!
# Simultaneous affine étale presentations of a finite covering family

Source: Stacks Project, Tag 099U, the geometric finite-cover reductions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace AlgebraicGeometry.ProEtale

private theorem exists_surjective_presentation
    {Y : Scheme.{u}} {A B : Y.AffineProEt} (q : A ⟶ B) [Surjective q.left] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (pA : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) A)
      (pB : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) B)
      (f : pA.Hom pB), f.map = q ∧
      ∀ i, Sieve.generate (Presieve.singleton (f.natTrans.app i)) ∈
        Scheme.AffineEtale.topology Y (pB.diag.obj i) := by
  have hrel : PreZeroHypercover.IsRelativelyPresentable.{u}
      (Scheme.AffineEtale.toAffineProEt Y) (Scheme.AffineEtale.topology Y)
      (Presieve.singleton q).preZeroHypercover := by
    apply Scheme.AffineProEt.singleton_inf_le_relativelyPresentable
    refine ⟨⟨A, q, rfl⟩, ?_⟩
    rw [MorphismProperty.singleton_mem_precoverage_iff]
    infer_instance
  obtain ⟨I, _, _, p, hp⟩ := hrel
  let a₀ : (Presieve.singleton q).preZeroHypercover.I₀ :=
    ⟨⟨A, q⟩, Presieve.singleton.mk⟩
  have ha (a : (Presieve.singleton q).preZeroHypercover.I₀) : a = a₀ := by
    rcases a with ⟨⟨Z, t⟩, ht⟩
    cases ht
    rfl
  refine ⟨I, inferInstance, inferInstance, p.pres₀ a₀, p.pres, p.f a₀, p.hf a₀, ?_⟩
  intro i
  have he : (p.preZeroHypercover i).sieve₀ =
      Sieve.generate (Presieve.singleton ((p.f a₀).natTrans.app i)) := by
    apply congrArg Sieve.generate
    apply le_antisymm
    · rintro Z t ⟨a⟩
      obtain rfl := ha a
      exact Presieve.singleton.mk
    · rintro Z t ⟨⟩
      exact ⟨a₀⟩
  rw [← he]
  exact hp i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A finite covering of affine ind-étale objects admits compatible small cofiltered
presentations by affine étale covering families. Only the base and the members are
presented here; the repeated intersections are constructed separately by universal
properties in `presentedNerveIsLimit`.
Source: Stacks Project, Tag 099U, the two geometric finite-cover reductions;
Tags 01ZM, 01ZN and 07RP, finite presentation and covering descent.
(blueprint: lem-cbc-affine-etale-cover-presentation).

Proof: Write the finite disjoint union of the members as Spec of the product of
their rings of global sections. It is affine ind-étale over the base, and the
covering hypothesis makes its map to the base surjective. The original members
are a finite affine open cover of this disjoint union. Simultaneously present this
single surjection and its target by affine étale Y-schemes, refining the index to
ensure surjectivity at every stage; this is the single-surjection relative-limit
presentation in AffineProEt.singleton_inf_le_relativelyPresentable.
Descend the finite affine open cover of the source to one stage, using finite
Zariski-cover descent along the source presentation. Restrict the common index
to the over-category of that stage. Pulling the descended opens back gives
presentations of the original members with compatible arrows to the target
presentation. Their composites cover the target at every stage: the opens cover
the source stage and its map to the target stage is surjective. Affineness is
preserved under the pullbacks. The original pullback squares and cofiltered
base-change limits identify each member's limit, while the target presentation
remains a limit by initiality of the over-category projection. This construction
keeps the given finite indexing, including repetitions. The same construction handles an
empty covering: its disjoint union is empty, and the descended covering family
is empty at every stage. -/
theorem exists_affine_etale_cover_presentation
    (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ a, proAffineEtale (U a).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (P : (finiteCover U).RelativeLimitPresentation (Scheme.toProEt Y) I),
      (∀ i, Sieve.ofArrows (fun a ↦ (P.pres₀ a).diag.obj i)
        (fun a ↦ (P.f a).natTrans.app i) ∈ Y.smallEtaleTopology (P.pres.diag.obj i)) ∧
      (∀ i, IsAffine (P.pres.diag.obj i).left) ∧
      (∀ i a, IsAffine ((P.pres₀ a).diag.obj i).left) ∧
      Nonempty (IsLimit ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone P.pres.cone)) ∧
      ∀ a, Nonempty (IsLimit
        ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (P.pres₀ a).cone)) := by
  classical
  let B : Y.AffineProEt := Scheme.AffineProEt.mk V.hom hV
  let A (a : Fin n) : Y.AffineProEt :=
    Scheme.AffineProEt.mk (U a).left.hom (hU a)
  let f (a : Fin n) : A a ⟶ B :=
    MorphismProperty.Over.homMk (U a).hom.left (U a).hom.w trivial
  have hcov : Sieve.ofArrows A f ∈ Scheme.AffineProEt.topology Y B := by
    rw [← Functor.functorPushforward_mem_iff _ (Scheme.ProEt.topology Y)
      (Scheme.AffineProEt.toProEt Y), Sieve.functorPushforward_ofArrows]
    exact hcover
  have hsurj : ∀ x : B.left, ∃ a, x ∈ Set.range ((f a).left.base) := by
    obtain ⟨ι, _, Z, g, hg, hs⟩ :=
      Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hcov
    intro x
    obtain ⟨i, z, hz⟩ := hs x
    obtain ⟨Q, r, t, ⟨a⟩, ht⟩ := hg i
    refine ⟨a, r.left.base z, ?_⟩
    rw [← hz, ← ht]
    rfl
  obtain ⟨W, q, j, hq, hjq, hj, hjcov⟩ :=
    Scheme.AffineProEt.exists_surjective_factorization
      (fun a : ULift.{u} (Fin n) ↦ A a.down) (fun a ↦ f a.down) (by
        intro x
        obtain ⟨a, z, hz⟩ := hsurj x
        exact ⟨ULift.up a, z, hz⟩)
  let : Surjective q.left := hq
  obtain ⟨I, _, _, pW, pB, pq, hpq, hqcov⟩ := exists_surjective_presentation q
  let j' (a : Fin n) : A a ⟶ W := j (ULift.up a)
  let cov : W.left.OpenCover := by
    refine ⟨⟨Fin n, fun a ↦ (A a).left, fun a ↦ (j' a).left⟩, ?_⟩
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun a ↦ hj (ULift.up a)⟩
    intro x
    obtain ⟨a, z, hz⟩ := hjcov x
    exact ⟨a.down, z, hz⟩
  have : ∀ a, IsAffine (cov.X a) := fun a ↦ by
    change IsAffine (A a).left
    infer_instance
  have : Finite cov.I₀ := inferInstanceAs (Finite (Fin n))
  let F := Scheme.AffineEtale.toScheme Y
  let R := Scheme.AffineProEt.toScheme Y
  have : ∀ i, IsAffine ((pW.diag ⋙ F).obj i) := fun i ↦ by
    change IsAffine ((Scheme.AffineEtale.Spec Y).obj (pW.diag.obj i)).left
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  let x := R.mapCone pW.cone
  obtain ⟨i, rings, v, hv, g, hg⟩ := cov.exists_of_isCofiltered_of_finite
    (pW.diag ⋙ F) x (isLimitOfPreserves R pW.isLimit)
  have (a : Fin n) : IsOpenImmersion (v a) := hv.right ⟨a⟩
  have : Etale (pW.diag.obj i).hom := (pW.diag.obj i).prop
  let E (a : Fin n) : Y.AffineEtale := Scheme.AffineEtale.mk
    (v a ≫ (pW.diag.obj i).hom)
  let v' (a : Fin n) : E a ⟶ pW.diag.obj i :=
    CostructuredArrow.homMk (Spec.preimage (v a)).op trivial (by simp [E])
  let g' (a : Fin n) : A a ⟶ (Scheme.AffineEtale.toAffineProEt Y).obj (E a) := by
    refine MorphismProperty.Over.homMk (g a) ?_ trivial
    have h1 := CostructuredArrow.w (j' a).toCommaMorphism
    dsimp at h1
    have h2 := CostructuredArrow.w (pW.π.app i).toCommaMorphism
    dsimp at h2
    change (pW.π.app i).left ≫ (pW.diag.obj i).hom = W.hom at h2
    change (j' a).left ≫ W.hom = (A a).hom at h1
    change g a ≫ (v a ≫ (pW.diag.obj i).hom) = (A a).hom
    rw [(hg a).w_assoc]
    change (j' a).left ≫ (pW.π.app i).left ≫ (pW.diag.obj i).hom = (A a).hom
    rw [h2, h1]
  have hpb (a : Fin n) : IsPullback (g' a) (j' a)
      ((Scheme.AffineEtale.toAffineProEt Y).map (v' a)) (pW.π.app i) := by
    refine IsPullback.of_map_of_faithful R ?_
    simpa [R, v', g', x, cov, E] using hg a
  let pA (a : Fin n) := pW.restrict (v' a) (A a) (g' a) (j' a) (hpb a)
  let pB' := pB.precomp (Over.forget i)
  let pq' : (pW.precomp (Over.forget i)).Hom pB' :=
    ⟨Functor.whiskerLeft (Over.forget i) pq.natTrans⟩
  let pf (a : Fin n) : (pA a).Hom pB' :=
    (pW.restrictHom (v' a) (A a) (g' a) (j' a) (hpb a)).comp pq'
  have hpf (a : Fin n) : (pf a).map = f a := by
    apply pB'.isLimit.hom_ext
    intro b
    rw [RelativeLimitPresentation.Hom.map_π]
    change (pA a).π.app b ≫ (Scheme.AffineEtale.toAffineProEt Y).map
      ((pW.restrictHom (v' a) (A a) (g' a) (j' a) (hpb a)).natTrans.app b ≫
        pq.natTrans.app b.left) = _
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← RelativeLimitPresentation.Hom.map_π,
      RelativeLimitPresentation.restrictHom_map]
    rw [Category.assoc]
    change j' a ≫ pW.π.app b.left ≫ _ = _
    rw [← RelativeLimitPresentation.Hom.map_π, hpq, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ pB.π.app b.left) (hjq (ULift.up a))
  let peB : RelativeLimitPresentation (Over i) (Scheme.toProEt Y) V :=
    { diag := presentationDiagram pB'
      π := (presentationCone pB').π
      isLimit := isLimitOfReflects (Scheme.ProEt.forget Y)
        (isLimitOfReflects (Over.forget Y) (isLimitPresentationCone pB')) }
  let peA (a : Fin n) : RelativeLimitPresentation (Over i) (Scheme.toProEt Y) (U a).left :=
    { diag := presentationDiagram (pA a)
      π := (presentationCone (pA a)).π
      isLimit := isLimitOfReflects (Scheme.ProEt.forget Y)
        (isLimitOfReflects (Over.forget Y) (isLimitPresentationCone (pA a))) }
  let pfe (a : Fin n) : (peA a).Hom peB :=
    ⟨Functor.whiskerRight (pf a).natTrans (Scheme.AffineEtale.Spec Y)⟩
  have hpfe (a : Fin n) : (pfe a).map = (U a).hom := by
    apply peB.isLimit.hom_ext
    intro b
    rw [RelativeLimitPresentation.Hom.map_π]
    apply (Scheme.ProEt.forget Y ⋙ Over.forget Y).map_injective
    have hw := congrArg (Scheme.AffineProEt.toScheme Y).map ((pf a).map_π b)
    rw [hpf] at hw
    change ((pA a).π.app b).left ≫
      (Scheme.AffineEtale.toScheme Y).map ((pf a).natTrans.app b) =
      (f a).left ≫ (pB'.π.app b).left
    exact hw.symm
  let P : (finiteCover U).RelativeLimitPresentation (Scheme.toProEt Y) (Over i) :=
    ⟨peB, peA, pfe, hpfe⟩
  refine ⟨Over i, inferInstance, inferInstance, P, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro t
    have hQ := (Functor.functorPushforward_mem_iff
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology
      (Scheme.AffineEtale.Spec Y)).mpr (hqcov b.left)
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton,
      ← Presieve.ofArrows_pUnit.{0}] at hQ
    have hQ' := Scheme.ofArrows_mem_smallEtaleTopology_iff _ |>.mp hQ
    have ht : t ∈ ⋃ a : PUnit.{1}, Set.range
        ((Scheme.AffineEtale.Spec Y).map (pq.natTrans.app b.left)).left := by
      rw [hQ']
      trivial
    obtain ⟨_, z, hz⟩ := Set.mem_iUnion.mp ht
    have hv' := (Scheme.ofArrows_mem_precoverage_iff _).mp hv
    obtain ⟨a, w, hw⟩ := hv'.1 ((F.map (pW.diag.map b.hom)).base z)
    have H := (IsPullback.of_hasPullback (pW.diag.map b.hom) (v' a)).map F
    have hxy : (F.map (pW.diag.map b.hom)).base z = (F.map (v' a)).base w := by
      have he : F.map (v' a) = v a := by
        simp [F, v']
      rw [he]
      exact hw.symm
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback z w hxy
    let r := H.isoPullback.inv.base p
    have hr : (F.map (pullback.fst (pW.diag.map b.hom) (v' a))).base r = z := by
      change (H.isoPullback.inv ≫ F.map (pullback.fst _ _)).base p = z
      rw [H.isoPullback_inv_fst]
      exact hp₁
    apply Set.mem_iUnion.mpr
    refine ⟨a, r, ?_⟩
    change (F.map (pullback.fst (pW.diag.map b.hom) (v' a) ≫
      pq.natTrans.app b.left)).base r = t
    rw [CategoryTheory.Functor.map_comp]
    change (F.map (pq.natTrans.app b.left)).base
      ((F.map (pullback.fst _ _)).base r) = t
    rw [hr]
    exact hz
  · intro b
    exact inferInstanceAs (IsAffine ((presentationDiagram pB').obj b).left)
  · intro b a
    exact inferInstanceAs (IsAffine ((presentationDiagram (pA a)).obj b).left)
  · exact ⟨isLimitPresentationCone pB'⟩
  · intro a
    exact ⟨isLimitPresentationCone (pA a)⟩

end AlgebraicGeometry.ProEtale
