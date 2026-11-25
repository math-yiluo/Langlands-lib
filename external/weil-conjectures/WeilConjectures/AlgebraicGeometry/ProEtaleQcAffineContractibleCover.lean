/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# An affine weakly contractible singleton cover

Source: Stacks Project, proetale.tex, Tag 0F4P, last sentence; sites.tex, Tags 090K, 090L
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

private theorem exists_finite_refinement (T : Scheme.{u}) [CompactSpace T]
    (𝒰 : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) T)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    ∃ 𝒱 : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) T,
      Finite 𝒱.I₀ ∧ QuasiCompactCover 𝒱.toPreZeroHypercover ∧ Nonempty (𝒱 ⟶ 𝒰) := by
  classical
  let 𝒜₀ := T.affineCover.finiteSubcover
  let 𝒜 : Scheme.OpenCover.{u + 1} T := 𝒜₀.reindex (Equiv.ulift : ULift.{u + 1} 𝒜₀.I₀ ≃ 𝒜₀.I₀)
  have : Finite 𝒜.I₀ := inferInstanceAs (Finite (ULift 𝒜₀.I₀))
  have hAffine (a : 𝒜.I₀) : IsAffine (𝒜.X a) := by
    change IsAffine (𝒜₀.X a.down)
    dsimp [𝒜₀]
    infer_instance
  let (a : 𝒜.I₀) : IsAffine (𝒜.X a) := hAffine a
  have hlocal (a : 𝒜.I₀) :
      ∃ (𝒱 : Scheme.AffineCover.{u + 1} @WeaklyEtale (𝒜.X a))
        (r : 𝒱.cover ⟶ 𝒰.pullback₁ (𝒜.f a)),
        Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (r.h₀ j) := by
    let : QuasiCompactCover (𝒰.pullback₁ (𝒜.f a)).toPreZeroHypercover := by
      change QuasiCompactCover (𝒰.toPreZeroHypercover.pullback₁ (𝒜.f a))
      infer_instance
    exact QuasiCompactCover.exists_hom (𝒰.pullback₁ (𝒜.f a))
  choose 𝒱 r hfin _ using hlocal
  let (a : 𝒜.I₀) : Finite (𝒱 a).I₀ := hfin a
  let 𝒜' := 𝒜.changeProp (Q := @WeaklyEtale) (fun _ ↦ inferInstance)
  let 𝒲 := 𝒜'.bind (fun a ↦ (𝒱 a).cover)
  have hqcA : QuasiCompactCover 𝒜'.toPreZeroHypercover := by
    change QuasiCompactCover 𝒜.toPreZeroHypercover
    infer_instance
  have hqcV (a : 𝒜'.I₀) : QuasiCompactCover (𝒱 a).cover.toPreZeroHypercover := by
    infer_instance
  let := hqcA
  let (a : 𝒜'.I₀) := hqcV a
  refine ⟨𝒲, ?_, ?_, ⟨?_⟩⟩
  · change Finite (Σ a : 𝒜.I₀, (𝒱 a).I₀)
    infer_instance
  · change QuasiCompactCover (𝒜'.toPreZeroHypercover.bind
      (fun a ↦ (𝒱 a).cover.toPreZeroHypercover))
    infer_instance
  · exact
    { s₀ := fun p ↦ (r p.1).s₀ p.2
      h₀ := fun p ↦ (r p.1).h₀ p.2 ≫ 𝒰.pullbackHom (𝒜.f p.1) _
      w₀ := fun p ↦ by
        change ((r p.1).h₀ p.2 ≫ 𝒰.pullbackHom (𝒜.f p.1) _) ≫
          𝒰.f _ = (𝒱 p.1).cover.f p.2 ≫ 𝒜.f p.1
        rw [Category.assoc, Cover.pullbackHom_map, ← Category.assoc, (r p.1).w₀ p.2] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every quasi-compact object has a singleton pro-etale covering by an affine object
weakly contractible in the full site. Source: Stacks Project, Tag 0F4P, last sentence,
and Tags 090K (2), 090L
(auxiliary; not a blueprint node).

Proof:
1. Use lem-weil-pbc-proetale-affine-wcontractible-covering-family to cover `T` by
   affine objects weakly contractible in the full site.
2. Choose a finite affine open cover of `T`. For each member, the affine-open
   witnesses in definition-small-pro-etale-site--1 involve only finitely many covering
   indices. Retain their union. The witnesses restrict to principal opens and then
   to arbitrary affine opens; composition and refinement in definition-small-pro-etale-site--1
   show that the retained finite subfamily still covers. For empty `T`, retain no indices.
3. Take the finite disjoint union `V` of this family. By
   lem-weil-pbc-proetale-qcqs-finite-family-geometry it is an affine object of the site.
   The induced map to `T` is weakly etale: flatness is checked on each summand, and
   the diagonal is flat on equal-summand pieces and empty on distinct-summand pieces
   (definition-ind-etale-pro-etale-weakly--3). The same affine-open witnesses establish the
   singleton covering criterion of definition-small-pro-etale-site--1.
4. The finite-family geometry lemma identifies sheaf evaluation at `V` naturally
   with the product of evaluations at the summands. For any epimorphism of sheaves,
   choose a preimage in each factor by weak contractibility. This proves surjectivity
   at `V`. Empty products are singletons, so the argument also covers empty `T`. -/
theorem exists_affine_weaklyContractible_cover (X : Scheme.{u}) (T : X.ProEt)
    [CompactSpace T.left] :
    ∃ (V : X.ProEt) (f : V ⟶ T),
      Presieve.singleton f ∈ precoverage X T ∧
      IsAffine V.left ∧
      ∀ (F G : Sheaf (topology X) (Type (u + 1))) (η : F ⟶ G),
        Epi η → Function.Surjective (η.hom.app (op V)) := by
  classical
  obtain ⟨I, V, f, hcov, haff, hwc⟩ :=
    exists_affine_weaklyContractible_covering_family X T
  let E : PreZeroHypercover.{u + 1} T.left :=
    { I₀ := I, X := fun i ↦ (V i).left, f := fun i ↦ (f i).left }
  have hE : E.presieve₀ ∈ Scheme.proetalePrecoverage T.left := by
    simpa [precoverage, Presieve.map_ofArrows, ProEt.forget, E,
      MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      MorphismProperty.Comma.Hom.hom, PreZeroHypercover.presieve₀] using hcov
  let 𝒰 : Scheme.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale) T.left :=
    ⟨E, hE.2⟩
  let : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE.1
  obtain ⟨𝒲, hfin, hqc, ⟨r⟩⟩ := exists_finite_refinement T.left 𝒰
  let := hfin
  let := hqc
  let V' : 𝒲.I₀ → X.ProEt := fun j ↦ V (r.s₀ j)
  have haff' (j : 𝒲.I₀) : IsAffine (V' j).left := haff _
  obtain ⟨W, ι, _, _, _, _, hWaff, ⟨hc⟩, _, hprod, hnat, _⟩ :=
    finite_coproduct_evaluation.{u, u + 1, 0} X 𝒲.I₀ V'
      (fun j ↦ by let := haff' j; infer_instance)
      (fun j ↦ by let := haff' j; infer_instance)
  let Y := (topology X).uliftYoneda.{u + 1}
  let c := Limits.Cofan.mk (Y.obj T) (fun j ↦ Y.map (f (r.s₀ j)))
  let g : W ⟶ T := Y.preimage (hc.desc c)
  have hιg (j : 𝒲.I₀) : ι j ≫ g = f (r.s₀ j) := by
    apply Y.map_injective
    simp only [Functor.map_comp, g, Functor.map_preimage]
    exact hc.fac c ⟨j⟩
  refine ⟨W, g, ?_, hWaff haff', ?_⟩
  · let href : 𝒲.toPreZeroHypercover.Hom (PreZeroHypercover.singleton.{0} g.left) :=
      { s₀ := fun _ ↦ PUnit.unit
        h₀ := fun j ↦ r.h₀ j ≫ (ι j).left
        w₀ := fun j ↦ by
          change (r.h₀ j ≫ (ι j).left) ≫ g.left = 𝒲.f j
          rw [Category.assoc, ← MorphismProperty.Comma.comp_left, hιg j]
          exact r.w₀ j }
    let : QuasiCompactCover (PreZeroHypercover.singleton.{0} g.left) :=
      QuasiCompactCover.of_hom href
    have hgc : Presieve.singleton g.left ∈ Scheme.proetalePrecoverage T.left := by
      refine ⟨?_, ?_⟩
      · simpa using (Scheme.presieve₀_mem_qcPrecoverage_iff.mpr
          (inferInstance : QuasiCompactCover (PreZeroHypercover.singleton.{0} g.left)))
      · apply (Scheme.singleton_mem_precoverage_iff (@WeaklyEtale) g.left).mpr
        refine ⟨?_, ?_⟩
        · intro x
          obtain ⟨j, y, hy⟩ := 𝒲.exists_eq x
          refine ⟨(r.h₀ j ≫ (ι j).left) y, ?_⟩
          rw [← Scheme.Hom.comp_apply]
          have hw : (r.h₀ j ≫ (ι j).left) ≫ g.left = 𝒲.f j := by
            simpa [href, PreZeroHypercover.singleton] using href.w₀ j
          exact (congrArg (fun k : 𝒲.X j ⟶ T.left ↦ k y) hw).trans hy
        · have : WeaklyEtale (g.left ≫ T.hom) := by
            have hg : g.left ≫ T.hom = W.hom := by simp
            rw [hg]
            infer_instance
          exact WeaklyEtale.of_comp g.left T.hom
    simpa [precoverage, Presieve.map_singleton, ProEt.forget,
      MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      MorphismProperty.Comma.Hom.hom, PreZeroHypercover.presieve₀] using hgc
  · intro F G η hη s
    have hlift (j : 𝒲.I₀) :
        ∃ t : F.obj.obj (op (V' j)), η.hom.app (op (V' j)) t = G.obj.map (ι j).op s :=
      hwc (r.s₀ j) F G η hη _
    choose t ht using hlift
    obtain ⟨a, ha⟩ := (hprod F).2 t
    refine ⟨a, (hprod G).1 ?_⟩
    funext j
    change G.obj.map (ι j).op (η.hom.app (op W) a) = G.obj.map (ι j).op s
    rw [hnat F G η a j]
    have haj : F.obj.map (ι j).op a = t j := congrFun ha j
    rw [haj, ht j]

end AlgebraicGeometry.Scheme.ProEt
