/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateEtalePowerGeneration

/-! # Detection of maps on local lifted finite root tensors

Source: Stacks Project, `proetale.tex`, Lemma `describe-pullback-from-etale`, and
`sites-modules.tex`, tensor products; the uniqueness argument of the root comparison.
(blueprint: lem-pur-finite-tate-local-root-tensors-ext)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem finite_covering_intersection
    {C : Type*} [Category C] (J : GrothendieckTopology C) {U : C}
    {I : Type*} [Finite I] (S : I → Sieve U) (hS : ∀ i, S i ∈ J U) :
    iInf S ∈ J U := by
  classical
  let := Fintype.ofFinite I
  have hs (s : Finset I) : s.inf S ∈ J U := by
    induction s using Finset.induction_on with
    | empty => exact J.top_mem U
    | @insert i s hi ih =>
      simpa only [Finset.inf_insert] using J.intersection_covering (hS i) ih
  apply J.superset_covering ?_ (hs Finset.univ)
  exact le_iInf (fun i ↦ Finset.inf_le (Finset.mem_univ i))

private theorem finite_roots_lift_cover
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r d : ℕ) (U : T.Etaleᵒᵖ)
    (z : Fin d → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U) :
    ∃ S : Sieve ((toProEt T).obj U.unop), S ∈ ProEt.topology T _ ∧
      ∀ (W : T.ProEt) (v : W ⟶ (toProEt T).obj U.unop), S v →
        ∃ x : Fin d → (purTwistZlOne T l).obj.obj (Opposite.op W),
          ∀ i, finiteTateLimitRootValue l T r (Opposite.op W) (x i) =
            Units.map v.left.appTop.hom.toMonoidHom
              (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i)) := by
  classical
  have hstalk (t : T) : IsUnit (l : T.presheaf.stalk t) := by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  have hsurj := (rootTower_finite_tensor T l hstalk r).1
  let := hsurj
  let m := l ^ (r + 1)
  have hm : 0 < m := pow_pos (Fact.out : l.Prime).pos _
  have hTm : IsUnit (m : Γ(T, ⊤)) := by
    simpa only [m, Nat.cast_pow] using hT.pow (r + 1)
  let c := ProEtale.cartierRootsIso T m hm hTm
  let η := (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
    (T.rootsOfUnitySheaf m)
  let y (i : Fin d) := c.hom.hom.app
    (Opposite.op ((toProEt T).obj U.unop)) (η.hom.app U (z i))
  let S (i : Fin d) := Presheaf.imageSieve (rootTowerProjection T l r).hom (y i)
  refine ⟨iInf S, finite_covering_intersection (ProEt.topology T) S
    (fun i ↦ Presheaf.imageSieve_mem _ _ (y i)), ?_⟩
  intro W v hv
  have hi (i : Fin d) : S i v := iInf_le S i v hv
  choose x hx using hi
  refine ⟨x, ?_⟩
  intro i
  obtain ⟨_, _, _, hunit, _⟩ := finiteRootSiteComparison (ULift.{u + 1} (ZMod 1))
  have hn := ConcreteCategory.congr_hom (c.hom.hom.naturality v.op)
    (η.hom.app U (z i))
  change c.hom.hom.app (Opposite.op W)
      (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf m)).obj.map v.op (η.hom.app U (z i))) =
    (proEtaleRootsOfUnitySheaf T m).obj.map v.op (y i) at hn
  change finiteTateLimitRootValue l T r (Opposite.op W) (x i) = _
  unfold finiteTateLimitRootValue
  exact (congrArg (fun q ↦ Additive.toMul
    (((proEtaleRootsOfUnityInclusion T m).hom.app (Opposite.op W) q).down))
      ((hx i).trans hn.symm)).trans (hunit m hm T hTm U (Opposite.op W) v (z i))

private theorem finite_tate_generators_hom_ext
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (d : ℕ)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f g : finiteEtaleTateTwist T m A hA d ⟶ M)
    (h : ∀ U a z, f.hom.app U (finiteTateEtalePowerGenerator T A m hA U a d z) =
      g.hom.app U (finiteTateEtalePowerGenerator T A m hA U a d z)) : f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  obtain ⟨S, hS, ht⟩ := finiteTateEtalePowerGenerator_locally_span T A m hA d U t
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose T.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj
      M).property).isSeparated _ hS).ext
  intro V v hv
  have he : f.hom.app (Opposite.op V)
      ((finiteEtaleTateTwist T m A hA d).obj.map v.op t) =
      g.hom.app (Opposite.op V)
        ((finiteEtaleTateTwist T m A hA d).obj.map v.op t) := by
    have hspan : Submodule.span A (Set.range (fun q :
        A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj (Opposite.op V)) ↦
          finiteTateEtalePowerGenerator T A m hA (Opposite.op V) q.1 d q.2)) ≤
        LinearMap.eqLocus (f.hom.app (Opposite.op V)).hom
          (g.hom.app (Opposite.op V)).hom := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, z⟩, rfl⟩
      exact h _ a z
    exact hspan (ht V v hv)
  have hf := ConcreteCategory.congr_hom (f.hom.naturality v.op) t
  have hg := ConcreteCategory.congr_hom (g.hom.naturality v.op) t
  exact hf.symm.trans (he.trans hg)

/-- Maps from a compared finite Tate power are detected by root tensors after local
lifting to the root tower; the target is any sheaf of modules.
Source: Stacks Project, `proetale.tex`, Lemma `describe-pullback-from-etale` (0GLZ),
and `sites-modules.tex`, tensor product of module sheaves; the uniqueness step of
`def-pur-adic-root-comparisons`.
(blueprint: lem-pur-finite-tate-local-root-tensors-ext)

Proof: transpose both maps under the etale/pro-etale comparison adjunction. To compare
these adjuncts it suffices to compare their values on the etale pure root tensors:
scalar extension is the sheafification of the section tensor, and induction on the
ordered power gives this generation statement in every degree. Fix one such tensor
over an etale object U. By the finite-root comparison, each of its roots becomes a
pro-etale finite root on U. The root-tower projection is locally surjective when l is
invertible. Lift the finitely many roots on a common refinement of these pro-etale
covers. On every member W of that refinement the lifted roots satisfy the displayed
unit equalities, so the hypothesis identifies the two images of the restricted tensor.
Naturality makes these images the restrictions of the original two images. Separatedness
of the target sheaf identifies the original images. The tensor and scalar-extension
universal properties now identify the adjuncts, and the adjunction bijection identifies
the original maps. In degree zero the tuple is empty and no root lift is needed; the
constant-sheaf unit generators suffice. Empty schemes and the zero coefficient ring are
covered by the same separatedness and generation arguments. -/
theorem finiteTate_local_root_tensors_hom_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
    (f g : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d) ⟶ M)
    (h : ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
      (v : W.unop ⟶ (toProEt T).obj U.unop) (a : finiteTateCoefficient l E n)
      (z : Fin d → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
      (x : Fin d → (purTwistZlOne T l).obj.obj W),
      (∀ i : Fin d, finiteTateLimitRootValue l T r W (x i) =
        Units.map v.left.appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
      f.hom.app W
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d)).obj.map v.op
          (((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).unit.app
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d)).hom.app U
                (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a d z))) =
      g.hom.app W
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d)).obj.map v.op
          (((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).unit.app
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d)).hom.app U
                (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a d z)))) :
    f = g := by
  let adj := ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T
  apply (adj.homEquiv _ _).injective
  apply finite_tate_generators_hom_ext
  intro U a z
  obtain ⟨S, hS, hlift⟩ := finite_roots_lift_cover l T hT r d U z
  let t := (adj.unit.app (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d)).hom.app U
    (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a d z)
  change f.hom.app (Opposite.op ((toProEt T).obj U.unop)) t =
    g.hom.app (Opposite.op ((toProEt T).obj U.unop)) t
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose (ProEt.topology T)
      (CategoryTheory.forget (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))).obj
        M).property).isSeparated _ hS).ext
  intro W v hv
  obtain ⟨x, hx⟩ := hlift W v hv
  have hf := ConcreteCategory.congr_hom (f.hom.naturality v.op) t
  have hg := ConcreteCategory.congr_hom (g.hom.naturality v.op) t
  exact hf.symm.trans ((h U (Opposite.op W) v a z x hx).trans hg)

end AlgebraicGeometry.Scheme
