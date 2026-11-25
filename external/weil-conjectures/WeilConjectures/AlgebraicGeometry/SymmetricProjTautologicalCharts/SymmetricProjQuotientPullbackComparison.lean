/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjQuotientPullbackLocalComparison
import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso

/-! # Comparison of normalized quotient lines along a fixed Proj comparison

Source: Stacks Project, Constructions, Tags 01NR, 01NQ and 01OB.
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

open Scheme.Modules

-- Match the finite-limit instance used by the normalized quotient definitions.
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

private theorem iso_of_common_frame_coefficients {T : Scheme.{u}}
    {M P Q : T.Modules} (q : M ⟶ P) (q' : M ⟶ Q) {ι : Type u}
    (U : ι → T.Opens) (s : ∀ i, Γ(P, U i)) (t : ∀ i, Γ(Q, U i))
    (hU : (⨆ i, U i) = ⊤) (hs : ∀ i, IsFreeGenerator (s i))
    (ht : ∀ i, IsFreeGenerator (t i))
    (hc : ∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
      a • P.presheaf.map (homOfLE hi).op (s i) =
        c • P.presheaf.map (homOfLE hj).op (s j) →
      a • Q.presheaf.map (homOfLE hi).op (t i) =
        c • Q.presheaf.map (homOfLE hj).op (t j))
    (hq : ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
      ∃ c : Γ(T, V), q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
        q'.app V m = c • Q.presheaf.map (homOfLE hi).op (t i)) :
    ∃ w : P ≅ Q, q ≫ w.hom = q' := by
  let w := isoOfIsFreeGenerator hU hs ht hc
  refine ⟨w, Scheme.Modules.hom_ext _ _ fun V ↦ ?_⟩
  ext m
  have hcover : V ≤ ⨆ i, U i ⊓ V := by
    rw [← iSup_inf_eq, hU, top_inf_eq]
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨Q.presheaf, Q.isSheaf⟩
    (fun i ↦ U i ⊓ V) V (fun _ ↦ homOfLE inf_le_right) hcover
  intro i
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  obtain ⟨c, hcs, hct⟩ := hq i (U i ⊓ V) inf_le_left
    (M.presheaf.map (homOfLE inf_le_right).op m)
  rw [hcs, hct]
  exact isoOfIsFreeGenerator_hom_app_smul hU hs ht hc i inf_le_left c

/-- For fixed normalized quotients and a fixed generator-preserving graded pullback
comparison, the quotient lines agree along its induced relative Proj map.

Source: Stacks Project, Constructions, Tag 01NQ (lemma-relative-proj-base-change),
the degree-one part of theta; Tag 01NR (lemma-glue-relative-proj-twists), uniqueness;
Tag 01OB (definition-projective-bundle), the quotient normalization.
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison).

Proof: write A = Sym(E), A' = Sym(g*E). On a pair of affine base charts W, U
with W contained in g inverse U, the map of graded rings is the specified b.map.
On D_+(iota(m)), the normalized twist has the free frame iota(m). Pull back this
frame to the chart D_+(b.map(iota(m))) of Proj A'(W), and send it to the frame
b.map(iota(m)). This gives an isomorphism of free rank-one modules: its inverse
sends the new frame to the pulled frame. All degree-one elements of A(U) are
inclusion generators, and their charts cover. On an overlap the old transition
is the degree-zero fraction iota(m)/iota(n); its pullback is exactly
b.map(iota(m))/b.map(iota(n)), the new transition. Hence these local isomorphisms
and their inverses agree and glue. Refining overlaps of affine base opens by
affine opens gives the same calculation, so the isomorphisms glue over the
relative Proj. The chosen charts of D and D' identify their quotients with the
same inclusion sections. By the generator equation for b, the glued isomorphism
therefore preserves the quotient on every pulled section 1 tensor m. These
sections generate the pullback module locally; equality extends by linearity
and the sheaf axiom. The pullback composition isomorphisms used here are the
ones fixed by those sections, giving the displayed equation with the equality
proof induced by b.isPullback. Proof irrelevance gives the same equation with
any supplied proof e of that equality of module objects. Empty
charts, the zero module, and zero coefficient rings give zero localizations and
the same equations. No finite-generation or flatness hypothesis is used. -/
theorem quotient_comparison_of_normalized_pullbackData
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    ∃ w : (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line ≅ D'.line,
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
          (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient ≫ w.hom =
        (eqToIso e).hom ≫
        (Scheme.Modules.tensorPullbackSectionComp
          (SymmetricAlgebraSheaf.gradedAlgebraData
            ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫
          D'.quotient := by
  obtain ⟨ι, U, s, t, hU, hs, ht, hc, hq⟩ :=
    exists_normalized_pullback_frame_atlas g E D D' b hb e
  exact iso_of_common_frame_coefficients _ _ U s t hU hs ht hc hq

end AlgebraicGeometry.SymmetricProjTautologicalCharts
