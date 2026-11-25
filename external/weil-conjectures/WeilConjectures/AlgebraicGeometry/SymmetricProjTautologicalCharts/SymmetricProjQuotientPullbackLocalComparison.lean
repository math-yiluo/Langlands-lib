/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackQuotientCrossTensor

/-! # Local frame atlas for normalized symmetric Proj pullback

Source: Stacks Project, Constructions, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison-local).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

open Scheme.Modules CategoryTheory.MonoidalCategory

private theorem tensor_pullback_invertible {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((tensorPullback g).obj M).IsInvertible := by
  have : ((Scheme.Modules.pullback g).obj M).IsInvertible := inferInstance
  exact IsInvertible.of_iso
    (((tensorPullbackSectionAdjunction g).leftAdjointUniq
      (pullbackPushforwardAdjunction g)).symm.app M)

private theorem tensor_pullback_epi {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : Y.Modules} (q : M ⟶ N) [Epi q] : Epi ((tensorPullback g).map q) := by
  have : (tensorPullback g).IsLeftAdjoint :=
    (tensorPullbackSectionAdjunction g).isLeftAdjoint
  infer_instance

private theorem local_lift {T : Scheme.{u}} {M P : T.Modules}
    (q : M ⟶ P) [Epi q] (U : T.Opens) (s : Γ(P, U)) (x : T) (hx : x ∈ U) :
    ∃ (V : T.Opens) (h : V ≤ U), x ∈ V ∧
      ∃ m : Γ(M, V), q.app V m = P.presheaf.map (homOfLE h).op s := by
  have : CategoryTheory.Limits.PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u} T.ringCatSheaf) :=
    SheafOfModules.preservesFiniteColimits_toSheaf _
  have hF : Epi ((SheafOfModules.toSheaf.{u} T.ringCatSheaf).map q) :=
    Functor.map_epi _ _
  have h := (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map q.val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi
      ((SheafOfModules.toSheaf.{u} T.ringCatSheaf).map q)).mpr hF)
  obtain ⟨V, hV, hm, hxV⟩ := h U s x hx
  exact ⟨V, hV, hxV, hm⟩

private theorem coefficients_of_cross_tensor {T : Scheme.{u}} {M P Q : T.Modules}
    (q : M ⟶ P) (q' : M ⟶ Q)
    (hcross : ∀ (V : T.Opens) (m n : Γ(M, V)),
      tmulSection (q.app V m) (q'.app V n) =
        tmulSection (q.app V n) (q'.app V m))
    {U : T.Opens} (m : Γ(M, U)) (hm : IsFreeGenerator (q.app U m))
    (V : T.Opens) (hV : V ≤ U) (n : Γ(M, V)) :
    ∃ c : Γ(T, V),
      q.app V n = c • P.presheaf.map (homOfLE hV).op (q.app U m) ∧
      q'.app V n = c • Q.presheaf.map (homOfLE hV).op (q'.app U m) := by
  obtain ⟨c, hc⟩ := (hm.map hV).exists_smul_eq (q.app V n)
  refine ⟨c, hc.symm, ?_⟩
  apply (hm.bijective_tmulSection_left hV).injective
  dsimp only
  rw [tmulSection_smul, ← smul_tmulSection, hc]
  have h := hcross V (M.presheaf.map (homOfLE hV).op m) n
  simpa only [Hom.app_presheaf_map] using h

private theorem exists_common_lifted_frame {T : Scheme.{u}} {M P Q : T.Modules}
    (q : M ⟶ P) (q' : M ⟶ Q) [Epi q] [Epi q']
    [SheafOfModules.IsInvertible.{u, u, u} P]
    [SheafOfModules.IsInvertible.{u, u, u} Q]
    (hcross : ∀ (V : T.Opens) (m n : Γ(M, V)),
      tmulSection (q.app V m) (q'.app V n) =
        tmulSection (q.app V n) (q'.app V m)) (x : T) :
    ∃ (U : T.Opens) (m : Γ(M, U)), x ∈ U ∧
      IsFreeGenerator (q.app U m) ∧ IsFreeGenerator (q'.app U m) := by
  obtain ⟨U, hxU, _, s, hs⟩ := exists_isFreeGenerator P (x := x) (W := ⊤) trivial
  obtain ⟨V, hxV, hVU, t, ht⟩ := exists_isFreeGenerator Q hxU
  obtain ⟨W, hWV, hxW, m, hm⟩ := local_lift q V.1
    (P.presheaf.map (homOfLE hVU).op s) x hxV
  obtain ⟨Z, hZW, hxZ, n, hn⟩ := local_lift q' W
    (Q.presheaf.map (homOfLE hWV).op t) x hxW
  let m' := M.presheaf.map (homOfLE hZW).op m
  have hm' : IsFreeGenerator (q.app Z m') := by
    dsimp only [m']
    rw [Hom.app_presheaf_map, hm]
    exact ((hs.map hVU).map hWV).map hZW
  have hn' : IsFreeGenerator (q'.app Z n) := by
    rw [hn]
    exact (ht.map hWV).map hZW
  obtain ⟨c, hc, hc'⟩ := coefficients_of_cross_tensor q q' hcross m' hm' Z le_rfl n
  simp only [presheaf_map_id_apply] at hc hc'
  obtain ⟨a, ha⟩ := hn'.exists_smul_eq (q'.app Z m')
  have hca : c * a = 1 := hn'.smul_left_injective (by
    dsimp only
    rw [mul_smul, ha, ← hc', one_smul])
  refine ⟨Z, m', hxZ, hm', ?_⟩
  rw [← ha]
  exact hn'.units_smul ⟨a, c, by rw [mul_comm, hca], hca⟩

private theorem atlas_of_cross_tensor {T : Scheme.{u}} {M P Q : T.Modules}
    (q : M ⟶ P) (q' : M ⟶ Q) [Epi q] [Epi q']
    [SheafOfModules.IsInvertible.{u, u, u} P]
    [SheafOfModules.IsInvertible.{u, u, u} Q]
    (hcross : ∀ (V : T.Opens) (m n : Γ(M, V)),
      tmulSection (q.app V m) (q'.app V n) =
        tmulSection (q.app V n) (q'.app V m)) :
    ∃ (ι : Type u) (U : ι → T.Opens) (s : ∀ i, Γ(P, U i))
      (t : ∀ i, Γ(Q, U i)),
      (⨆ i, U i) = ⊤ ∧ (∀ i, IsFreeGenerator (s i)) ∧
      (∀ i, IsFreeGenerator (t i)) ∧
      (∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
        a • P.presheaf.map (homOfLE hi).op (s i) =
          c • P.presheaf.map (homOfLE hj).op (s j) →
        a • Q.presheaf.map (homOfLE hi).op (t i) =
          c • Q.presheaf.map (homOfLE hj).op (t j)) ∧
      ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
        ∃ c : Γ(T, V), q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
          q'.app V m = c • Q.presheaf.map (homOfLE hi).op (t i) := by
  classical
  choose U m hx hs ht using exists_common_lifted_frame q q' hcross
  refine ⟨T, U, fun i ↦ q.app (U i) (m i), fun i ↦ q'.app (U i) (m i),
    eq_top_iff.mpr (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩),
    hs, ht, ?_, ?_⟩
  · intro i j V hi hj a c hac
    obtain ⟨d, hd, hd'⟩ := coefficients_of_cross_tensor q q' hcross (m i) (hs i)
      V hi (M.presheaf.map (homOfLE hj).op (m j))
    rw [Hom.app_presheaf_map] at hd hd'
    have had : a = c * d := ((hs i).map hi).smul_left_injective (by
      dsimp only
      rw [mul_smul, ← hd]
      exact hac)
    rw [hd', smul_smul, had]
  · intro i V hi n
    exact coefficients_of_cross_tensor q q' hcross (m i) (hs i) V hi n

private theorem composed_pullback_quotient_epi {S Y T : Scheme.{u}}
    (j : T ⟶ Y) (p : Y ⟶ S) (E : S.Modules) (L : Y.Modules)
    (q : (tensorPullback p).obj E ⟶ L) [Epi q] :
    Epi ((tensorPullbackSectionComp j p).hom.app E ≫ (tensorPullback j).map q) := by
  have := tensor_pullback_epi j q
  infer_instance

private theorem transported_composed_quotient_epi {S X T : Scheme.{u}}
    (p : T ⟶ X) (g : X ⟶ S) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback p).obj ((tensorPullback g).obj E) ⟶ L) [Epi q]
    (M : T.Modules) (e : M = (tensorPullback (p ≫ g)).obj E) :
    Epi ((eqToIso e).hom ≫ (tensorPullbackSectionComp p g).hom.app E ≫ q) := by
  infer_instance

private theorem tensor_pullback_sheaf_invertible {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] :
    SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback g).obj M) := by
  have := tensor_pullback_invertible g M
  exact IsInvertible.sheafOfModules_isInvertible _

private theorem pullback_atlas_of_cross_tensor
    {S X Y T : Scheme.{u}} (g : X ⟶ S) (j : T ⟶ Y) (p : Y ⟶ S) (p' : T ⟶ X)
    (E : S.Modules) (L : Y.Modules) (L' : T.Modules)
    (q₀ : (tensorPullback p).obj E ⟶ L)
    (q₀' : (tensorPullback p').obj ((tensorPullback g).obj E) ⟶ L')
    (e : (tensorPullback (j ≫ p)).obj E = (tensorPullback (p' ≫ g)).obj E)
    (hL : L.IsInvertible) (hL' : L'.IsInvertible) (hq₀ : Epi q₀) (hq₀' : Epi q₀')
    (hcross :
    let M := (tensorPullback (j ≫ p)).obj E
    let P := (tensorPullback j).obj L
    let q : M ⟶ P := (tensorPullbackSectionComp j p).hom.app E ≫
      (tensorPullback j).map q₀
    let q' : M ⟶ L' := (eqToIso e).hom ≫
      (tensorPullbackSectionComp p' g).hom.app E ≫ q₀'
    ∀ (V : T.Opens) (m n : Γ(M, V)),
      tmulSection (q.app V m) (q'.app V n) =
        tmulSection (q.app V n) (q'.app V m)) :
    let M := (tensorPullback (j ≫ p)).obj E
    let P := (tensorPullback j).obj L
    let q : M ⟶ P := (tensorPullbackSectionComp j p).hom.app E ≫
      (tensorPullback j).map q₀
    let q' : M ⟶ L' := (eqToIso e).hom ≫
      (tensorPullbackSectionComp p' g).hom.app E ≫ q₀'
    ∃ (ι : Type u) (U : ι → T.Opens) (s : ∀ i, Γ(P, U i))
      (t : ∀ i, Γ(L', U i)),
      (⨆ i, U i) = ⊤ ∧ (∀ i, Scheme.Modules.IsFreeGenerator (s i)) ∧
      (∀ i, Scheme.Modules.IsFreeGenerator (t i)) ∧
      (∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
        a • P.presheaf.map (homOfLE hi).op (s i) =
          c • P.presheaf.map (homOfLE hj).op (s j) →
        a • L'.presheaf.map (homOfLE hi).op (t i) =
          c • L'.presheaf.map (homOfLE hj).op (t j)) ∧
      ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
        ∃ c : Γ(T, V),
          q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
          q'.app V m = c • L'.presheaf.map (homOfLE hi).op (t i) := by
  exact @atlas_of_cross_tensor T ((tensorPullback (j ≫ p)).obj E)
    ((tensorPullback j).obj L) L'
    ((tensorPullbackSectionComp j p).hom.app E ≫ (tensorPullback j).map q₀)
    ((eqToIso e).hom ≫ (tensorPullbackSectionComp p' g).hom.app E ≫ q₀')
    (@composed_pullback_quotient_epi S Y T j p E L q₀ hq₀)
    (@transported_composed_quotient_epi S X T p' g E L' q₀' hq₀'
      ((tensorPullback (j ≫ p)).obj E) e)
    (@tensor_pullback_sheaf_invertible T Y j L hL)
    (@IsInvertible.sheafOfModules_isInvertible T L' hL') hcross

/-- Common local frames and quotient coefficients for the fixed Proj pullback map.

Source: Stacks Project, Constructions, Tags 01NQ and 01N2 (base-change fractions),
01NR (twist frames and transition ratios), and 01OB (quotient normalization).
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison-local).

Proof: cover the source by degree-one basic opens over pairs of affine base opens.
Scalar extension preserves the degree-one cover. On each such open choose the
pulled degree-one frame and its image frame. Both are free generators, since
localizing at the corresponding generator trivializes the degree-one twist.
On intersections the transition coefficient is the same pulled homogeneous ratio;
this remains true after any further restriction. The equation hb identifies the
image of every pulled module generator with the same coefficient times the two
frames. Pure tensors locally generate the tensor pullback; linearity and sheaf
uniqueness give this coefficient equation for every section on every subopen of a chart.
The section-normalized composition isomorphisms identify these with the two
morphisms below, including their equality transport. Refining base intersections
by affine opens gives compatibility without a separatedness assumption. Empty
schemes admit the empty cover; zero rings and empty charts satisfy the same formulas.
No global line isomorphism or gluing of line morphisms is asserted here. -/
theorem exists_normalized_pullback_frame_atlas
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
    let T := (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback g).obj E)).relProj
    let M := (Scheme.Modules.tensorPullback
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E
    let P := (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line
    let q : M ⟶ P :=
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    let q' : M ⟶ D'.line := (eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient
    ∃ (ι : Type u) (U : ι → T.Opens) (s : ∀ i, Γ(P, U i))
      (t : ∀ i, Γ(D'.line, U i)),
      (⨆ i, U i) = ⊤ ∧ (∀ i, Scheme.Modules.IsFreeGenerator (s i)) ∧
      (∀ i, Scheme.Modules.IsFreeGenerator (t i)) ∧
      (∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
        a • P.presheaf.map (homOfLE hi).op (s i) =
          c • P.presheaf.map (homOfLE hj).op (s j) →
        a • D'.line.presheaf.map (homOfLE hi).op (t i) =
          c • D'.line.presheaf.map (homOfLE hj).op (t j)) ∧
      ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
        ∃ c : Γ(T, V),
          q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
          q'.app V m = c • D'.line.presheaf.map (homOfLE hi).op (t i) := by
  exact pullback_atlas_of_cross_tensor g b.relProjComparison
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback g).obj E)).relProjHom
    E D.line D'.line D.quotient D'.quotient e D.invertible D'.invertible
    D.surjective D'.surjective (normalized_pullback_cross_tensor g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
