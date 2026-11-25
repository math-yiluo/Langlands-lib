/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! Local `q` coefficient frames for the normalized pullback generator relation.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
The statement isolates the first (pulled quotient) coefficient formula from the
common-coefficient conclusion.
(blueprint: lem-trf-symmetric-proj-pullback-generator-local-coefficients-q)
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

-- The fixed interface includes hypotheses used by the two-quotient comparison.
set_option linter.unusedVariables false in
/-- A local frame and coefficient formula for the first pulled quotient map.

This is the local standard-open refinement and degree-one fraction calculation
for `q`; the second quotient map is deliberately omitted. The proof is the
corresponding first half of the chart argument in the cited Stacks tags.
-/
theorem normalized_pullback_generator_local_coefficients_q
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
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T), x ∈ W →
      ∃ (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
        (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q.app Z s = c t • a := by
  classical
  intro T M P q U W h x hx
  have : D.line.IsInvertible := D.invertible
  have : ((Scheme.Modules.pullback b.relProjComparison).obj D.line).IsInvertible :=
    inferInstance
  have : P.IsInvertible := Scheme.Modules.IsInvertible.of_iso
    (((Scheme.Modules.tensorPullbackSectionAdjunction b.relProjComparison).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction b.relProjComparison)).symm.app D.line)
  have : SheafOfModules.IsInvertible.{u, u, u} P :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible P
  obtain ⟨Z, hxZ, hZW, a, ha⟩ := Scheme.Modules.exists_isFreeGenerator P hx
  let s (t : Γ(E, U.1)) : Γ(M, Z.1) :=
    M.presheaf.map (homOfLE (hZW.trans h)).op
      (Scheme.Modules.tensorPullbackSection
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
        E U.1 t)
  refine ⟨Z.1, hZW, hxZ, a, fun t ↦ ha.coeff (q.app Z.1 (s t)), ?_⟩
  intro t
  exact (ha.coeff_smul (q.app Z.1 (s t))).symm

end AlgebraicGeometry.SymmetricProjTautologicalCharts
