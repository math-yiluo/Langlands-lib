/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackGeneratorLocalCoefficientsQ
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime

/-! Local coefficient charts for the normalized pullback generator relation.
(blueprint: lem-trf-symmetric-proj-pullback-generator-cross-tensor).
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

-- Perform the logical pairing before specializing to the concrete relative-Proj data.
private theorem pair_local_coefficients {S T : Scheme.{u}} (f : T ⟶ S)
    (E : S.Modules) {P Q : T.Modules}
    (q : (Scheme.Modules.tensorPullback f).obj E ⟶ P)
    (q' : (Scheme.Modules.tensorPullback f).obj E ⟶ Q)
    (hq : ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U.1)
      (x : T), x ∈ W →
      ∃ (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
        (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
        ∀ t : Γ(E, U.1),
          let s := ((Scheme.Modules.tensorPullback f).obj E).presheaf.map
            (homOfLE (hZW.trans h)).op (Scheme.Modules.tensorPullbackSection f E U.1 t)
          q.app Z s = c t • a)
    (hq' : ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := ((Scheme.Modules.tensorPullback f).obj E).presheaf.map
          (homOfLE (hZW.trans h)).op (Scheme.Modules.tensorPullbackSection f E U.1 t)
        q.app Z s = c t • a) →
      ∃ b' : Γ(Q, Z), ∀ t : Γ(E, U.1),
        let s := ((Scheme.Modules.tensorPullback f).obj E).presheaf.map
          (homOfLE (hZW.trans h)).op (Scheme.Modules.tensorPullbackSection f E U.1 t)
        q'.app Z s = c t • b') :
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U.1)
      (x : T), x ∈ W →
      ∃ (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
        (a : Γ(P, Z)) (b' : Γ(Q, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
        ∀ t : Γ(E, U.1),
          let s := ((Scheme.Modules.tensorPullback f).obj E).presheaf.map
            (homOfLE (hZW.trans h)).op (Scheme.Modules.tensorPullbackSection f E U.1 t)
          q.app Z s = c t • a ∧ q'.app Z s = c t • b' := by
  intro U W h x hx
  obtain ⟨Z, hZW, hxZ, a, c, hqZ⟩ := hq U W h x hx
  obtain ⟨b', hqZ'⟩ := hq' U W h x Z hZW hxZ a c hqZ
  exact ⟨Z, hZW, hxZ, a, b', c, fun t ↦ ⟨hqZ t, hqZ' t⟩⟩

/-- Local factorization and coefficient formulas on one affine chart.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
The proof first chooses an affine `V` below the image of a point and lifts the
point to the relative Proj chart over `V`. The old degree-one basic opens cover
that chart by symmetric-algebra induction. Choose one generator `v` containing
the lifted point, refine its standard open and the original open by an affine
`Z`, and factor the inclusion through the standard open. The absolute
`Proj.awayι_comp_map` and homogeneous-localization fraction map give the old
coefficient. The normalized chart formula for `D'` gives the new coefficient;
`hb` identifies the two coefficients. The pullback unit and composition
naturality transport both formulas to the displayed maps `q` and `q'`.
This is strictly weaker than the parent statement: it supplies only the local
common-coefficient data, with no tensor symmetry or sheaf gluing conclusion. -/
theorem normalized_pullback_generator_local_coefficients
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
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T), x ∈ W →
      ∃ (Z : T.Opens) (hZW : Z ≤ W) (_ : x ∈ Z)
        (a : Γ(P, Z)) (b' : Γ(D'.line, Z))
        (c : Γ(E, U.1) → Γ(T, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q.app Z s = c t • a ∧ q'.app Z s = c t • b' := by
  exact pair_local_coefficients
    (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) E
    ((Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
      (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient)
    ((eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient)
    (normalized_pullback_generator_local_coefficients_q g E D D' b hb e)
    (normalized_pullback_generator_local_coefficients_qprime g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
