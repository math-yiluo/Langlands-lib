/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackGeneratorLocalCoefficients
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjCrossTensorFromLocal

/-! # Degree-two relation on pulled module generators
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
open Scheme.Modules CategoryTheory.MonoidalCategory

/-- The degree-two cross relation on actual pulled generators over affine opens.

Source: Stacks Project, Constructions, Tags 01N2 (lemma-base-change-map-proj),
01NQ (lemma-relative-proj-base-change), 01NR (lemma-glue-relative-proj-twists),
and 01OB (definition-projective-bundle).
(blueprint: lem-trf-symmetric-proj-pullback-generator-cross-tensor).

Proof: refine W by inverse images of affine-pair charts for g and by their
standard opens D_+(b(iota(v))). They cover: the degree-one base-change condition
says that the images of the old degree-one elements span the new degree-one
part, so a homogeneous prime containing all images contains the irrelevant ideal.
On such a standard open, the chart normalization D.generator writes the image
of a pulled generator m as iota(m)/iota(v) times the pulled old twist frame.
The new chart normalization D'.generator writes its image as
b(iota(m))/b(iota(v)) times the new frame, by hb. The fraction formula for the
Proj map identifies the pulled old coefficient with this new coefficient.
Thus the two displayed tensors have respective coefficients c_m*c_n and c_n*c_m
in the same tensor of the two frames; they agree by commutativity. The
section-normalized pullback composition and its unit equation identify the
sections with m' and n', including the equality transport e; proof irrelevance
makes the choice of equality proof immaterial. Where U and an affine pair's
base open differ, refine their intersection by affine opens and apply the same
calculation to restricted m and n. Separation of the tensor sheaf glues the
identity on W. Empty standard opens and zero coefficient rings satisfy the
same equality. This proves only the formula for the specified pulled generators;
no extension to arbitrary sections, free-frame atlas or line isomorphism is
asserted. -/
theorem normalized_pullback_generator_cross_tensor
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
    ∀ (U : S.affineOpens) (W : T.affineOpens)
      (h : W.1 ≤ (b.relProjComparison ≫
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (m n : Γ(E, U.1)),
      let m' := M.presheaf.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection
          (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
          E U.1 m)
      let n' := M.presheaf.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection
          (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
          E U.1 n)
      Scheme.Modules.tmulSection (q.app W.1 m') (q'.app W.1 n') =
        Scheme.Modules.tmulSection (q.app W.1 n') (q'.app W.1 m')  := by
  exact cross_tensor_of_local_coefficients_public
    (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) E
    ((Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
      (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient)
    ((eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient)
    (normalized_pullback_generator_local_coefficients g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
