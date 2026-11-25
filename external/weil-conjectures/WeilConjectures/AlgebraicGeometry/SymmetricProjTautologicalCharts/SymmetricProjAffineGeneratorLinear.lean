/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescent
import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjChartScalar
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj

/-! # Linearity of the affine symmetric degree-one section

Source: Stacks Project, Constructions, Tags 01OB and 01NR.
(blueprint: lem-trf-symmetric-proj-affine-generator-linear).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι

private noncomputable def affineFraction {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (W : (Proj 𝒜).Opens) (a : 𝒜 1) : Γ(Proj.twist 𝒜 1, W) :=
  (Proj.unitToTwist a.property).app W (1 : Γ(Proj 𝒜, W))

private theorem affineFraction_val {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (W : (Proj 𝒜).Opens) (a : 𝒜 1) (x : W) :
    ((affineFraction 𝒜 W a).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (a : B) 1 := by
  exact (Proj.val_unitToTwist_app_apply (𝒜 := 𝒜) a.property
    (1 : Γ(Proj 𝒜, W)) x).trans (by simp)

private theorem affineFraction_add {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (W : (Proj 𝒜).Opens) (a b : 𝒜 1) :
    affineFraction 𝒜 W (a + b) = affineFraction 𝒜 W a + affineFraction 𝒜 W b := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((affineFraction 𝒜 W (a + b)).1 x :
    Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      ((affineFraction 𝒜 W a).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) +
        (affineFraction 𝒜 W b).1 x
  rw [affineFraction_val, affineFraction_val, affineFraction_val]
  simp [Localization.add_mk, add_comm]

private theorem affineFraction_smul {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (W : (Proj 𝒜).Opens) (r : R) (a : 𝒜 1) (c : Γ(Proj 𝒜, W))
    (hc : ∀ x : W, (c.1 x).val = Localization.mk (algebraMap R B r) 1) :
    affineFraction 𝒜 W (r • a) = c • affineFraction 𝒜 W a := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((affineFraction 𝒜 W (r • a)).1 x :
    Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      ((c • affineFraction 𝒜 W a).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
  rw [Proj.coe_twist_smul_apply, affineFraction_val, affineFraction_val, hc]
  simp [Algebra.smul_def, Localization.mk_mul]

/-- The section m maps to iota(m)/1 is linear over the affine base ring. This assertion
is entirely on the absolute affine Proj chart and constructs no descended sheaf.

Source: Stacks, Tag 01OB, definition-projective-bundle, and Tag 01NR, its affine
homogeneous-section map.
(blueprint: lem-trf-symmetric-proj-affine-generator-linear).

Proof: evaluate sections in the degree-one part of the localization at each point.
The section associated to m has value iota(m)/1. Additivity follows from additivity
of iota and of localization. Multiplying m by r multiplies its image by the image of
r under the structural ring map: iota(r m)=r iota(m). This is exactly the scalar
action in the two iterated pushforwards, because relProjι followed by relProjHom
is the structural morphism of the affine Proj chart followed by the base inclusion.
The equalities hold pointwise and hence as sections. These identities bundle the
specified function as a linear map; no freeness or finite generation is used. -/
theorem exists_affine_generator_linear
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] (U : S.affineOpens) :
    ∃ t : E.val.obj (op U.1) →ₗ[Γ(S, U.1)]
      ((Scheme.Modules.pushforward (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj
        ((Scheme.Modules.pushforward
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj
          (Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1))).val.obj
        (op U.1),
      ∀ (m : E.val.obj (op U.1))
        (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
          (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1),
        t m = (SymmetricAlgebraSheaf.gradedAlgebraData E).twistChartFraction U
          ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m, hm⟩ := by
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let : GradedAlgebra (A.grading U) := A.gradedAlgebra U
  have hι (m : E.val.obj (op U.1)) :
      SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈ A.grading U 1 := by
    change _ ∈ _ ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ m
  let t (m : E.val.obj (op U.1)) : Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
    A.twistChartFraction U
    ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m, hι m⟩
  refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, fun _ _ ↦ rfl⟩
  · intro m n
    have he : (⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) (m + n),
        hι (m + n)⟩ : A.grading U 1) =
        ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m, hι m⟩ +
          ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) n, hι n⟩ :=
      Subtype.ext (map_add _ m n)
    change affineFraction (A.grading U) (A.twistChartOpen U) _ =
      affineFraction (A.grading U) (A.twistChartOpen U) _ +
        affineFraction (A.grading U) (A.twistChartOpen U) _
    rw [he]
    exact affineFraction_add _ _ _ _
  · intro r m
    have he : (⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) (r • m),
        hι (r • m)⟩ : A.grading U 1) =
        r • ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m, hι m⟩ :=
      Subtype.ext ((SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))).map_smul r m)
    let c : Γ(Proj (A.grading U), A.twistChartOpen U) :=
      (A.relProjι U).app (A.relProjHom ⁻¹ᵁ U.1) (A.relProjHom.app U.1 r)
    change affineFraction (A.grading U) (A.twistChartOpen U) _ =
      c • affineFraction (A.grading U) (A.twistChartOpen U) _
    rw [he]
    exact affineFraction_smul _ _ _ _ _ (fun x ↦ A.chart_scalar_value U r x)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
