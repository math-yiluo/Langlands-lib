import Langlands.Representation.CuspidalSupport.UniformAdmissibilityStatements
import Langlands.Representation.Plancherel.RationalNormKernelCompactOpenTransport
import Langlands.Representation.Induction.OpenIrreducibleEmbedding
import Langlands.Representation.Jacquet.FixedVectorUniverseLift

/-! # Renard VI.2.3–VI.2.4: assembly from the `G(F)` theorem and VI.2.4

The uniform admissibility theorem for `G(F)` in carrier universe `max u v` gives the
same theorem in carrier universe `v` and, by the Remark after VI.2.3, the theorem for
the common norm kernel `⁰G`. With VI.2.4 this gives the full target
`UniformAdmissibilityStatements`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- The three statements of Renard VI.2.3–VI.2.4 follow from the uniform admissibility
theorem for `G(F)` with carriers in `Type (max u v)` and from VI.2.4 with carriers in
`Type v`. -/
def UniformAdmissibilityAssemblyReductionStatement : Prop :=
  RationalPointsUniformAdmissibilityStatement.{u, max u v} →
    SupercuspidalUniformCoefficientSupportStatement.{u, v} →
      UniformAdmissibilityStatements.{u, v}

/-- The uniform admissibility theorem for `G(F)` passes from carriers in
`Type (max u v)` to carriers in `Type v`: lift the carrier with `ULift`, which keeps
irreducibility and the fixed-vector space up to a linear equivalence. -/
theorem rationalPointsUniformAdmissibility_of_max
    (h : RationalPointsUniformAdmissibilityStatement.{u, max u v}) :
    RationalPointsUniformAdmissibilityStatement.{u, v} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro K hK
  obtain ⟨c, hc⟩ := h F G hG K hK
  refine ⟨c, fun A hA => ?_⟩
  have hE := hc (SmoothRep.universeLift.{u} A)
    ((SmoothRep.isIrreducible_universeLift_iff A).mpr hA)
  have heq := (Jacquet.fixedVectorsUniverseLiftEquiv.{u} K.toSubgroup A).lift_rank_eq
  have hE' := Cardinal.lift_le_nat_iff.{max u v, v}.mpr hE
  rw [← heq] at hE'
  exact Cardinal.lift_le_nat_iff.{v, max u v}.mp hE'

/-- Renard VI.2.3 Remark: the uniform admissibility theorem for `G(F)`, for carriers in
`Type (max u v)`, implies the uniform admissibility theorem for the common norm kernel
`⁰G`, for carriers in `Type v`. Each irreducible of `⁰G` embeds in the restriction of an
irreducible of `G(F)`, and the `K`-fixed vectors go into the fixed vectors of the
image of `K` in `G(F)`. -/
theorem rationalNormKernelUniformAdmissibility_of_rationalPoints
    (h : RationalPointsUniformAdmissibilityStatement.{u, max u v}) :
    RationalNormKernelUniformAdmissibilityStatement.{u, v} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro K hK
  let K' := Plancherel.rationalNormKernelAmbientLevel G K
  obtain ⟨c, hc⟩ :=
    h F G hG K' (Plancherel.isCompact_rationalNormKernelAmbientLevel G K hK)
  refine ⟨c, fun A hA => ?_⟩
  let H := Plancherel.rationalCommonNormOpenSubgroup G
  let E := Induction.openIrreducibleEmbedding H A hA
  have hE : Module.rank ℂ (fixedVectors E.obj.representation K'.toSubgroup) ≤ c :=
    hc E.obj E.irreducible
  rw [← Plancherel.fixedVectors_rationalNormKernelAmbientLevel G E.obj.representation K]
    at hE
  let φ := fixedVectorsMap E.embedding K.toSubgroup
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply E.injective
    exact congrArg Subtype.val hxy
  have hlift := φ.lift_rank_le_of_injective hφ
  have hE' := Cardinal.lift_le_nat_iff.{max u v, v}.mpr hE
  exact Cardinal.lift_le_nat_iff.{v, max u v}.mp (hlift.trans hE')

/-- The assembly reduction holds. -/
theorem uniformAdmissibilityAssemblyReduction :
    UniformAdmissibilityAssemblyReductionStatement.{u, v} := fun hG hsc =>
  ⟨rationalPointsUniformAdmissibility_of_max.{u, v} hG,
    rationalNormKernelUniformAdmissibility_of_rationalPoints.{u, v} hG, hsc⟩

end Langlands.CuspidalSupport
