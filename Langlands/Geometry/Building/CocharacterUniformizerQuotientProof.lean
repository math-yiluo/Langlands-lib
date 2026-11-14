import Langlands.Geometry.Building.CocharacterUniformizerQuotientStatement
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Actual integral and common-uniformizer quotients: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- The actual lattice quotient agrees with the image of the uniformizer
subgroup in the rational-point quotient, on every representative. -/
theorem quotientComparison : QuotientComparisonStatement.{u} := by
  intro F _ _ _ _ A T hT f
  let P := (RealTorusSpace.cocharacterMapInt f).range
  let N := (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))
  let q := QuotientGroup.mk' N
  have hnat (c : cocharacterLattice A) :
      rationalPoints.map (CommGroupScheme.groupHom f)
        (latticeSection F A (Multiplicative.ofAdd c)) =
      latticeSection F T (Multiplicative.ofAdd (RealTorusSpace.cocharacterMapInt f c)) :=
    Plancherel.RenardCartan.uniformizerSection_naturality A f c
  have hzero (c : cocharacterLattice T) :
      q (latticeSection F T (Multiplicative.ofAdd c)) = 1 ↔ c ∈ P := by
    change (↑(latticeSection F T (Multiplicative.ofAdd c)) :
      rationalPoints T.toGrp ⧸ N) = 1 ↔ c ∈ P
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, hab⟩
      refine ⟨b.toAdd, ?_⟩
      apply Multiplicative.ofAdd.injective
      apply (isUniformizerLatticeSection F T hT).1
      exact (hnat b.toAdd).symm.trans hab
    · rintro ⟨b, rfl⟩
      exact ⟨latticeSection F A (Multiplicative.ofAdd b),
        ⟨Multiplicative.ofAdd b, rfl⟩, hnat b⟩
  let r : Multiplicative (cocharacterLattice T) →* (CA F T).map q :=
    { toFun := fun c => ⟨q (latticeSection F T c),
        ⟨latticeSection F T c, ⟨c, rfl⟩, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro c d; apply Subtype.ext; simp }
  let g := r.toAdditiveRight
  have hker : P.toAddSubgroup = g.ker := by
    ext c
    change c ∈ P ↔ r (Multiplicative.ofAdd c) = 1
    rw [Subtype.ext_iff]
    exact (hzero c).symm
  have hsurj : Function.Surjective g := by
    intro b
    obtain ⟨a, ⟨c, rfl⟩, hab⟩ := b.toMul.property
    refine ⟨c.toAdd, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hab
  refine ⟨AddEquiv.toMultiplicativeLeft
    (QuotientAddGroup.liftEquiv P.toAddSubgroup hsurj hker), ?_⟩
  intro c
  rfl

end Langlands.GroupScheme.CocharacterUniformizer
