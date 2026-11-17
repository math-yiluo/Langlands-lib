import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeProof

/-!
# The smooth-family representer over affine bases of finite type over `ℤ`: proof

Every abelian scheme over `Spec R`, for a commutative ring `R` of finite type over `ℤ`,
admits an abelian-scheme parameter carrying an actual universal rigidified smooth-family
algebraically trivial family on all quasi-separated tests. The proof applies the assembly theorem
`finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme` to the published
unconditional proof `finiteTypeAbelianPicardSheafScheme` that the fppf Picard class sheaf
is represented by a scheme.
-/

universe u

namespace Langlands.AbelianScheme

/-- For every commutative ring `R` of finite type over `ℤ` and every abelian scheme `A` over
`Spec R`, there are an abelian scheme `B` over `Spec R` and a rigidified family on `B.X`
that is universal for smooth-family classes on all quasi-separated tests. -/
theorem finiteTypeSmoothFamilyAbelianRepresentability :
    FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} :=
  finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme
    Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafScheme.{u}

end Langlands.AbelianScheme
