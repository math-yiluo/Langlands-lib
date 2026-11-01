import Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityStatement
import Langlands.AlgebraicGeometry.FiniteSeparatingSectionsProof
import Langlands.AlgebraicGeometry.LinearSystemMorphismProof
import Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Proof of the very-ampleness criterion

Finitely many sections `s 0, …, s n` without common zero whose `K`-span separates rational
points and nonzero rational tangent vectors define a morphism `φ : X ⟶ ProjectiveSpace K n`
over `Spec K`. Its vanishing dictionary turns span separation into injectivity on rational
points and triviality of the rational tangent kernel. Since `X` is proper and projective
space is separated, `φ` is proper, so the closed-immersion criterion applies.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry

/-- The very-ampleness criterion follows from the finite separating family, the morphism to
projective space with its vanishing dictionary, and the closed-immersion criterion for proper
morphisms. -/
theorem separatingLineBundleHProjectivity_of (hA : FiniteSeparatingSectionsStatement.{u})
    (hB : LinearSystemMorphismStatement.{u})
    (hC : ProperRationalImmersionClosedImmersionStatement.{u}) :
    SeparatingLineBundleHProjectivityStatement.{u} := by
  intro K _ _ X p L hp hL
  obtain ⟨n, s, hbpf, hpts, htan⟩ := hA K X p L hp hL
  obtain ⟨φ, hφ, h1, h2⟩ := hB K X p L n s hbpf
  have : IsProper (φ ≫ projectiveSpaceToSpec K n) := by rw [hφ]; exact hp
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceToSpec K n)
  have : LocallyOfFiniteType p := by rw [← hφ]; infer_instance
  refine ⟨n, φ, ?_, hφ⟩
  refine hC K X (ProjectiveSpace K n) p (projectiveSpaceToSpec K n) φ hφ ?_ ?_
  · intro x y hx hy hxy
    by_contra hne
    obtain ⟨c, hcx, hcy⟩ := hpts x y hx hy hne
    exact hcy (((h1 x y hx hy).mp hxy) c hcx)
  · intro x hx t ht htx
    by_contra hne
    obtain ⟨c, hcx, hct⟩ := htan x hx t ⟨ht, hne⟩
    exact hct (((h2 x t hx ht).mp htx) c hcx)

/-- A line bundle on a proper scheme over an algebraically closed field whose complete linear
system separates rational points and rational tangent vectors embeds the scheme as a closed
subscheme of a projective space over the field. -/
theorem separatingLineBundleHProjectivity : SeparatingLineBundleHProjectivityStatement.{u} :=
  separatingLineBundleHProjectivity_of finiteSeparatingSections.{u} linearSystemMorphism.{u}
    properRationalImmersion_isClosedImmersion.{u}

end Langlands.AlgebraicGeometry
