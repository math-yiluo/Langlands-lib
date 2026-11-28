import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.AffineCechDeRhamInfinitesimalMorphism
import Mathlib.RingTheory.Artinian.Ring

/-! # Realizing a lifted degree-one Hodge summand by an actual marked lift -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AffineCechDeRham
open scoped Pointwise

namespace Langlands.AbelianScheme

/-- A finite free direct summand lifting the first Hodge step can be
realized by a marked abelian-scheme lift with compatible affine covers. -/
def ArtinianHodgeSummandRealizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R] [Algebra ℚ R]
    (I : Ideal R) (hI : I * I = ⊥) (_ : IsLocalRing.maximalIdeal R * I = ⊥)
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (U : Scheme.AffineOpenCover.{u} A.X.left) [Finite U.I₀]
    (M : Submodule R (H1 A.X.hom U)),
    Module.Finite R M → Module.Free R M →
    Module.Finite R (H1 A.X.hom U ⧸ M) → Module.Free R (H1 A.X.hom U ⧸ M) →
    M ⊔ I • ⊤ = hodgeF1 A.X.hom U ⊔ I • ⊤ →
    ∃ (B : AbelianScheme (Spec (CommRingCat.of R)))
      (e : (baseChange (quotientBaseMap I)).obj B ≅ (baseChange (quotientBaseMap I)).obj A)
      (V : Scheme.AffineOpenCover.{u} B.X.left),
      ∃ (hV : Finite V.I₀),
        letI := hV
        let m : quotientReduction B.X.hom I ⟶ A.X.left :=
          hom e.hom ≫ quotientReductionMap A.X.hom I
        ∃ (β : V.I₀ ≃ U.I₀)
          (hβ : ∀ j, quotientReductionMap B.X.hom I ⁻¹ᵁ coverOpens V j ≤
            m ⁻¹ᵁ coverOpens U (β j))
          (hm : m ≫ A.X.hom = quotientReductionMap B.X.hom I ≫ B.X.hom),
          (∀ j, m ⁻¹ᵁ coverOpens U (β j) ≤ quotientReductionMap B.X.hom I ⁻¹ᵁ coverOpens V j) ∧
          let P := reductionPullbackH1 B.X.hom I hI m hm β hβ
          Function.Bijective P ∧ (hodgeF1 B.X.hom V).comap P = M

end Langlands.AbelianScheme
