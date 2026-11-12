import Langlands.Representation.Exponents.MaximalLeviEndomorphismAssembly
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # The endomorphism dichotomy for inductions from supercuspidals of maximal Levis

Renard III.2.5 and VI.5.3, as used in VII.1.3. -/

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v

/-- Renard III.2.5 and VI.5.3: for an actual maximal proper rational parabolic and an
irreducible supercuspidal `ρ` of `M(F)`, every endomorphism of `i_P^G ρ` is a scalar unless
some `g ∈ G(F)` outside the Levi image normalizes the Levi through an automorphism `φ` with
`ρ ∘ φ(F) ≃ ρ`. -/
theorem maximalLeviSupercuspidalInductionEndomorphism :
    MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v} :=
  maximalLeviSupercuspidalInductionEndomorphism_of_geometricLemma
    representedGeometricLemma.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
