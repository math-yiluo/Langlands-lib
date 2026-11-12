import Langlands.Representation.Exponents.MaximalLeviHomAssembly
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # The morphism dichotomy between inductions from supercuspidals of maximal Levis: proof

Renard III.2.5 and VI.5.3, as used in VII.1.3. -/

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v

/-- Renard III.2.5 and VI.5.3: for an actual maximal proper rational parabolic and
irreducible supercuspidal `τ, τ'` of `M(F)`, a nonzero morphism `i_P^G τ' → i_P^G τ` forces
`τ' ≃ τ`, or `τ ≃ τ' ∘ φ(F)` for an automorphism `φ` of `M` induced by some `g ∈ G(F)`
outside the Levi image. -/
theorem maximalLeviSupercuspidalInductionHom :
    MaximalLeviSupercuspidalInductionHomStatement.{u, v} :=
  maximalLeviSupercuspidalInductionHom_of_geometricLemma representedGeometricLemma.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
