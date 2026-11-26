import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Constant terms of automorphic functions on parabolic quotients are automorphic -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- For standard parabolics `Q ⊆ P` of a compatible standard family, the constant term along `Q`
of an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` is an automorphic function on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`, for the same subgroup `Kinf` of `G(F_∞)` and the same closed matrix
embedding `rho` (Mœglin–Waldspurger I.2.6 and I.2.17; Bernstein–Lapid §6.2). -/
def ConstantTermAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsClosedSubgroup rho →
    ∀ (P Q : StandardIndex F G fam.i fam.ν), Q ≤ P →
      ∀ φ : AdelicGroupPoints F G → ℂ, fam.IsAutomorphicOn hsmooth Kinf rho P φ →
        fam.IsAutomorphicOn hsmooth Kinf rho Q (fam.constantTerm Q φ)

end Langlands.Global
