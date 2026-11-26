import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Harish-Chandra's reproducing kernel for automorphic functions on parabolic quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Harish-Chandra's reproducing kernel for automorphic functions on `U_Q(𝔸) M_Q(F) \ G(𝔸)`
(Mœglin–Waldspurger I.2.17, Lemma, for one function; Harish-Chandra 1966, §8, Theorem 1, at the
archimedean places). For a standard parabolic `Q` of a compatible standard family and every
function `φ` automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, there is a smooth compactly supported test
function `α` on `G(𝔸)` (`IsAdelicTestFunction`) whose left translates by `K_∞ = K ∩ G(F_∞)`
span a finite-dimensional space and with `∫ α(a) φ(g a) da = φ(g)` for every `g`, for the Haar
measure of `G(𝔸)` (`rightConvolution`). The compact serves the minimal standard parabolic and its
intersections with the standard Levis are maximal. -/
def ParabolicReproducingKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (Q : StandardIndex F G fam.i fam.ν) (φ : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth Kinf rho Q φ →
          ∃ α : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G α ∧
            FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf =>
              fun h : AdelicGroupPoints F G => α (ofInfinite F G k * h))) ∧
            rightConvolution F G α φ = φ

end Langlands.Global
