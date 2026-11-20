import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # Existence of Haar measures on `M(𝔸)` compatible with the Iwasawa decomposition

Mœglin–Waldspurger I.1.13: for a parabolic `P = MU` and a maximal compact `K` with
`G(𝔸) = P(𝔸) K`, there is a Haar measure `μ_M` on `M(𝔸)` such that
`∫_G f = ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dμ_M(m) dk`, with Mathlib's Haar measure on `G(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Existence of an Iwasawa-compatible Haar measure on `M(𝔸)` (Mœglin–Waldspurger I.1.13). Let
`G` be connected reductive over a number field `F`, `p : P → G` a parabolic with geometric
unipotent radical `iU : U → P` and rational Levi `l : M → P` admitting a compatible root
presentation, and `K` a maximal compact subgroup of `G(𝔸)` with `P(𝔸) K = G(𝔸)`. Then some Haar
measure `μ_M` on `M(𝔸)` satisfies `IsIwasawaCompatibleMeasure`: for every compactly supported
continuous `f` on `G(𝔸)`, `∫_G f = ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dμ_M(m) dk`, where `dg` is
Mathlib's Haar measure, `du` the Haar measure with `vol(U(F) \ U(𝔸)) = 1` and `dk` the Haar
probability measure on `K`. -/
def IwasawaCompatibleMeasureExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    ParabolicRootPresentation p l a →
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K),
      IsMaximalCompactSubgroup F G K →
      ∃ μM : Measure (AdelicGroupPoints F M), μM.IsHaarMeasure ∧
        IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM

end Langlands.Global
