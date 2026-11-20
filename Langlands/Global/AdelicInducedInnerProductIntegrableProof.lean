import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicInducedInnerProductIntegrableStatement

/-! # Proof of `InducedInnerProductIntegrableStatement`

For `φ, ψ ∈ A^2_P` the integrand of `inducedInnerProduct` is integrable on `K × M(F) \ M(𝔸)`.
The work is done in `Langlands.Global.AdelicInducedInnerProductIntegrable`; this module
specializes it to the data of the statement. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Langlands.GroupScheme

set_option autoImplicit false

namespace Langlands.Global

/-- Absolute convergence of the inner product `(φ, ψ)_P` on `A^2_P` (Lapid 2011, §2), in the
Iwasawa form of `inducedInnerProduct`. -/
theorem inducedInnerProductIntegrable : InducedInnerProductIntegrableStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA _ π _ _ hlπ K hK N d rho
    hsmooth hcalc _ _ μM _ _ n e β hβc hβs φ ψ hφ hψ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  exact InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand e
    r.isCompatible.levi.isConnectedReductive r.isCompatible.splitComponent hA hlπ μM hβc hβs
    hφ hψ

end Langlands.Global
