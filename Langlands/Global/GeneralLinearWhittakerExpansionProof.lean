import Langlands.Global.SmoothWhittakerExpansion.Assembly
import Langlands.Global.SmoothWhittakerExpansion.Torus
import Langlands.Automorphic.GroupSchemeCuspidalEnvelopingAction
import Langlands.Automorphic.GroupSchemeConstantTermEnvelopingProof

/-! # Proof of the Whittaker expansion of smooth cusp forms on `GL_{r+1}`

`WhittakerExpansionStatement` (Getz–Hahn, Theorem 11.3.6; Cogdell 2004, Theorem 1.1) follows
from `SmoothWhittakerExpansion.whittakerExpansionStatement_of`. Its two hypotheses are supplied
as follows. Enveloping derivatives of cuspidal functions are cuspidal by
`generalLinearCuspidal_envelopingAction` with the proved `adelicConstantTermEnveloping`. The
change of generic character is `SmoothWhittakerExpansion.exists_cosetEquiv_genericCharacter`.
See `GeneralLinearWhittakerExpansionProof.md`. -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- **The Whittaker expansion of smooth cusp forms on `GL_{r+1}`** (Getz–Hahn, Theorem 11.3.6;
Cogdell 2004, Theorem 1.1). -/
theorem whittakerExpansion : WhittakerExpansionStatement.{u} :=
  SmoothWhittakerExpansion.whittakerExpansionStatement_of
    (fun F _ _ _ n u _ hf =>
      Automorphic.GroupSchemeFunctions.generalLinearCuspidal_envelopingAction F n
        Automorphic.GroupSchemeFunctions.adelicConstantTermEnveloping u hf)
    (fun F _ _ r ψ hψ m hm =>
      SmoothWhittakerExpansion.exists_cosetEquiv_genericCharacter F r ψ hψ m hm)

end Langlands.Global
