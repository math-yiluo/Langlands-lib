# The two valuations on ℚ_p are equivalent

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's local-field structure on ℚ_p, `padicLocalField p`, uses the valuation coming from the discrete valuation ring ℤ_p, while Mathlib's local-field API uses `ValuativeRel.valuation ℚ_[p]`. The file shows that the two are equivalent valuations and uses this to transport valuation extensions between them.

- `padicDVRValuation_isEquiv_valuativeRelValuation`: `padicDVRValuation p` is equivalent to `ValuativeRel.valuation ℚ_[p]`; both have valuation at most 1 exactly on elements of norm at most 1.
- `padicLocalField_valuation_isEquiv_valuativeRelValuation`, `padicLocalField_valuation_isEquiv_localCompleteDVF` and its symmetric form `localCompleteDVF_valuation_isEquiv_padicLocalField`: the same comparison for the valuation of `padicLocalField p`, against Mathlib's valuation and against `localCompleteDVF ℚ_[p]`, the complete discretely valued structure the library derives from the topology.
- `padicLocalFieldValuation_hasExtension_of_localCompleteDVF` and `localCompleteDVFValuation_hasExtension_of_padicLocalField`: for a field `E` over ℚ_p, a valuation on `E` extends one of the two base valuations if and only if it extends the other, stated as two implications between `HasExtension` instances.

Watch for: the results are equivalences of valuations (`IsEquiv`), not equalities.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PadicValuationComparison.lean`: the Lean file is the source byte for byte (SHA-256 `af705e6eef79ea130cf86f7549274f52b64fb069dfce69ff27a032762b2fa45a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
