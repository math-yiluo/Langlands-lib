# Charts on affine opens, their structure maps, and localizations

- `map_sInf_eq`: localizing away from an element sends the intersection of a set of primes to the
  intersection of the extended primes not containing the element.
- `restrict_appTop`, `base_ofAffineOpen`, `restrict_appTop_eq_base`, `base_comp`, `pointHom_comp`:
  compatibility of the structure maps `AffineChart.base` and of `AffineChart.pointHom` with
  composition of morphisms and with charts on affine opens.
- `isIso_app_of_isIso_restrict`: a morphism which is an isomorphism over an open `V` induces an
  isomorphism on sections over `V`.
- `isLocalization_appLE`: if `g : X₂ ⟶ X` is an isomorphism over a basic open `D(s)` of an affine
  open `U`, the sections of `X₂` over `g⁻¹ D(s)` are the localization away from `s` of the sections
  of `X` over `U`.

Internal infrastructure for transporting charts, chart primes and centres along the modifications in
the induction (`DvrSmoothening.Induction`).
