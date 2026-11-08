# Spectral presentations from irreducible admissible finite slices

Module: `Langlands.Automorphic.CuspidalSlicePresentation`. Author: Worker 1827.

## Main results

* `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`. Take a number field
  `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`, `r : ℕ`,
  `S : CuspidalOperatorRealization F r`, and an actual finite slice `A : S.FiniteSlice` with
  `A.subspace.IsIrreducible` and `Langlands.IsAdmissible A.subspace.representation`.
  Then there is `P : CuspidalSpectralPresentation.{uF, uF} S` such that every actual local
  component `P.localComponent v` is irreducible and admissible, at **every** finite place.
  `P` is a complete presentation: finite slice `A`, factors with carriers in `uF`, reference
  vectors, a genuine `FiniteTensorPresentation` and normalized `UnramifiedData`.
* `CuspidalOperatorRealization.slicePresentation`: the presentation chosen from this theorem.
  `slicePresentation_localComponent` records its all-place irreducibility and admissibility.
* Local lemmas in namespace `Langlands.Global.FiniteAdelicGL`, for the completion topology of
  `FiniteLocalGL F (r + 1) v`:
  - `canonical_totallyDisconnected`: total disconnectedness of the canonical p-adic matrix
    topology. The field is a nonarchimedean ring, and the unit group embeds in the matrices.
  - `localGL_flathTopology`: `T2Space`, `LocallyCompactSpace`, `TotallyDisconnectedSpace`, and
    compactness of `localIntegral F (r + 1) v`.
  - `localGL_exists_sphericalHeckeCommutative`: for the Borel structure there is a regular
    Haar measure `μ` with `SphericalHeckeCommutative μ (localIntegral F (r + 1) v).toSubgroup`.

These are the inputs of Flath's theorem in the form of the Library statement
`FlathRestrictedProductExistenceStatement`.

## The implemented proof

1. **Topology comparison.** The Library proves `localGL_topology_eq`: the completion topology
   equals `(CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)`. It also
   proves `localIntegral_eq_sphericalSubgroup`: the integral subgroup is the canonical
   spherical subgroup. Each local lemma is proved for an arbitrary topology `τ` equal to the
   canonical one (`subst`) and then applied to the completion topology. In the canonical
   topology the Library supplies Hausdorffness, local compactness and compactness of the
   spherical subgroup (`sphericalOpenSubgroup_isCompact`). The measure is
   `Unramified.sphericalHaar`, which is Haar and regular (`normalizedCompactOpenHaar_regular`).
   Commutativity is Gelfand's theorem `Unramified.sphericalHeckeAlgebra_mul_comm`: two
   bi-invariant Hecke functions form elements of the corner
   `Hecke.HeckeAlgebra.Corner`, which is the bi-invariant subalgebra with its inherited
   multiplication.
2. **Pull back to the restricted product.** The finite action of `A` is composed with the
   inverse of `FiniteAdelicGL.restrictedProductEquiv` (a `≃ₜ*`), giving a representation `π` of
   the restricted product of the local groups with respect to the integral subgroups.
   Admissibility and irreducibility transfer by the Library's
   `isAdmissible_comp_continuousMulEquiv` and `isIrreducible_comp_continuousMulEquiv_iff`.
3. **Flath.** `Langlands.flathRestrictedProductExistence` gives admissible irreducible local
   factors `ρ v` on `W v : ModuleCat.{uF} ℂ`, a finite set `E`, nonzero integral-fixed
   reference vectors off `E`, and an equivalence of `π` with the restricted tensor product.
4. **Assembly.** The factors are bundled as `SmoothRep.of (ρ v)`. The references are
   `rr.family v`, which is zero on `E` and the Flath vector off `E`. The inverse Flath
   equivalence, read through `restrictedProductEquiv`, intertwines the Library's
   `tensorRepresentation` with the finite action of `A`; this is the `FiniteTensorPresentation`.
   The spectral exceptional set is `E`, and the unramified data are
   `FiniteTensorPresentation.unramifiedData`, constructed from irreducibility and admissibility
   of the factors. The all-place conclusion is
   `localComponent_isIrreducible_iff` and `localComponent_isAdmissible_iff`.

## Provenance

Internal and derived. The analytic and representation-theoretic content is the published
Flath theorem, Gelfand's commutativity theorem and the published comparison of the completion
and canonical p-adic models. This module only checks hypotheses and assembles the existing
structures. It is the reduction "irreducible admissible finite slice ⇒ all-place irreducible
admissible presentation" described in the Markdown of
`CuspidalAllLocalIrreduciblePresentation` (Getz–Hahn 2024, Theorem 5.7.1 and Theorem 6.3.7, as
a route); no source theorem beyond those Library results is used.
