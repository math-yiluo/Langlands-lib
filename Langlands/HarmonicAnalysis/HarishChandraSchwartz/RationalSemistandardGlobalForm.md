# Actual integral global form on semistandard spectral families

Worker 268. This construction and statement unit supports unit 4 of Task
7258. Its principal target is
`Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalForm.PositiveFormStatement`.
It constructs the actual weighted integral form on the full smooth
finite-support family, proves scalar integrability, sesquilinearity and
actual `G × G` invariance, and states the remaining Hermitian/positive-
definite property under concrete conditions on the actual densities.
Its conditional invariant positive form retains exactly this integral.

The source is J.-L. Waldspurger (2003), *La formule de Plancherel pour les
groupes p-adiques*, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
VII.2, printed page 319 (PDF page 85), gives the weighted integral formula
and positive Hermitian `G × G`-invariant product on invariant families.
The present full-family formula is a derived extension of that same scalar
expression before invariant restriction. Finite-support algebra and the
published actual orbit-form transport justify this supporting interface.
Invariant restriction and VII.2.4 association formulas remain separate.

The field has arbitrary characteristic and independent universe `u`;
representation carriers have independent universe `uV`. The ambient group
scheme is affine, locally of finite type and connected reductive, with its
canonical rational-point topology. No ambient splitness, quasi-splitness,
positive rank or representation-carrier topology is imposed. The index,
actual Levi model, compact data, split-component morphisms, source measures,
cocharacter presentations and primitive scalar data retain precisely the
meanings of the preceding semistandard source modules.

The literal split-central quotients have their displayed Borel measurable
spaces and Haar measures `mu`. The input `mu.IsInvInvariant` is explicit,
as in the existing standard inverse-formal-degree product-core interface.
It concerns those actual quotient Haar measures and is not a chosen form
or a positivity conclusion. Both normality instances and affine split-
component schemes are retained from the source-measure API. Actual
valuation-image finite index remains an explicit structural obligation.
All continuation, generic irreducibility, inverse-scalar regularity and
other scalar inputs stay in the displayed `OrbitPacketData` witnesses;
that structure contains no form or output property.

`compactOpenCofinal_levi` proves the cofinality used by smooth duality on
each literal Levi. The actual closed model proves that this literal Levi
is closed. The preimage of the displayed compact picture under its closed
subtype embedding is compact and open, and the published
`CompactOpenSubgroup.cofinal` theorem supplies cofinality. No additional
cofinality assumption is introduced.

In namespace `RationalSemistandard.SourceForm`, `representativeForm` is
exactly `unitaryOrbitRepresentativeProductForm`, built from the existing
canonical inverse-formal-degree induced tensor form. It uses the actual
central subgroup, quotient Haar and square-integrability proof throughout
the orbit. No invariant positive form is freely supplied. `pairing` is
exactly the published `unitaryOrbitProductPairing` on the actual smooth
coherent orbit sections. `pairing_representative` evaluates it at every
actual inducing representative, preserving all equivalences and self-
twists. `continuous_pairing` uses the existing actual finite-torus orbit
continuity theorem.

The pointwise addition, scalar and conjugate-symmetry laws come from the
canonical representative form. The first argument is conjugate linear;
the second is complex linear. `smoothAction` is the published actual
coefficient action on this same component, and `pairing_action` specializes
its full product-group invariance.

`orbitDensity` is exactly the previously constructed actual source density
at the primitive scalar data. `integrable_pairing` multiplies this proved
continuous density and the continuous actual inverse-degree pairing on
the actual compact orbit, then integrates a bounded continuous scalar
function against the finite source-scaled measure. Thus scalar
integrability is proved; it is not a hypothesis.

`weightedOrbitForm` is the exact one-orbit scalar integral of density times
that pairing. Its additive and scalar laws move through the integral using
the proved integrability and pointwise pairing laws. `orbitSesquilinear`
bundles this integral itself as a conjugate-linear/linear map.
`weightedOrbitForm_action` integrates the pointwise action-invariance
identity. These arguments need no positivity assumption on the density.

`FiniteSupportSections.totalSesquilinear` is the internal algebraic sum of
specified sesquilinear component maps. It uses the proved `totalLinear`
utility in the second variable. Linear summands vanish off the second
input's finite literal support; first-variable conjugate linearity follows
from the same finite-support finsum laws. No topology or finiteness of the
whole index set is assumed.

`GlobalForm.componentForm` specializes the actual one-orbit integral at
each theta, using precisely its actual representative and square-
integrability proof. `rawGlobalForm` is the actual scalar expression

```text
B(psi', psi) = sum over theta of a(M)
  * integral over omega of mu(omega)
      * inverseFormalDegreeTensorPairing(psi'[theta], psi[theta])(omega).
```

The real weight `a(M)` is exactly the preceding source construction
`c^-2 gamma^-1 |W^M|/(|W^G| |P(M)|)`, embedded into complex scalars.
`rawGlobalForm_finsum` exposes this expression before its finite-finset
version. `rawGlobalForm_apply` proves that it is exactly the sum over the
second input's literal finite support. Terms vanish when either input
component is zero; using that second support is therefore legitimate.
The type of `rawGlobalForm` already proves sesquilinearity. It is not a
form chosen by positivity or pulled back through an assumed synthesis
isometry.

`component_action` identifies component evaluation of the published full-
family action with the same actual component action. `rawGlobalForm_action`
then proves actual `G × G` invariance by the one-orbit integral theorem
and pointwise equality of finsum terms. This is a proved law, not an
assumption or a property of an arbitrary selected action.

`OrbitPoint` and `componentDensity` name exactly the actual orbit and
actual density used by these integrals. `DensityNonnegative` is the
concrete scalar obligation that each value of that density is a
nonnegative real complex number. `DensityPositiveDense` is the concrete
obligation that its positive-real-value set is dense in each actual orbit.
They wrap these exact density expressions; they introduce no free weight
and assume no property of the global form. Their proofs remain with the
existing scalar/density program and its semistandard transports. Strict
positivity at every unitary point is not required.

`PositiveFormStatement` consumes those concrete scalar-density obligations,
actual maximal splitness and the exact separately owned
`SemistandardSpectralFiberFinitenessStatement`. It concludes Hermitian
symmetry, nonnegativity of every diagonal real part and definiteness of
this particular integral form. The source weights' positivity is already
proved from the corresponding geometric hypotheses in the preceding
source-constant adapter. No one of the target's form conclusions is an
input.

`invariantPositiveForm` is conditional on that named target and the
explicit scalar/geometric witnesses. It sets its inner product to
`rawGlobalForm` itself. Additivity and conjugate homogeneity use the
already constructed sesquilinear map; product-group invariance is the
proved theorem above. The target supplies only the remaining Hermitian
and positive-definite fields. `invariantPositiveForm_inner` proves by
reflexivity that the constructed form is exactly the actual integral.

This unit does not yet give the full source-normalized comparison with
`standardLeviPlancherelOrbitProductCore`, the formal-degree/model transport,
invariant-subspace restriction, association-class construction or VII.2.4
representative sums. Those remain Task 7258 obligations. Source constants
and full compact/model/representative choice comparisons remain as stated
in the preceding units. No VII.2.5 isometry, synthesis isometry, VIII
Fourier-family finiteness, surjectivity or inversion is proved or assumed.
All existing owners and Task 4534 controls remain unchanged.
