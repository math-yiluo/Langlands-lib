# Canonical Galois comparison for actual conjugate apartments

This internal supporting result compares two descended torus embeddings in the
same affine group over a field. A supplied actual transporter identifies their
upper-field valuation apartments. The transported apartment inherits stability
under the canonical coefficient action, and the actual same-group equivariant
comparison of reduced buildings intertwines those coefficient actions. Every
coefficient-fixed point consequently has a fixed preimage. The result is valid
in arbitrary universe `u`, for arbitrary field extensions and in both
characteristics.

## Exact scope

`Langlands.Geometry.Building.ConjugateApartmentGaloisComparisonStatement` is a
`Prop` definition, proved by `conjugateApartmentGaloisComparison`. Let `k ⊆ K`
be a specified field extension. Supply two commutative group schemes `T,T'`
over `k`, an affine group scheme `G` over `k`, and maps `i:T→G`, `j:T'→G` whose
upper-field underlying scheme maps are monomorphisms. The statement does not
need a separate torus predicate: the actual supplied apartment data provides
all valuation-class hypotheses used in this comparison.

Supply an isomorphism `e:T_K≅T'_K`, a point `g∈G_K(K)` and the literal equation

```
i_K ≫ innerIso(g).hom = groupHom(e.hom) ≫ j_K.
```

Supply a weight function `ω:Kˣ→ℝ` and `D:KPApartmentData i_K ω`, stable under
all actual coefficient automorphisms `σ:K≃ₐ[k]K`. Put
`E = D.transport e (innerIso g) h`. The conclusion constructs a proof `hE` of
`GaloisStable k K j E`. Write `f = D.conjugateReducedBuildingEquiv e g h`, which
is the published equivalence `E.ReducedBuilding ≃ D.ReducedBuilding`. Then

```
σ_D(f(q)) = f(σ_E(q))
```

for every coefficient automorphism and every point `q` of the transported
quotient. For every `y` fixed by all `σ_D`, there is an actual `q` fixed by all
`σ_E` such that `f(q)=y`. The construction uses `q=f.symm(y)`. There is no
assumption of fixed coordinates for a representative of `y`.

The source and target actions are exactly
`KPApartmentData.galoisQuotientAction` on their respective original
root-valuation quotients. The comparison `f` also intertwines the same full
rational-point action, by the published
`conjugateReducedBuildingEquiv_smul`. Thus subsequent applications can transfer
point-fixing subgroups along the comparison.

## Canonical coefficient transporter

`torusIsoGaloisTransport k K σ e` uses the canonical commutative-group-scheme
descent isomorphisms, with the inverse descent on the source, base change of
`e` along `galoisBaseMap k K σ`, and forward descent on the target.
`characterCongr_torusIsoGaloisTransport` proves that the induced character
transport commutes with the canonical Galois representations. Its proof is
`StarActionIndependence.descentTransport_inv_comp` from
`GroupScheme.Reductive.StarActionIndependenceProof`, after unfolding the two
character congruence applications.

`conjugateTorusSquare_galois` proves that the actual point
`rationalConjugate k K G σ g` satisfies the same transporter equation, using
`torusIsoGaloisTransport k K σ e`. It applies the published
`StarActionIndependence.IsConjugatingPoint.baseChange_descent_of_eq` from
`GroupScheme.Rational.TorusConjugatorGaloisCocycle` and
`rationalConjugate_eq_baseChange_descent` from
`GroupScheme.Rational.NormalizerGaloisAction`. Hence the target transporter is
constructed from the actual coefficient conjugate; it is not an independent
hypothesis.

`RootFunctionFamily.galoisAction_transport_inner` establishes covariance of
the full root-function family. Surjectivity of character transport and the
coefficient action lets the proof evaluate at transported characters and
points. Multiplicativity of `rationalConjugate` identifies conjugation by `g`
with conjugation by `σg` after coefficient transport. The character identity
and `transportEquiv_apply_map` finish the pointwise equality. This is an
equality of the full families on all character and rational-point arguments.

## Apartments and the same quotient actions

`KPApartmentData.galoisStable_transport_inner` takes a family in `E.carrier`
and writes it as the transport of a family in `D.carrier`. The covariance
lemma gives its coefficient image as transport by the coefficient-conjugated
pair `(eσ,σg)`. Original stability supplies membership for the source family.
The published `transport_conjugation_independent` identifies the resulting
entire target datum with `E`. This proves target stability without assuming it.

`galoisAction_apartmentTransport_inner` applies `Apartment.ext` and the
family covariance identity. The comparison
`conjugateApartmentIdentification` is literally identity on valuation
families. The equation therefore identifies the coefficient action on `E`
with transport using `(eσ,σg)`, followed by this identity-on-families comparison.

`conjugateApartmentMap_galois` writes every target apartment point as an
`apartmentTransportEquiv` image. The published
`conjugateApartmentMap_transport` realizes that image as `g` acting on the
original apartment map. Semilinearity of `galoisQuotientAction_smul` and
`galoisQuotientAction_apartmentMap` gives the realization using `σg`.
`conjugateApartmentMap_independent` then identifies it with the original
realization evaluated at the actual target coefficient image.

`conjugateReducedBuildingEquiv_galois` writes every target quotient point as
`u` acting on an apartment point, using
`ApartmentQuotient.exists_smul_apartment`. It applies the existing same-group
equivariance of `f`, coefficient semilinearity on both quotients, and the
apartment comparison just proved. Finally,
`exists_galoisFixed_conjugate_preimage` uses injectivity of `f` and this
equivariance to prove fixedness of its inverse image. The final theorem
packages target stability, quotient equivariance and fixed-point transfer.

## Provenance and scope

This is an internal derivation from the named published Library constructions;
it claims no independent translation of a literature statement. Its direct
imports are `ConjugateApartmentIndependence`,
`GaloisApartmentQuotientAction`, `NormalizerGaloisAction`, and
`TorusConjugatorGaloisCocycle`. No building-descent theorem or conditional
building-descent statement is used. In particular no unramified building-descent
statement of the Library, such as `UnramifiedBuildingDescentStatement` or
`UnramifiedApartmentDescentStatement`, is in the project import closure.

The statement retains the actual embeddings, transporter, valuation datum and
source stability. It does not choose a maximal split torus over the base field,
construct an integral model or a residue quotient, or prove the main
`UnramifiedFixedPointSplitTorusStatement`. Its role is to transfer the
prescribed fixed point to a reference descended apartment chosen separately,
while preserving the original full rational-point action.
