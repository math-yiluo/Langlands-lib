# Nonzero restriction of incident roots in recovered apartment models

This derived internal unit combines the actual recovered apartment tori, their
generic and residue comparison squares, special-fibre quotient recovery,
incident-root survival and the finite-residue root restriction criterion. Its
provenance is composition of the imported constructions and theorems; it adds
no independent literature assertion. All declarations have arbitrary universe
parameter `u`, with no restriction on field or residue characteristic.

Let F be a valued topological field satisfying
`IsNonarchimedeanLocalField F`, and write K for `inertiaFixedField F` and A for
`fixedFieldIntegers F`. Supply an affine group scheme G over F, a commutative
group scheme T over F and a morphism iT into G whose pullback to K is
monomorphic on underlying schemes. Let D be the supplied `KPApartmentData` for
this upper morphism and the maximal-unramified integer valuation, let Ω be a
subset of its apartment, and let `M : RecoveredApartmentFixerModels D Ω`.
These data contain actual lower and upper relative-component models and their
specified unramified recovery. No lower-field building is supplied or used.

For any supplied `Q : SpecialFibreQuotientData M.lower`, the definition
`M.recoveredQuotient Q` changes residue coefficients from the residue field of
F to that of A and transports along the actual
`M.recovery.neutralResidueBaseChangeIso`. Its target is the actual upper neutral
special fibre. Its quotient group is literally the residue coefficient
pullback of Q's quotient group. The theorem
`recoveredQuotient_isReductiveQuotient` preserves the full predicate
`Q.IsReductiveQuotient`, including the unipotent radical, represented fppf
quotient and connected reductivity of the quotient. The proof uses the
published algebraicity and separability of the unramified residue extension
and the general supplied-isomorphism quotient construction. No quotient
existence is asserted.

For the remaining comparison results supply a centralizer datum C for the
upper morphism and the full compatibility proof
`hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`.
Also supply a commutative group scheme S over F, its morphism iS into G,
`hiS : IsMaximalSplitTorus iS`, and an actual morphism `f : S ⟶ T` satisfying
`hf : groupHom(f) ≫ iT = iS`. Assume `hG : IsConnectedReductive G` and
maximal splitness hiT of the actual pullback of iT to K. These are additional
hypotheses, not consequences of recovery.

`lowerApartmentTorus_quotient_isMaximalSplitTorus` shows that the actual lower
apartment torus remains maximal split after composing its special-fibre
inclusion with the projection of any valid supplied lower Q. This theorem uses
C, hDC, hiS, hf and hG. The theorem
`upperNeutralApartmentTorus_quotient_isMaximalTorus` shows that the actual upper
neutral apartment torus remains maximal after composing its special-fibre
inclusion with the projection of any valid supplied upper quotient. This one
uses C, hDC, hG and hiT. In both proofs smoothness and connectedness of the
unipotent kernel and smoothness of the reductive quotient come from the full
quotient-validity predicate. The upper residue field is algebraically closed;
the lower residue field is perfect. The imported unipotent-quotient maximality
theorems apply to the actual inclusions and projections.

`apartmentTorusMap_comp_recoveredQuotient` proves the exact residue coefficient
square for the actual integral map `M.apartmentTorusMap C hDC hiS hf hG hiT`.
Starting on the residue coefficient pullback of the lower torus, first apply
`apartmentTorusSpecialFibreIso.hom`, then the special-fibre map of this integral
map, then the upper torus inclusion and the recovered quotient projection.
The composite equals the residue coefficient pullback of the lower torus
inclusion followed by Q's projection. Quotient validity is unnecessary for
this identity. The proof postcomposes the already proved actual torus-inclusion
square with the recovered projection, then uses the recovery projection
identity, associativity and functoriality.

Finally, `incident_root_restrict_ne_zero` retains all these torus and
compatibility hypotheses, a supplied lower Q with its full validity proof,
a supplied `E : UnramifiedZeroDatum F (baseChanged F K G)`, an apartment point
x, and the exact global equality

```text
M.upper.neutral.integralPoints =
  E.zeroPoints ∩ D.pointwiseFixer (D.apartmentMap '' {x}).
```

It also retains `UnramifiedRootPositiveReductionStatement.{u}` as an explicit
hypothesis. For an actual upper relative root a, an ordinary affine root ψ of
D with `ψ x = 0`, and the exact equality `ψ.linear = rootForm iT_K a`, its
conclusion is

```text
(coefficient pullback of f) ≫ a.val ≠ 0.
```

The implemented proof recovers Q on the upper special fibre, obtains the
specialization of this same prescribed character a as an actual upper quotient
root from `unramified_quotient_root_of_incidentAffineRoot`, and applies
`generic_restriction_ne_zero_of_finite_residue_root`. The lower quotient is
connected reductive over the finite residue field, and hence quasi-split.
The two maximality results and the exact residue square provide that criterion's
remaining inputs. It yields nonvanishing along the generic map of the actual
integral torus morphism. The exact identity
`genericFibreMap_apartmentTorusMap` identifies that map with the coefficient
pullback of f, giving the stated conclusion.

The global neutral-fixer equality and positive-reduction hypothesis are not
proved here. The unit supplies neither recovered models nor reductive quotients
from scratch, and does not by itself prove the special-apartment chamber
statement.
