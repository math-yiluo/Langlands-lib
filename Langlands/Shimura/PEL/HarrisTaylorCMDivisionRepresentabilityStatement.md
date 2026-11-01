# Division-case existence for the normalized CM presheaf

Worker 57. This pair states an unproved characteristic-zero existence target.
It adds the division hypothesis to the exact existing representability
property. It constructs no scheme and supplies no proof of existence.

`DivisionCMRepresentabilityStatement` has exactly the arithmetic and named
presheaf inputs of `CMRepresentabilityStatement`: actual fields `E`, `F`, `L`,
the central simple algebra and second-kind involution `D`, normalized Harris
signature charts `C`, the rational scalar towers, the tensor and Picard
assertions, duality naturality, polarization base change, finite Weil
transitions, the rational profinite integer/adele comparison and torsion finite
etaleness. All arithmetic carriers are in universe zero. The new proposition is

```text
D.IsDivision -> CMRepresentabilityStatement D C ...
```

Here `D.IsDivision` means that every nonzero element of the actual ring `A`
is a unit. It is not inferred from central simplicity. The consequent is the
unchanged imported target: at every original sufficiently small transporter
level, an actual componentwise admissible scheme over `Spec F`, smooth over
`F` and admitting a compatible closed immersion into finite projective space,
naturally represents the constructed normalized CM class presheaf through
lifted actual Hom sets. The representing object must itself lie in the full
test category. No representing object, natural isomorphism or proof of that
consequent is an input to this proposition.

The target preserves the actual Hodge-positive auxiliary left involution and
form used in `HarrisPolarizedWeilClasses`, the opposite convention for the
original right multiplication group, and the conjugated reflex scalar map
used in the Harris–Taylor normalization. It changes none of the underlying
moduli definitions or their same-representative determinant and dimension
conditions.

The proposed source route is the characteristic-zero, regular-module
specialization of Kottwitz's PEL construction. Kottwitz, *Points on some
Shimura varieties over finite fields*, JAMS 5 (1992), Section 5, printed
pp.390–392 (one-based PDF pp.18–20), describes the determinant-condition
moduli problem, sufficiently small quasi-projective representability,
smoothness, and projectivity when `End_B(V)` is a division algebra.
The positive auxiliary algebra has the same underlying ring `A`; for
`V = A` with its left regular action its commuting endomorphism algebra is
the opposite algebra. `DivisionCondition` proves division is preserved by
passage to the opposite and is equivalent to simplicity of the regular
module. Its dimension bound supplies the elementary algebraic obstruction
in the source's properness argument. Registered source:
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.89–91 (PDF pp.97–99), motivates the exact normalized
CM moduli conclusion. Its running assumptions in I.7, printed pp.51–55
(PDF pp.59–63), include division and additional finite-place conditions.
The present statement is a derived characteristic-zero target under division
and the constructed signature charts. It does not claim to encode all of I.7,
an integral model at a specified prime, or the local hypotheses needed for
Harris–Taylor's later reduction and uniformization results. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Applying Kottwitz is still a proof obligation. In particular a proof must
construct the applicable PEL moduli scheme and integral auxiliary choices,
pass to characteristic zero and the specified normalized CM base, identify
its determinant condition, polarization and rational-isogeny classes and
adelic level orbits with this presheaf, and prove naturality of that
identification on the actual test category. It must also establish all the
componentwise admissibility fields for the representing scheme: local
Noetherianity, quasi-separatedness, invertible torsion orders, finite etale
roots of unity, Lie naturality, polarized-pair additivity and existence of
the constrained dual data. The existing signature, Hodge and trace
constructions do not by themselves supply these geometric steps. No
comparison or representability theorem is assumed as unconstrained data.

This proposition states that those steps give the exact imported conclusion
under division; it proves none of them. In particular it does not discharge
the named global prerequisites, extend the current restricted test category
to all locally Noetherian `F`-schemes, or assert finite etale covers, Galois
groups, canonical-model comparisons, uniformization or coefficient descent.
The original exact target and the conditional Yoneda scheme-tower pair remain
unchanged. The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
