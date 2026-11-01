# Detection by geometric torsion of order a power of two

`FieldTwoPowerTorsionDetectionStatement` asserts the following proposition at
arbitrary universe `u`. Let `Ω` be an algebraically closed field of characteristic
zero, let `A` and `B` be actual abelian schemes over `Spec Ω`, and let `f : A ⟶ B`
be an actual homomorphism. If the existing `GroupScheme.Tate.levelMap` induced by
`AbelianScheme.groupHom f` is zero at every order `2 ^ n`, then `f = 0`.

The test scheme is exactly `Over.mk (𝟙 (Spec Ω))`. Thus the level groups are the
existing additive groups of actual `Ω`-valued sections killed by multiplication
by `2 ^ n`. The hypothesis says that every such section is sent to the identity
section of `B`. It includes `n = 0`, whose order-one level is trivial. No chosen
representation, replacement point group, rational Tate module, or assumed
faithfulness enters this proposition.

This is a geometric prerequisite for field faithfulness of the actual full
rational Tate Hom map. The statement itself supplies no proof. Its intended use
is after lifting geometric 2-power torsion points to the actual integral
2-adic Tate module and comparing that module with the actual full Tate module.
Those algebraic reductions do not prove this geometric assertion.

## Provenance

This is a derived, weaker target suggested by Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, preliminary draft, Chapter XII §1, Lemma (12.8), printed
p.182 / one-based PDF p.186, and Theorem (12.10)(i), printed pp.183–184 / PDF
pp.187–188. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
No matching project erratum note was present when preparing this statement.

Theorem (12.10)(i) gives injectivity of the geometric prime-adic Hom map after
tensoring Hom with `ℤ_ℓ`, for a prime different from the characteristic. Killing
all 2-power torsion makes the induced 2-adic map zero. Together with the
source's torsion-freeness of Hom, its injectivity implies the assertion above
by taking `ℓ = 2`. A proof of the present target may instead use geometric
torsion density. This file does not assert either argument has been formalized,
and the proposition is not a verbatim statement of (12.10).

The task's restrictions on neighboring Picard, polarization, multiplication
kernel, and moduli work remain in force. This statement concerns only detection
of an actual morphism by its geometric torsion points.
