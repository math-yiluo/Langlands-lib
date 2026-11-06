# Actual local genericity of cuspidal presentations

Author: Worker 1778.

`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement.{uF, uQ}`
is a proposition definition isolating the genericity input used at the start
of Henniart's Appendix A.2. It is an independently usable target for a later
proof. This module supplies no proof of the existence of a Whittaker functional.

## Exact quantifiers and original action

The statement quantifies over every `F : Type uF` with `Field F`,
`NumberField F`, and `CompactSpace (Langlands.Global.AdeleQuotient F)`, every
`r : ℕ`, and every
`T : Langlands.Automorphic.CuspidalOperatorRealization F r` satisfying
`Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`.
The last predicate means that some continuous idele-class character `χ`
has unit complex norm everywhere and satisfies `T.HasCentralCharacter χ`.
The compactness instance is for the additive adelic quotient in the existing
cuspidal interface.

It then quantifies over every
`P : Langlands.Automorphic.CuspidalSpectralPresentation.{uF, uQ} T`, every
finite place `v`, and every proof
`hI : (P.localComponent v).IsIrreducible` and
`hA : (P.localComponent v).IsAdmissible`. Write
`K = Langlands.Global.CompletionPadic.padicField v` and

```text
ρ = ((P.localComponent v).padicObject hI hA).obj.representation.
```

The statement installs `K.canonicalTopologicalData.topology` and
`K.canonicalGeneralLinearTopology (r + 1)`. For every
`ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier`, the
conclusion is exactly `Langlands.Whittaker.IsGeneric ψ r ρ`.
The character type already requires continuity, nontriviality, and values in
the unit circle. There is no further choice of topology or character class.

The [`padicObject` interface](PadicLocalCategory.md) retains the original
embedded form-space carrier and the original action of the actual matrix group
`GL_(r+1)(K.Carrier)`, packaged with canonical smoothness, irreducibility, and
admissibility. It does not choose an equivalent Whittaker model. The original
local carrier lies in `uF`; the carriers of `P.localFactor` may lie in the
independent universe `uQ`. No equality of these universes is imposed.
Quantification over supplied presentations does not assert their existence.

## Meaning of genericity

The shared [`Whittaker.IsGeneric`](../Representation/Whittaker/GeneralLinear.md)
is the conjunction of irreducibility, admissibility for the selected group
topology, and the existence of an actual nonzero complex linear functional
`ℓ` on the carrier of `ρ` satisfying

```text
ℓ(ρ(u) x) = ψ.complex(∑ i : Fin r, u[i, i+1]) * ℓ(x)
```

for every standard upper-unipotent matrix `u` and every vector `x`. Here the
matrix indices are precisely `i.castSucc` and `i.succ` in `Fin (r + 1)`.
The sign is positive. The coefficient convention is
`W_x(g) = ℓ(ρ(g) x)`, so the group acts by right translation
`W_x(g) ↦ W_x(g s)`. Neither a functional nor the desired genericity is an
input. No multiplicity-one result or topology on the vector-space carrier is
asserted. Rank one is included: `r = 0`, the upper-unipotent group is trivial,
and the first-superdiagonal sum is empty.

## Why every nontrivial additive character is faithful to the source

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Inventiones Mathematicae 139 (2000), Théorème 2.4,
printed p.445, works with cuspidal representations with unitary central
character. Appendix A.2, printed p.453, uses that the local component is
unitary and generic. It does not fix a new Whittaker functional as a
hypothesis or prove its existence. Source: `henniart-2000-simple-proof`,
SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The character convention can be checked in Jacquet, Piatetski-Shapiro and
Shalika, *Rankin-Selberg Convolutions* (1983), printed p.377: the standard
upper-unipotent character is the product of `ψ` on the first-superdiagonal
entries, equivalently `ψ` of their sum. Their §2.1, printed p.385, explains
the change of character: if `ℓ` is equivariant for `θ`, then
`x ↦ ℓ(ρ(d) x)` is equivariant for `u ↦ θ(d u d⁻¹)` when `d` is diagonal.
Source: `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field* (1976), §5.3, printed p.44, identify the additive
characters relative to a fixed nontrivial `ψ₀` as
`ψ_a(x) = ψ₀(a*x)`. Nontrivial characters correspond to `a ≠ 0`.
Source: `bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The relevant original pages of all three sources were read directly.

For such an `a`, take
`d_a = diag(a^r, a^(r-1), ..., a, 1)`. Conjugation by `d_a` multiplies every
first-superdiagonal entry by `a`, so
`ℓ_a(x) = ℓ(ρ(d_a) x)` has the standard character for `ψ_a`.
It remains nonzero because `ρ(d_a)` is invertible. This changes the functional
on the same original representation. Thus the usual genericity assertion for
one nontrivial character yields the assertion for every such character.
The inverse character is covered by `a = -1`.
Continuous additive characters of a p-adic field with values in the circle
are locally constant, so the shared continuous character type has the usual
nonarchimedean character convention. The Library's
[`PadicAdditiveCharacterSelfDuality`](../HarmonicAnalysis/PadicAdditiveCharacterSelfDuality.md)
implements scalar parameterization for locally constant complex characters;
[`Whittaker.CharacterChange`](../Representation/Whittaker/CharacterChange.md)
implements the stated diagonal conjugation and functional equivalence.
These explain the formulation; this statement module does not prove the
initial existence of a generic functional.

## Source-to-presentation boundary

Henniart speaks about representation classes. This proposition translates the
input to every actual presentation in the Library's interfaces. A nonzero
Whittaker functional transports along an equivariant linear equivalence;
irreducibility and admissibility are also invariant under such equivalence.
This translation does not identify different embedded form subspaces.
The source's arithmetic representation and weak-association hypotheses are
used in the later comparison argument, rather than in the isolated local
genericity input.

The companion local unitarity proposition is separately stated in
[`CuspidalUnitaryLocalUnitarityStatement`](CuspidalUnitaryLocalUnitarityStatement.md).
This module does not depend on that proposition or take its conclusion as a
premise. The Appendix A.3 pole correction in
[`notes/henniart/audit.md`, §3.2](../../notes/henniart/audit.md) is separate and
is not used by either statement.
