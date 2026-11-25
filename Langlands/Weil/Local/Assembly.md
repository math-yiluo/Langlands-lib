# Local Weil assembly over a separable closure

This is a definition and construction module.

Let `K` have `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`. The namespace
`Langlands.Weil.Local.SepClosed` constructs the Weil group using an extension
`Ω` with `[Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]`.
There is no characteristic hypothesis, and no topology on `Ω` is supplied.
The automorphism group `Gal(Ω/K)` carries Mathlib's Krull topology. The hypotheses
are deliberately broader than being a separable closure so the same definitions
also specialize to the old algebraic-closure interface in every characteristic
where that interface was already defined.

For `[IsSepClosure K Ω]`, algebraicity and `IsGalois K Ω`
are inferred by Mathlib. Its separable-closedness certificate is installed locally
with `letI := IsSepClosure.sep_closed K (K := Ω)`: this theorem is not itself a
global instance. The canonical `SeparableClosure K` already has the needed
instances. Thus all the constructions below apply to arbitrary separable closures,
including those of positive-characteristic local fields.

The residue field `localResidueField K` is exactly `𝓀[K]`, finite by the local field
instance. `localResidueMap K Ω` bundles
`LocalGalois.SepClosed.absoluteResidueHom K Ω` with its proved continuity. Composing
it with the existing finite-field Frobenius equivalence gives
`localResidueDegree K Ω : Gal(Ω/K) →ₜ* ProfiniteIntegers`. The finite-field
comparison sends arithmetic Frobenius to minus one, giving the geometric
normalization. `localWeilGroup K Ω` is the existing `Weil.Pullback` of this degree
along the integer map into the profinite integers, with the subgroup topology
from `Gal(Ω/K) × Multiplicative ℤ`.

`localProjection`, `localDegree`, and `localDegreeInt` expose its two components.
`localInertia` is the kernel of the integer degree, with normality inherited from
the kernel construction. The injective finite-field comparison identifies the
kernel of the profinite residue degree with absolute Galois inertia;
`localGaloisInertiaEquiv` packages this equality as a topological group equivalence.
`localInertiaInclusion` sends absolute inertia to pairs with degree zero. The
continuity proofs use the ordinary subtype topologies.

With the additional `[IsGalois K Ω]`, surjectivity of the constructed residue map
and of the finite-field equivalence proves `localResidueDegree_surjective`; the
existing pullback theorem then proves `localDegree_surjective`. These are
construction obligations, needed to define
`localGeometricFrobenius` as a preimage of degree plus one. Its degree equation is
the corresponding choice certificate. The residue map, Weil group and inertia
constructions do not require `IsGalois`, nor do the characters:
`localUnramifiedCharacter K Ω z` sends degree `n` to `z^n`;
`localNormCharacter K Ω` is the same character with degree-one value
`(Nat.card 𝓀[K])⁻¹`, using the proved positivity of this finite field's cardinality.
Its defining formula as a complex number is `q^(-n)` with `q = Nat.card 𝓀[K]`.
Complex units carry their usual topology.

## Characteristic assumptions and in-place specialization

The old declarations in `Langlands.Weil.Local` keep their full names, types and
meanings. They specialize these definitions at `K = F.Carrier`, with the instances
of `F.canonicalTopologicalData`, and `Ω = AlgebraicClosure F.Carrier`. The p-adic
field's characteristic-zero certificate is derived locally from its `Padic p`
algebra where the Frobenius construction needs Galois surjectivity. This supplies
perfection, so Mathlib's
`IsSepClosure.of_isAlgClosure_of_perfectField` makes its algebraic closure a
separable closure. Characteristic zero is used only in these p-adic
specializations of surjectivity and geometric Frobenius. For an arbitrary
characteristic-zero local field, the same general constructions at
`Ω = AlgebraicClosure K` use this Mathlib instance.

The former arithmetic inputs used characteristic zero in two places. First,
algebraic-closedness of the residue field of an algebraic closure is replaced by
`LocalGalois.SepClosed.residue_isAlgClosure`: the residue field of the integer ring
of a separably closed extension is separably closed, and its algebraicity over the
finite, hence perfect, field `𝓀[K]` makes it algebraically closed. This supplies the
residue-field identification and continuous residue map. Second, Galoisness of
the chosen closure in the residue-surjectivity proof is supplied directly by
`IsSepClosure.isGalois`. The spectral valuation and its invariance, normality and
kernel constructions, finite-field comparison, pullback topology, and the
degree characters require no characteristic-zero argument.

All specializations agree by unfolding; no comparison theorem is introduced.
In particular the old norm character agrees by unfolding
`canonicalResidueNormCharacter`, `residueNormCharacter`, and `normCharacter`,
since both use the same actual residue cardinality. The old residue field,
pullback, projection, degree and inertia definitions retain their defining
expressions; their residue map is now obtained from the general constructor.

| General declaration in `Langlands.Weil.Local.SepClosed` | Characteristic-zero specialization | P-adic specialization in `Langlands.Weil.Local` |
| --- | --- | --- |
| `localResidueField K` | `𝓀[K]` | `localResidueField F` |
| `localResidueMap K Ω` | `Ω = AlgebraicClosure K` | `localResidueMap F` |
| `localResidueDegree K Ω` | same closure | `localResidueDegree F` |
| `localWeilGroup K Ω` | same closure | `localWeilGroup F` |
| `localProjection K Ω` | same closure | `localProjection F` |
| `localDegree K Ω`, `localDegreeInt K Ω` | same closure | `localDegree F`, `localDegreeInt F` |
| `localInertia K Ω` | same closure | `localInertia F` |
| `localInertia_normal K Ω` | same closure | `localInertia_normal F` |
| `localResidueDegree_ker K Ω` | same closure | `localResidueDegree_ker F` |
| `localGaloisInertiaEquiv K Ω` | same closure | `localGaloisInertiaEquiv F` |
| `localInertiaInclusion K Ω` | same closure | `localInertiaInclusion F` |
| `localResidueDegree_surjective K Ω` | same closure | `localResidueDegree_surjective F` |
| `localDegree_surjective K Ω` | same closure | `localDegree_surjective F` |
| `localGeometricFrobenius K Ω` | same closure | `localGeometricFrobenius F` |
| `localGeometricFrobenius_degree K Ω` | same closure | `localGeometricFrobenius_degree F` |
| `localUnramifiedCharacter K Ω z` | same closure | `localUnramifiedCharacter F z` |
| `localNormCharacter K Ω` | same closure | `localNormCharacter F` |

## Original sources and provenance

Henniart, *Représentations du groupe de Weil d'un corps local* (1980), §§2.1–2.2
(opening paragraph), printed p. 158 (PDF p. 5), defines the Weil group as the
integer-Frobenius preimage, its inertia topology, and its integer quotient. This
is source `henniart-1980-weil-representations`, original PDF SHA-256
`451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
Tate, *Number theoretic background* (1979), (1.4.1), printed p. 6 (PDF p. 15),
explicitly gives the nonarchimedean local field description without restricting
the characteristic. It uses inverse arithmetic Frobenius for uniformizers.
Section (1.4.6), printed p. 7 (PDF p. 16), gives the norm homomorphism, and (4.1.3),
printed p. 20 (PDF p. 29), writes it as `q^(-v(w))`. This is source
`tate-1979-number-theoretic-background`, Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These original pages were read directly for this generalization.

This is derived assembly using the Library's spectral residue map, finite-field
Frobenius comparison, generic pullback, and degree characters. These, and the
general residue constructions with their intrinsic proofs, are documented in
their respective modules.
The topology, density, compactness, character evaluation, and residue Frobenius
properties beyond these construction obligations belong to separate statement
and proof modules. Existing p-adic statement modules keep their text.
The unchanged `Langlands.Weil.Local.AssemblyProof` compiles against the
generalization. Private compilation probes also check the arbitrary
`IsSepClosure K Ω` interface, the canonical separable closure of `LaurentSeries k`
for finite fields `k`, definitional agreement of the p-adic constructors, and
unchanged fully elaborated types of all 19 published Assembly declarations.
The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
