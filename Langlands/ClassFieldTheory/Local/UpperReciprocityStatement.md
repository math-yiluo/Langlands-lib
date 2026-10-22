# Higher unit images and upper ramification

Worker 10 authors this proposition family. It states the finite abelian
upper-numbering consequences of local reciprocity. It does not prove
reciprocity, Hasse-Arf or a conductor comparison.

## Actual objects and scope

The base field ranges over every prime and every `PadicField.{u} p`.
The local structure `T` is any of its `TopologicalData` realizations;
`PadicField.canonicalTopologicalData` supplies one for every such field.
The extension `L` is any actual finite abelian intermediate extension
in `AlgebraicClosure F.Carrier`, and `S` is any topological realization
of the existing `L.asPadicField`. The universe of the base is unrestricted;
this presentation uses intermediate fields of its chosen closure.

All extension-field algebra and scalar-tower instances are explicitly
the existing instances on `L.field`, exposed through `inferInstanceAs`
on the definitional `asPadicField` wrapper. No new embedding is selected.

The source subgroups are `T.unitFiltration n`, obtained from the actual
maximal-ideal-power quotient kernels. At zero the filtration is the
valuation-unit subgroup; positive levels are principal units. The target
subgroup is `Ramification.Padic.upperRamificationGroup S F.Carrier v`.
Worker 60 constructs it by applying the genuine inverse Herbrand
function to the existing real-indexed lower ramification groups.
It is neither a renamed unit-image subgroup nor a supplied filtration
certificate.

For four of the five components, `r` is a supplied continuous homomorphism
into the actual absolute-Galois abelianization and must satisfy
`GeometricProfiniteReciprocityRelation F T r`. That predicate requires the
finite norm kernels, surjectivity and restriction compatibility, density,
and geometric residue normalization. No unit-image or ramification law
occurs in it. The existence and uniqueness of `r` are separate unconditional
targets in `ProfiniteReciprocityStatement`. The norm-level component here
does not even take such a map as an input.

## Exact statements

`FiniteReciprocityHigherUnitImages` states that, for every natural `n`,
the image of `T.unitFiltration n` under the existing finite restriction
`finiteFamilyOfHom r L` is the actual upper group at `n`.
In particular, at zero it is inertia. Positive indices are upper
indices throughout, not lower indices.

`FiniteReciprocityRealUnitImages` extends that equality to every real
`v >= 0`, using the unit level `Nat.ceil v`. This is the left-continuous
convention: between consecutive integers `n` and `n+1`, and including
the upper endpoint, the upper subgroup is the one at `n+1`.
In a finite abelian extension Hasse-Arf makes every upper break integral.
The assertion is derived from that theorem and the integer-level
reciprocity assertion. It does not assert integer breaks for nonabelian
extensions or use a newly defined real filtration.

`FiniteAbelianNormUpperLevels` says, unconditionally for every finite
abelian extension, that a unit level is contained in the actual norm
subgroup if and only if the corresponding integer upper group is trivial.
At zero this allows precisely the unramified case. The norm subgroup is
the image of the determinant field norm on units, imported from `Norms`.
This is an existence-free formulation of the filtration criterion in
Serre XV.2; an eventual proof can use the separately stated reciprocity
existence theorem and its exact norm kernels.

`FiniteCharacterUpperConductorLevels` says that a finite Galois character
is trivial on the upper group at real `v >= 0` if and only if the existing
multiplicative conductor of its pullback is at most `Nat.ceil v`.
The imported conductor is the least principal-unit level of triviality.
The character need not be faithful. At zero this gives conductor zero
exactly for unramified characters.

`FiniteCharacterLastUpperBreak` states that this conductor is `n+1`
exactly when the character is nontrivial on the upper group at `n`
and trivial on every real upper group at `v > n`. Using every later real
level makes the right-limit boundary explicit. Tame ramification has
`n=0`; unramified characters have conductor zero and satisfy neither
side for any natural `n`. For a nonfaithful character this is the last
break detected by that character, not necessarily the last break of the
whole extension.

`FiniteUpperReciprocityTheorems` conjoins these five assertions. It leaves
the absolute/abelianized infinite-filtration formulation for a separate
pair once that construction is published. The rational Artin-sum
comparison is in `FiniteConductorStatement`; this pair uses the existing
multiplicative conductor and does not duplicate the Artin construction.

## Original sources and derivations

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, GTM 67, Springer, 1979:

| Declaration | Source and derivation |
| --- | --- |
| `FiniteReciprocityHigherUnitImages` | XV.2, Theorem 1, Corollary 3, and Theorem 2, printed pages 227-228 / PDF 232-233. The theorem treats general abelian extensions; its finite case gives equality of subgroups. |
| `FiniteReciprocityRealUnitImages` | Derived from that integer-level result, the real upper numbering and left-continuity convention in IV.3, printed pages 73-75 / PDF 80-82, and Hasse-Arf on printed page 76 / PDF 83. |
| `FiniteAbelianNormUpperLevels` | XV.2, Theorem 1, Corollaries 1-2, printed page 228 / PDF 233, together with Theorem 2 for the extension with an unramified part and the exact finite norm kernel. |
| `FiniteCharacterUpperConductorLevels` | Derived from the real unit-image equality and the imported least-level definition of the multiplicative conductor. The source compares the least norm level with the conductor in XV.2, Corollary 2, printed page 228 / PDF 233. |
| `FiniteCharacterLastUpperBreak` | Derived boundary formulation of the same result. VI.2, Proposition 5 and its corollary, printed page 102 / PDF 109, identifies a degree-one Artin conductor with one plus the detected upper break and treats passage to the character's cyclic quotient. |

Worker 10 read these complete original pages, including VI.2 printed
100-102 / PDF 107-109 for the fixed-space formula and quotient-character
compatibility. Registered source `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre's reciprocity is arithmetic. The project inverts its values, so
uniformizers correspond to geometric Frobenius of degree `+1`.
Inversion preserves every ramification subgroup and every character
kernel, and therefore preserves these image and conductor statements.
No Frobenius lift or inverse into a nonabelian Weil group is chosen.

## Dependencies and development status

All imports are published in the Library:
`Langlands.ClassFieldTheory.Local.Units`, `Langlands.HarmonicAnalysis.Conductor`,
`Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement` and
`Langlands.LocalFactor.Ramification.Herbrand.Finite`.
The Herbrand construction is imported unchanged from Worker 60's
published work; this contribution contains only the present statement pair.

The current environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation and exact inspection of
`FiniteUpperReciprocityTheorems` succeeded with zero errors or warnings
and confirmed that it returns `Prop`. Independent semantic review and
publication are required in addition to compilation. No theorem in this
family is claimed as proved.
