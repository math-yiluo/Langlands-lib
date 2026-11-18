# The absolute residue action of a nonarchimedean local field

Original construction (characteristic zero, `AlgebraicClosure K`): Worker 9.
Generalization to every nonarchimedean local field over a separably closed
algebraic extension: Worker 122 (Task 7404, deliverable 1b of Task 7341).

For every nonarchimedean local field \(K\), in any characteristic, and every
algebraic extension \(\Omega/K\) that is separably closed, this file constructs
an actual homomorphism
\[
 \rho_{K,\Omega}:\operatorname{Gal}(\Omega/K)
 \longrightarrow
 \operatorname{Gal}(\operatorname{AlgebraicClosure}k/k),
 \qquad k=\mathcal O_K/\mathfrak m_K,
\]
and the inertia subgroup of \(\operatorname{Gal}(\Omega/K)\). The field \(k\) is
the residue field `𝓀[K]` of the supplied `ValuativeRel K`, with its usual
algebraic structure. Both groups carry Mathlib's Krull topology. No residue
homomorphism, closure property, lifting theorem, continuity certificate or
surjectivity certificate is accepted as input data.

The general declarations live in the namespace `Langlands.LocalGalois.SepClosed`.
The published characteristic-zero declarations of `Langlands.LocalGalois` and the
p-adic declarations of `Langlands.PadicField` keep their names and types and are
now these general declarations at \(\Omega=\) `AlgebraicClosure K` (see "In
place" below).

## Hypotheses

All general declarations take explicit arguments `K` and `Ω` with
```
(K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
(Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
```
and, from `residue_isAlgClosure` on, also `[IsSepClosed Ω]`. There is no
hypothesis on the characteristic of \(K\) and no `PerfectField K`.

These hypotheses hold for every separable closure. If `[IsSepClosure K Ω]`,
Mathlib derives `Algebra.IsAlgebraic K Ω` by instances, and
`IsSepClosure.sep_closed K (K := Ω) : IsSepClosed Ω` is a theorem that is not an
instance, so a user writes
`haveI := IsSepClosure.sep_closed K (K := Ω)` before applying the general
declarations. For Mathlib's `SeparableClosure K`, both instances are found
automatically. Each of the following was checked to compile, in a private draft
module importing this file, `AbsoluteProof` and `SeparableInertiaDefinitions`:
the declarations at an arbitrary `Ω` with `[IsSepClosure K Ω]` (through that
`haveI`), at `SeparableClosure K`, and at
`SeparableClosure (LaurentSeries k)` for a finite field `k`, with the local field
structure of `Langlands/LocalField/LaurentSeries.lean`.

The hypotheses are weaker than `[IsSepClosure K Ω]` on purpose: they also hold
for `Ω = AlgebraicClosure K` in every characteristic, which is not a separable
closure when \(K\) has characteristic \(p\). The published declarations at
`AlgebraicClosure K` carry no `CharZero K` argument in their types. A general
definition requiring `IsSepClosure K Ω` could therefore not specialize to them by
unfolding without adding a characteristic hypothesis to published types.

## Norm and valuation choices

`localRankOne` chooses an ordered embedding of the supplied rank-one value group
into the nonnegative reals. `localNormedField` uses Mathlib's valued-field norm
construction with the original additive uniformity. Its construction lemmas
certify completeness, the ultrametric inequality, the unchanged topology, and
equality of its unit ball with the original integer ring. This norm need not have
a specified numerical normalization. Its order relation is the supplied
valuation relation. These declarations were already stated for every
nonarchimedean local field and are unchanged.

`SepClosed.closureValuation K Ω` is the spectral extension of that norm to
\(\Omega\) (`spectralValuation K Ω` of `SpectralDefinitions`). The instance
`SepClosed.closureValuation_extends` proves Mathlib's `Valuation.HasExtension` from
the original `ValuativeRel.valuation K`, so it extends the supplied valuation up
to the natural equivalence of value groups. `SepClosed.closureIntegers K Ω` is
the abbreviation `extensionIntegers K Ω`, the valuation subring of this spectral
valuation, and `SepClosed.integerMap` embeds the original integer ring `𝒪[K]`
into it. The construction never assumes that \(\Omega\) is complete or locally
compact.

## The residue field of the integers of Ω

Write \(A\) for the norm's unit ball (`baseIntegers K`), \(B\) for
`SepClosed.closureIntegers K Ω`, and \(k_A,k_B\) for their residue fields.
Equality of \(A\) with the supplied integer ring induces `localResidueEquiv`, a
ring equivalence \(k_A\simeq k\). `SepClosed.residueAlgebra` is the
\(k\)-algebra structure on \(k_B\) obtained from the residue algebra
\(k_A\to k_B\) by transport along this equivalence.

The identification of \(k_B\) with an algebraic closure of \(k\) uses two
general lemmas of this file, in the namespace `Langlands.LocalGalois`:

- `lifted_separable`: let \(A_0\) be a local ring, \(\varphi:A_0\to k_0\) a local
  ring homomorphism to a field, and \(g\in A_0[X]\) monic with \(\varphi(g)\)
  separable. Then \(g\) is separable. The resultant of \(g\) and \(g'\), formed
  with the degrees of \(g\) and \(g'\), maps under \(\varphi\) to the resultant
  of \(\varphi(g)\) and \(\varphi(g)'\) (the degree of \(g'\) may exceed that of
  \(\varphi(g)'\); because \(\varphi(g)\) is monic, padding the degree multiplies
  the resultant by a power of its leading coefficient, which is \(1\)). For a
  monic polynomial, separability is coprimality with the derivative, which is
  invertibility of this resultant. A local homomorphism reflects units.
- `residue_isSepClosed`: if \(L\) is separably closed, the residue field of every
  valuation subring \(A_0\) of \(L\) is separably closed. Lift an irreducible
  separable polynomial over the residue field to a monic polynomial over \(A_0\)
  of the same degree; it is separable by `lifted_separable`, so it has a root in
  \(L\). The root is integral over \(A_0\), hence lies in \(A_0\) because
  valuation rings are integrally closed, and its residue class is a root of the
  given polynomial.

With `[IsSepClosed Ω]`, `SepClosed.residue_isAlgClosure` proves that \(k_B\) is an
algebraic closure of \(k_A\). By `residue_isSepClosed`, \(k_B\) is separably
closed. It is algebraic over \(k_A\) by the published spectral integrality. The
field \(k_A\) is finite, hence perfect, so its algebraic extension \(k_B\) is
perfect, and a perfect separably closed field is algebraically closed (Mathlib's
`IsSepClosed.isAlgClosed_of_perfectField`).

`SepClosed.residueClosureEquiv` then uses Mathlib's `IsAlgClosure.equivOfEquiv` to
choose a ring equivalence
\[
 e:k_B\simeq\operatorname{AlgebraicClosure}k
\]
compatible with \(k_A\simeq k\) (`SepClosed.residueClosureEquiv_base`).
`SepClosed.residueClosureAlgEquiv` is the same \(e\) as a \(k\)-algebra
equivalence for `SepClosed.residueAlgebra`. No canonical choice of \(e\)
independent of closure presentations is claimed.

## Automorphisms and inertia

`semilinearAutCongr` conjugates actual field automorphisms through compatible
equivalences of base fields and extension fields.
`SepClosed.residueTransport K Ω` applies it to \(k_A\simeq k\) and \(e\).
`SepClosed.absoluteResidueHom K Ω` composes this conjugation with the published
spectral residue homomorphism `residueHom K Ω`:
\[
 \rho_{K,\Omega}(\sigma)(e(\bar x))=e(\overline{\sigma x})\quad(x\in B).
\]
`SepClosed.absoluteInertia K Ω` is the spectral inertia subgroup `inertia K Ω`,
the kernel of `residueHom K Ω`, with the instance
`SepClosed.absoluteInertia_normal`. It needs no `IsSepClosed Ω`. Its equality with
the kernel of \(\rho_{K,\Omega}\) is `SepClosed.absoluteResidueHom_ker` in
`AbsoluteProof`, together with the continuity of \(\rho_{K,\Omega}\) and, under
`[IsGalois K Ω]`, its surjectivity.

For every intermediate field \(E\subseteq\operatorname{AlgebraicClosure}K\),
`integerInclusion` uses equality of spectral norms in a tower to embed its
integer ring into \(B\). A proved local-hom instance permits reduction to the
residue-field embedding `residueInclusion`. These two declarations are unchanged.

## Where characteristic zero was used, and its replacement

The published section assumed `[CharZero K]` and worked with
`AlgebraicClosure K`. Characteristic zero entered in two ways.

1. *Algebraic closedness of \(k_B\).* The published `localResidueClosureEquiv`
   took the algebraic closure property of \(k_B\) from the published
   `residueExtension_isAlgClosure`, which requires \(\Omega\) algebraically
   closed. `AlgebraicClosure K` is algebraically closed, and it is a separable
   closure of \(K\) exactly when \(K\) is perfect, which characteristic zero
   guarantees (Mathlib's `IsSepClosure.of_isAlgClosure_of_perfectField`).
   Replacement: `[IsSepClosed Ω]` together with `residue_isSepClosed` and the
   perfectness of the finite field \(k_A\), as in `SepClosed.residue_isAlgClosure`
   above.
2. *Galois property, for surjectivity.* The published
   `absoluteResidueHom_surjective` of `AbsoluteProof` applies the spectral
   surjectivity theorem, which needs `IsGalois K (AlgebraicClosure K)`. This
   instance exists because a field of characteristic zero is perfect.
   Replacement: the explicit hypothesis `[IsGalois K Ω]` of
   `SepClosed.absoluteResidueHom_surjective`. It holds for every separable closure
   (Mathlib's instance `IsSepClosure.isGalois`), so in particular for
   `SeparableClosure K` in every characteristic.

The other published uses of `CharZero K` in `AbsoluteProof` (openness,
compactness of inertia, the quotient equivalence) are part of the published
statement `LocalResidueProperties` and are not generalized here; a later task of
Task 7341 states their general analogue.

## In place: the published declarations are the general ones

Every published declaration of this file keeps its full name and its type. The
Lean types of all 141 declarations of `AbsoluteDefinitions`, `AbsoluteProof`,
`SeparableInertiaDefinitions` and `Langlands/Weil/Local/Assembly.lean` were
printed with `set_option pp.all true` before and after the change and are
identical. The published characteristic-zero definitions are now defined as the
general ones at \(\Omega=\) `AlgebraicClosure K`, for example
`absoluteResidueHom K := SepClosed.absoluteResidueHom K (AlgebraicClosure K)`.
The single exception is the abbreviation `closureIntegers K`, which keeps its
literal body `extensionIntegers K (AlgebraicClosure K)`: rewriting it as
`SepClosed.closureIntegers K (AlgebraicClosure K)` changes the fully elaborated
types of three declarations of `AbsoluteProof` (through the names of file-local
instances) although they stay definitionally equal. It is equal to the general
one by `rfl`.

The `Langlands.PadicField` declarations are unchanged. They install the
instances of the supplied `T : F.TopologicalData` and call the declarations
above, so they are the general ones at `F.Carrier` and
`AlgebraicClosure F.Carrier`.

In a private draft module, each equation in the following table between a
published declaration and the general declaration was checked by `rfl` (for the
p-adic column, after installing `T.topology`, `T.valuativeRel` and
`T.localField`).

| General (`LocalGalois.SepClosed`) | Characteristic 0, \(\Omega=\) `AlgebraicClosure K` (`LocalGalois`) | p-adic (`PadicField`, data `T`) | \(\Omega=\) `SeparableClosure F` (`LocalGalois.Separable`) |
| --- | --- | --- | --- |
| `closureIntegers K Ω` | `closureIntegers K` | `closureIntegers F T` | `sepClosureIntegers F` |
| `closureValuation K Ω` | `localClosureValuation K` | — | `sepClosureValuation F` |
| `closureValuation_extends K Ω` | `localClosureValuation_extends K` | — | `sepClosureValuation_extends F` |
| `integerMap K Ω` | `localIntegerMap K` | — | `integerToSepClosure F` (equal by `rfl`, own body) |
| `residueAlgebra K Ω` | `standardResidueAlgebra K` | — | — |
| `residueClosureEquiv K Ω` | `localResidueClosureEquiv K` | — | — |
| `residueClosureEquiv_base K Ω` | `localResidueClosureEquiv_base K` | — | — |
| `residueClosureAlgEquiv K Ω` | `localResidueClosureAlgEquiv K` | — | — |
| `residueTransport K Ω` | `localResidueTransport K` | — | — |
| `absoluteResidueHom K Ω` | `absoluteResidueHom K` | `absoluteResidueHom F T` | `(residueTransport K Ω).toMonoidHom.comp (separableResidueHom F)` |
| `absoluteInertia K Ω` | `absoluteInertia K` | `absoluteInertia F T` | `separableInertia F` |
| `absoluteInertia_normal K Ω` | `absoluteInertia_normal K` | `absoluteInertia_normal F T` | `separableInertia_normal F` |

The continuity, kernel and surjectivity lemmas of `AbsoluteProof` are listed in
`AbsoluteProof.md`. The general Weil group built on `absoluteResidueHom K Ω` is
in `Langlands/Weil/Local/Assembly.lean`.

## Sources, dependencies and scope

The mathematical source is Serre, *Local Fields*, English 1979:
Chapter II, §2, Proposition 3 and Corollaries 2–3, pp. 28–29 (PDF 36–37);
Chapter I, §7, Propositions 20–22 and the inertia definition, pp. 20–23
(PDF 28–31); and Chapter III, §5, Theorems 2–3 and Corollaries 1–3, pp. 54–55
(PDF 61–62). Corollary 1 of Chapter III, §5 (p. 55) states that the maximal
unramified extension has residue field the separable closure \(k_s\) of \(k\);
for finite \(k\) this is an algebraic closure, which is the mathematical content of
`SepClosed.residue_isAlgClosure`. The pages were read in the retained file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Registered source: `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The proofs of `lifted_separable` and `residue_isSepClosed` are derived: they are
the standard lifting argument described above, written for this file, and not
taken from Serre's text, which works with finite unramified extensions.

This is a derived formal construction, making all closure and valuation choices
explicit. Its project dependencies are:

- `Langlands.Galois.Local.SpectralProof`, which supplies the spectral valuation,
  integrality of the constructed unit ball, the residue homomorphism and inertia
  for any algebraic extension of a complete ultrametric field, and
  `residueExtension_isAlgClosure`.
- `Langlands.LocalField.Definitions`, which supplies `PadicField` and the explicit
  `TopologicalData` interface.
- Mathlib's `Mathlib.FieldTheory.IsSepClosed` and
  `Mathlib.RingTheory.Polynomial.Resultant.Basic` (resultants:
  `isUnit_resultant_iff_isCoprime`, `resultant_map_map`,
  `resultant_add_right_deg`).

The generalization was compiled in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) over Library commit `fcb85a7e`.

This file does not prove the residue exact sequence. `AbsoluteStatement`
specifies the published characteristic-zero conclusions, and a later task of
Task 7341 states their general analogue. The identification of
`Field.absoluteGaloisGroup k` with the profinite integers by Frobenius, and the
local Weil group, are in `Langlands/Weil/Local/Assembly.lean`.
