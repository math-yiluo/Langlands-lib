# Spectral displacement tests on full represented affinoid domains

This module constructs subgroups of bounded automorphisms by imposing actual
section tests on full represented affinoid domains. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism`.

## Actual algebras and the uniform bound

Let `K` be an ultrametric normed field and let `A` be a
`PresentedAffinoidAlgebra K`. Thus `A` is the existing actual closed quotient of
a finite Tate algebra with arbitrary positive real polyradius. The imported
`BanachSpectrum.SpectralBound b r` means

```
for every x : BanachSpectrum A, x b <= r.
```

It makes sense even when the spectrum is empty. This module reuses the generic
bound and its zero, negation, addition and bounded-map transport lemmas from
`StrictTestDomain.SpectralDisplacement`; it does not redefine that bound.

`spectralDisplacementSubgroup b r hr`, for `hr : 0 <= r`, is the subgroup of
`Aut A` defined by `SpectralBound (g.hom b - b) r`. Multiplication applies the
right operator first. To prove closure under multiplication, the proof writes

```
g(h(b)) - b = g(h(b) - b) + (g(b) - b).
```

The first summand has the same spectral bound because every bounded ring map
pulls target spectrum points back to source points. The nonarchimedean triangle
inequality bounds the sum by the same radius. For inversion, the proof applies
`g.inv` to `-(g.hom b - b)` and uses the actual inverse law to obtain
`g.inv b - b`. The identity condition uses the zero bound. These steps do not
require a common operator-norm bound or a norm-isometry assertion.

The membership lemma exposes this uniform inequality. The subgroup increases
with the radius, and the test on the zero element gives the whole automorphism
group. Completeness of `K` is not needed for these initial declarations.

## Tests on actual domains

Assume also that `K` is complete. For any supplied `U : Domain K A`, the module
`DomainAutomorphism` constructs the monoid homomorphism
`stabilizerSectionAction U` from its setwise locus stabilizer to bounded
automorphisms of the actual quotient algebra `U.algebra`. Its operators come
from full unique factorization; they are not inputs to the test.

`stabilizerSpectralSubgroup U b r hr` is the inverse image of the displacement
subgroup along this constructed action. `domainSpectralSubgroup U b r hr`
then maps it into `Aut A` by the stabilizer inclusion. Its exact membership
criterion is existence of `hg : g ∈ locusStabilizer U` such that

```
for every x : BanachSpectrum U.algebra,
  x ((stabilizerSectionAction U <g,hg>).hom b - b) <= r.
```

Thus membership includes setwise preservation of the actual domain locus.
`domainSpectralSubgroup_le_locusStabilizer` exposes that condition. Increasing
the radius weakens the test, and testing the zero section gives exactly the
locus stabilizer, rather than imposing pointwise fixation.

`DomainSpectralTest K A` consists of one such full represented domain, an actual
element of its section algebra, a real radius, and proof that the radius is
strictly positive. `finiteDomainSpectralSubgroup tests` intersects all the test
subgroups for any finite index type in an independent universe. Its membership
lemma gives every domain and section condition. The empty family gives the
whole group, and concatenation by a sum of finite types gives the intersection
of the two finite test subgroups.

## Conjugation and movement

`DomainAutomorphismTransport.movedDomain U g` changes the structural map to
`U.baseMap.comp g.inv`, represents the image of the original locus under the
inverse-comap point action of `g`, and retains **exactly** the section algebra
and its quotient norm. The transported element can therefore remain `b` itself.

`conjugate_mem_stabilizerSpectralSubgroup_iff` uses the previously proved
full-map equality `stabilizerSectionMap_conjugate`: on the moved domain the
operator for `g * h * g⁻¹` is the same bounded operator on that retained algebra
as the original operator for `h`. Substitution identifies the two spectral
conditions. Together with the proved equivalence of stabilizer membership,
`conjugate_mem_domainSpectralSubgroup_iff` proves the ambient subgroup
membership equivalence.

`DomainSpectralTest.transport g t` moves the domain and retains its actual
section element and positive tolerance. `DomainSpectralTest.subgroup_transport`
identifies the resulting subgroup with the image of the original subgroup
under `MulAut.conj g`. `finiteDomainSpectralSubgroup_transport` proves the same
identity for every finite family, including the empty family. Both proofs use
the bijectivity of conjugation and the single-test membership equivalence; no
equality of domain presentations or spectrum faithfulness is inferred.

## Provenance and scope

This is an internal construction from the existing actual positive-polyradius
quotients, their spectra, the full `Domain` universal property, and the
constructed section actions and base transport. The displacement subgroup,
finite intersection, and conjugation-image proof patterns adapt the published
strict rational constructions in `StrictTestDomain.SpectralDisplacement` and
`StrictTestDomain.SpectralTransport`, with Worker 36 credited as coauthor.
Here the domain input is a full representation over general positive-radius
algebras, and transport retains its algebra rather than using a different
rational presentation and a comparison isomorphism. The generic spectral-bound
lemmas are imported unchanged.

No nontrivial valuation, reducedness, nonzero quotient, or nonempty locus is
assumed. All presented algebras and domain tests lie in the stated universe of
`K`. The module does not construct every analytic domain, identify these tests
with all compact analytic-domain tests, construct an automorphism topology,
or assert continuity of group actions. Those are separate obligations.
