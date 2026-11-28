# Totally complex cyclic globalization with two split finite places

`Langlands.BaseChange.CyclicGlobalizationWithSplitPlacesTCStatement.{u, v}`
takes a cyclic extension `E/F` of characteristic-zero nonarchimedean local
fields of degree `l` with chosen generator `σ`. The topology on `E` is the
module topology over `F`. The local carriers are in independent universes
`Type u` and `Type v`, and the number-field carriers are in `Type`.

It asserts the existence of a cyclic Galois extension `L/K` of the same degree
with chosen generator `σ₀`. The base `K` satisfies
`NumberField.IsTotallyComplex K`, so every infinite place of `K` is complex.
The additive adele quotients `𝔸_K / K` and `𝔸_L / L` are compact.

- At a distinguished finite place `p` of `K` there is exactly one place `w` of
  `L` above `p`. The ring isomorphisms `a : F ≃+* p.adicCompletion K` and
  `b : E ≃+* w.1.adicCompletion L` are continuous in both directions. They
  identify the scalar embedding `F → E` with the canonical map of
  completions. The map `b` intertwines `σ` with the extension of `σ₀` given
  by `uniquePlaceCompletionAutEquiv`.
- Every infinite place of `K` and two distinct finite places of `K` different
  from `p` split completely. At each such place with completion `A`,
  `IsCyclicShiftSplit` identifies `A ⊗[K] L` with the product `Fin l → A`,
  carrying `id ⊗ σ₀` to precomposition by `finRotate l`.

## Sources

This is the totally complex form of
[`CyclicGlobalizationWithSplitPlacesStatement`](CyclicGlobalizationWithSplitPlaces.md).
Arthur and Clozel choose the distinguished completion, two other split
finite places and split infinite places in the proof of Proposition 6.9(ii).
Henniart's globalization in §3.3 adjoins quadratic fields split at the residue
prime to a totally real realization and retains the distinguished completion
comparison.

The imaginary quadratic step gives the totally complex base for this
formulation. An imaginary quadratic field split at the residue prime is
linearly disjoint from the totally real upper field, so adjoining it to both
fields preserves the Galois group and chosen generator. At a selected place
over the distinguished place the quadratic extension of completions is
trivial, so the same comparison holds there. Chebotarev with identity
Frobenius gives two other finite split places by successively excluding the
chosen places. Every infinite completion of the new base is complex, which
gives complete splitting there. At each split place the algebra maps to the
completion form a torsor under the cyclic Galois group, giving the stated
shift by indexing them with successive powers of the generator.

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula* (1989), Chapter I, proof of Proposition
  6.9(ii), printed p. 69 (PDF p. 83). Literature ID
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000), §3.3, printed p. 449 (PDF p. 11). Literature
  ID `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
