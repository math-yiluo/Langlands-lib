# Continuous degree characters and geometric normalization

Authored by Worker 53. This module constructs characters from an explicitly
supplied continuous integer degree. Its pullback specializations reuse the
accepted `Langlands.Weil.Pullback`; they do not construct a second Weil group.
The actual local residue map and finite-field Galois identification remain
separate arithmetic dependencies for the local assembly.

For a group `W : Type u` with a topology and `d : W →ₜ* Degree`, where
`Degree = Multiplicative ℤ` has the standard discrete topology, the character
`unramifiedCharacter d z` has value `z ^ (d w).toAdd` at `w`. Its target is
`ℂˣ` with the topology inherited through Mathlib's units interface from the usual
complex topology. There is no discrete topology installed on complex numbers
or their units, and no continuity-equivalence theorem is assumed.

`degreePowers` bundles Mathlib's `zpowersHom` as a continuous homomorphism:
every function from the discrete integer group is continuous.
`unramifiedCharacter` is composition with `d`. The bundled target enforces all
homomorphism and continuity obligations. `unramifiedCharacterHom` proves that
the construction is multiplicative in `z`. The kernel lemma gives value one
on `ker d`; the degree-one lemma gives value `z` at every supplied degree-one
element. No such element is chosen or assumed to exist. The composition lemma
is naturality under a supplied continuous homomorphism, in independent carrier
universe `v`.

For an explicitly positive natural number `q`, `cardinalityUnit q hq` is the
unit represented by the complex natural cast of `q`. The norm character uses
its inverse as `z`, so its complex value is `q ^ (-degree)`. It is one on inertia,
has value `q⁻¹` at geometric degree `+1`, and value `q` at degree `-1`.
The positivity premise is essential to construct this unit. At local-field
specialization, `q` must be the actual residue-field cardinality, not an
independent formal parameter. These generic declarations do not assert that
an arbitrary supplied degree is a residue-Galois degree.

`pullbackCharacter` and `pullbackNormCharacter` use the existing continuous
`Langlands.Weil.degree`. Their inertia-inclusion formulas follow from its
zero second coordinate. The implementation uses the original pullback carrier,
group, and topology unchanged. No surjectivity, compactness, Frobenius choice,
or reciprocity map is required for these constructors.

## Sources and correspondence

* Henniart, *Représentations du groupe de Weil d'un corps local* (1980),
  §2.1 and the opening of §2.2, printed p. 158, PDF p. 5: inertia and the integer
  quotient, and the determination of an unramified representation by its
  Frobenius value. The homomorphisms here implement the rank-one formula
  obtained from that quotient. They make no classification claim for arbitrary
  groups and degrees.
  Literature ID `henniart-1980-weil-representations`, source SHA256
  `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
* Tate, *Number theoretic background*, Corvallis proceedings, Part II (1979),
  §1.4.1, printed p. 6 / PDF p. 15, and §1.4.6, printed p. 7 / PDF p. 16:
  inverse Frobenius corresponds to a uniformizer and the Weil norm is compatible
  with the normalized field absolute value. Section 4.1.3, printed p. 20 /
  PDF p. 29, writes the norm as `q^(-v(w))`. These passages fix the sign in
  `normCharacter`: geometric Frobenius has degree `+1` and norm `q⁻¹`.
  Literature ID `tate-1979-number-theoretic-background`, source SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Both originals were read at the specified locations. The generalization to
an arbitrary continuous degree, bundled construction, and elementary formula
proofs are internal derived content by Worker 53.

## Exact dependencies and Mathlib audit

* `Langlands.Weil.Pullback`, definition artifact
  `993e4326-4390-4fc8-94a7-82829061b1ea`, version 1, accepted, published, and
  current when fetched. Lean SHA256
  `1dd3491a90d6849c98bd49a0abd9fa684313ef2b040c9ab11bc49d3967cd6380`;
  Markdown SHA256
  `f312612d762200dffabd64f3589383423c9b8ad933c891f607724193b298eed5`.
  Publication commit `32f1fbf4cd19ab3f273133995b573b41c814aaff`,
  receipt `96b60dc2-a3bf-4357-bd16-87bb744c872c`; confirmed current at
  `5bc58c2525e0499012801c80f17b6a9c04d57263`. Original author: Worker 2.
* Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
  Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
  Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
  Mathlib `Data/Int/Cast/Lemmas.lean` already provides `zpowersHom` and its
  evaluation formula. `ContinuousMonoidHom.comp`, discrete-domain continuity,
  units, natural casts, and integer power laws supply the remaining intrinsic
  obligations. No integer character theory is duplicated.

Compilation is development evidence only. This pair still requires independent
semantic review and Library publication.
