# Finite abelian reciprocity statements

This pair defines propositions on actual finite extensions of `Q_p`, their
field norms on units, quotient topologies, and algebra automorphism groups.
It does not construct a reciprocity map or assume one to establish its existence.
No theorem proof is claimed.

`FiniteAbelianReciprocityTheorems` combines three finite-level assertions.
Every prime is quantified, and the three field carriers may belong to independent
universes. Finite extension structures and their scalar towers are explicit.
`TopologicalData` supplies the existing local-field realizations. The separate
accepted `canonicalTopologicalData` constructor realizes this data for every
algebraic `PadicField`; there is no restriction to a chosen list of fields.
The assertions themselves quantify over every such supplied realization.

## The quotient and normalization

`FiniteAbelianReciprocity` asserts existence of a continuous multiplicative
equivalence from

`Fˣ / range (Units.map (Algebra.norm F))`

to `Gal(E/F)` for each finite abelian extension `E/F`. The source uses Mathlib's
quotient topology on the multiplicative topological group of the base field.
The target has Mathlib's Krull topology. There is no supplied equivalence in
the hypotheses. Surjectivity and the norm-kernel characterization are encoded
by the equivalence out of precisely this quotient.

Two conditions accompany the equivalence. For any base uniformizer `a`,
the inverse automorphism of `r([a])` acts on integral extension elements
modulo the maximal ideal as the `q_F`-power map. In field notation this is

`v_E((r([a]))⁻¹(x) - x^q_F) < 1` whenever `v_E(x) ≤ 1`.

Consequently `r([a])` acts as geometric Frobenius on the residue field.
The inverse in this formula is an inverse automorphism, not an invented inverse
map from an abelianization into a nonabelian Weil group. For an unramified
extension this specifies the usual geometric Frobenius automorphism. For a
ramified extension it specifies only its residue action, as it should.

The second condition says that an automorphism is the image of a base valuation
unit exactly when it acts trivially modulo the maximal ideal on every integral
extension element. Thus it identifies the image of valuation units with inertia.
These congruences use the actual discrete valuation from
`TopologicalData.discreteValuation`. The integer ring consists of elements
with valuation at most one and the maximal ideal of those with valuation less
than one. They do not define a new field or a substitute Galois group, and
they assert no separate residue exact-sequence theorem.

The order-zero test is applied only to `Fˣ`, so the convention `ord(0)=0`
cannot erroneously classify zero as a valuation unit. In the residue congruences,
zero is allowed among integral elements and satisfies the required formulas.

## The two finite-tower statements

`FiniteAbelianNormTransfer` considers `F ⊆ E ⊆ L` with `L/F` finite abelian.
It asserts that equivalences for `L/F` and `L/E` can be chosen so that:

- `N_E/F : Eˣ → Fˣ` corresponds to inclusion
  `Gal(L/E) → Gal(L/F)`, implemented by `AlgEquiv.restrictScalars`.
- Scalar inclusion `Fˣ → Eˣ` corresponds, after that same injective Galois
  inclusion, to raising an element of `Gal(L/F)` to `[E:F]`.

The second formula is the abelian ambient-group formula for transfer.
It has the opposite direction from norm. It does not identify a transfer
with a restriction map. A general nonabelian ambient group requires genuine
abelianizations and the general transfer, which are outside this particular
finite abelian component.
Indeed, Serre's transfer product over coset representatives telescopes in an
abelian group to the `[G:H]`-th power. Here `G=Gal(L/F)` and `H=Gal(L/E)`,
and `[G:H]=[E:F]`. Applying the injective inclusion of `H` makes this an
equality in the actual group `G`, exactly as written in Lean.

`FiniteAbelianRestriction` asserts compatible choices for the finite abelian
extensions `L/F` and `E/F` in the same tower. Restriction of the `L/F` value to
`E` is the `E/F` value. The restriction is Mathlib's `AlgEquiv.restrictNormalHom`.
The normality of `E/F` is derived by `IsAbelianGalois.tower_bot`; it is not an
extra hypothesis.

These are finite-level existence assertions. The aggregate does not assert
uniqueness of these choices, simultaneous coherence over all fields and all
towers, or that the choices in its three conjuncts are the same choices.
The local reciprocity system's globally coherent existence and uniqueness
remain separate required targets. The finite component is therefore not
presented as completion of the entire local class-field theorem layer.

## Original-source correspondence

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979),
registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `C:/Central-Library/Serre--Local Fields--1979.pdf`.

- XIII.4, Proposition 8 and its corollary, printed page 196 / PDF page 201:
  finite reciprocity identifies the norm quotient with the abelianized Galois
  group. Under the abelian-extension hypothesis the latter is the actual
  Galois group.
- XIII.4, Proposition 10(a)-(b), printed page 197 / PDF page 202:
  the norm/inclusion and inclusion/transfer diagrams.
- VII.8, Propositions 7-8, printed page 121 / PDF page 127:
  the coset-product formula for transfer, specialized here to an abelian
  ambient group.
- XIII.4, Proposition 12, printed page 197 / PDF page 202:
  restriction in the upper field.
- XIII.4, Proposition 13 and its corollary, printed pages 197-198 /
  PDF pages 202-203: Frobenius normalization and the valuation-unit image.
- XI.3, printed pages 170-171 / PDF pages 176-177 gives the same diagrams;
  XI.5, printed pages 173-175 / PDF pages 179-181, and XIV.6, printed
  pages 218-219 / PDF pages 223-224, supply openness of the norm subgroup.
  With the finite discrete Galois target, the finite reciprocity equivalence
  is then a topological equivalence for the actual quotient topology.

Worker 10 read the cited original passages. Serre uses arithmetic reciprocity.
The geometric convention here inverts its values throughout. Since the finite
Galois groups in these assertions are abelian, this inversion is a homomorphism,
and it preserves both tower diagrams and the image of every unit subgroup.
The same geometric convention appears in Tate, *Number theoretic background*,
section 1.4.1, printed page 6 / PDF page 15 of Corvallis Part II (1979), source
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The congruence presentation, packaging as existential continuous equivalences,
and abelian transfer power formula are derived interface formulations; they
are not claimed as literal copies of Serre's notation.

## Dependencies and current status

The project import is `Langlands.LocalField.Normalization.Definitions`,
accepted definition artifact `e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2` version 1,
with its exact dependency `Langlands.LocalField.Definitions`, artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1.
The all-fields realization constructor is separately accepted in
`Langlands.LocalField.Canonical`, artifact
`c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629` version 1; it is not assumed as a theorem
premise or needed to form these quantified propositions.
The two imported definition pairs were verified accepted, published and available
at Library commit `9007729971e6e6ecea63b5567b6d1621769ccfb0`.
Their effective Lean SHA256 values are respectively
`b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b`
and `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`;
their paired Markdown hashes are
`dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436`
and `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.

Mathlib supplies `IsAbelianGalois`, its tower consequences, `Algebra.norm`,
`Units.map`, quotient groups and their quotient topology, `ContinuousMulEquiv`,
Krull topology, scalar restriction and normal restriction. The pinned environment
is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 10 authored this pair. The shared incremental Lake build and exact
declaration inspection succeed with no errors or warnings, report a proposition
definition with universe parameters `u`, `v`, `w`, and report target fingerprint
`7076c656e23865f7c270177c5bd36baecf6bbedabda9dbdd6b8eb1ad15d11200`.
This is development evidence, not mathematical acceptance or a proof.
Independent semantic review and publication remain necessary.
The concrete Mathlib norm/quotient/Galois objects can also be exposed through
the definition companion's transparent wrappers; this pair installs no
competing mathematical structure or chosen reciprocity constructor.
