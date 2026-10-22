# Proof of canonical realization compatibility

The closing theorem `Langlands.PadicField.canonicalCompatibility` proves
`CanonicalCompatibilityStatement.{u} (p := p)` for every prime `p` and every
carrier universe `u`. It retains every quantifier and conclusion of the
target. The only prime hypothesis is `[Fact p.Prime]`; the main quantified
`F : PadicField.{u} p` already contains the algebraic finite-extension data.
No topological realization or additional project assumption is a premise.

All component lemmas remain in this coherent proof module and are available
for later use. The proof follows the selected Mathlib interfaces rather than
reproving the general theory of local fields.

## Implemented argument

`canonicalTopologicalData_topology` installs the topology and module-topology
certificate of the actual canonical realization. Mathlib's
`eq_moduleTopology (Padic p) F.Carrier` then identifies it with the accepted
canonical module topology. `canonicalTopologicalData_normTopology` unfolds
the construction to show that its topology is precisely the one carried by
the spectral normed field.

`canonicalValuation_coe` unfolds the numerical valuation: its value, coerced
from `NNReal` to `Real`, is the spectral norm. The relation was defined using
`ValuativeRel.ofValuation`, so `canonicalValuation_compatible` is the existing
`Valuation.Compatible.ofValuation` certificate.
`canonicalTopologicalData_vle` changes the selected relation to comparison
of the numerical valuation values. The equivalence `NNReal.coe_le_coe`
then identifies this with comparison of the real-valued canonical norm.
Both directions include zero values.

`canonicalNorm_algebraMap` is Mathlib's `spectralNorm_extends`.
`canonicalNorm_prime` specializes it to the integer `p`, using `map_natCast`
and `Padic.norm_p`. Thus the normalization is explicitly `|p| = p⁻¹`.
`canonicalTopologicalData_base_vle` first uses the already proved norm
comparison, then replaces both norms of base images by the original p-adic
norms. Negating `Padic.norm_lt_norm_iff_mulValuation_lt` gives equivalence
of the two non-strict comparisons. This proves preservation and reflection
of the existing p-adic valuative comparison along the specified algebra map.

`canonical_complete_proper` installs the explicit canonical normed field
and normed algebra. It invokes `FiniteDimensional.complete` and
`FiniteDimensional.proper` over `Padic p`. These supply completeness of
that norm's uniformity and properness of that metric.

`canonical_localField_properties` installs the actual realization's
topology, valuative relation, and `IsNonarchimedeanLocalField` certificate.
Existing Mathlib instances then supply local compactness, compactness of
the valuation integer ring, its discrete valuation ring structure,
discreteness of the relation, and finiteness of the residue field.
The proof does not replace any of those interfaces.

`canonical_rational_topology` first identifies the canonical realization's
topology with the module topology. Applying `eq_moduleTopology` to the
usual `Padic p` topology proves equality with the topology in the accepted
`rationalTopologicalData`. `canonical_rational_vle` specializes the
already proved base comparison to `rational p`. Its algebra map is the
identity and its usual relation is the existing p-adic valuation relation.
These lemmas compare mathematical structures without asserting equality
of the whole packages.

Finally, `canonicalCompatibility` introduces an arbitrary `F` and assembles
all ten general clauses, followed by both rational compatibility clauses.
It proves the entire proposition, not a restricted specialization.

## Structures, sources, and exact dependencies

Only the statement module `Langlands.LocalField.CanonicalStatement` is
imported directly. It in turn imports the canonical constructor and accepted
algebraic interface. All instances in the proof are selected locally, and
the theorem statements explicitly fix the relevant topology, relation, or
normed field. The carrier universe remains arbitrary.

The construction uses the base-extending norm. No conversion to the
residue-cardinality normalization, ramification calculation, or integral
closure identification is asserted. The target's source correspondence
is documented in `CanonicalStatement.md`: Henniart Section 1.1 specifies
the general finite extension, and Serre Chapter II Sections 1-2 gives the
topology, completeness, and prolongation conventions. This proof is an
internal derivation from exact accepted project definitions and pinned
Mathlib results; it does not claim a new source proof of that general theory.

The project interface is definition artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1. The constructor
is accepted definition artifact `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`,
version 1, published at commit
`9db46907db3181b0c1dfd287b8ab2f1f02054cab` with independent receipt
`24df660d770545809d3f2ad0d607c9bb`. Its effective snapshot is
`bdbf7a14a6a5d5800958d1d758d3a90273f129253b41a85d6bca034255b7abb9`;
the Lean and Markdown hashes are
`e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48`
and `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d`.
Both definitions are accepted, published, and current, and the local pairs
match their effective published versions. The exact accepted statement is
`da56ec1d-e753-4f10-a532-f1330f5ec063`, version 1, with target fingerprint
`31cf58218ce1e184e0f1463a4413ee1703b7ae569e191bc4a046c0896b001df8`.
It is published at commit `9007729971e6e6ecea63b5567b6d1621769ccfb0`,
with independent receipt `96f72413bc8c44248819787ef8b044a0` and effective
snapshot
`dd0dcacc51cb14861f05bf78ad2d8453aa25323babcceeb5be63a4580af3f84d`.
Its Lean and Markdown hashes are
`7efb82ba3fc852b3b714dc317f08b428fb2bb9b5e2a51f7a22da3b83f3ec5246`
and `cf84a8defa8ddee1c1d21a8d01bd1255ddcda6718917a246c11be892b66a1d99`.
A fresh fetch confirms accepted, public, published, and current status,
with no missing or changed files or unavailable dependencies. The final
published pair matches the local pair used by this proof.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib
at `5ed2965256430c3649e86755f9576b54eca72435`. The main reused interfaces
are in Mathlib's `Analysis/Normed/Module/FiniteDimension.lean`,
`Topology/Algebra/Module/FiniteDimension.lean`,
`Analysis/Normed/Unbundled/SpectralNorm.lean`,
`NumberTheory/LocalField/Basic.lean`, and p-adic norm/valuation modules.

## Validation and authorship

Worker 26 authored the complete Lean proof and the original Markdown.
Worker 37 checked the supplied proof and exact accepted dependencies,
retained the Lean source unchanged, and prepared this proof contribution.
Native compilation of the constructor, target, and proof succeeded without
errors or warnings. A separate universe-polymorphic example bound the closing
theorem to the whole target. Native axiom inspection of the closing
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
There are no placeholders or project axioms.

The reused proof has Lean SHA256
`8353938d38bd3439aa35b345b907d86d2a0418240f9cf3002a1258df37ea8182`.
Fresh dependency checks at Library
`9007729971e6e6ecea63b5567b6d1621769ccfb0` confirm that the target and both
definition versions remain accepted, published, and current. All six
dependency source hashes match their effective published records.

These checks are development evidence. This contribution is submitted under
proof task `3267379a-8999-420b-9d05-0da91ddfef7f`, revision 1, which binds
the exact statement version above to this module and closing theorem.
Acceptance requires registered independent proof checking, independent
semantic review, and publication to the current Library.
