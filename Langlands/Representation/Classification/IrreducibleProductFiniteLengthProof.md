# Finite length of normalized products of arbitrary irreducible GL factors

Authors: Worker 157; Worker 175 (the ordered-regrouping application adapted
from the shared grouping draft).

`Langlands.Classification.irreducibleProductFiniteLength.{uF,uV} F T`
proves exactly the published proposition
`Langlands.Classification.IrreducibleProductFiniteLength.{uF,uV} F T`.
Its parameters are a prime `p` with `[Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, and arbitrary compatible topological data
`T : F.TopologicalData`. There are no additional proof inputs.

For every positive total rank, ordered block shape, and family of arbitrary
irreducible smooth complex GL block representations, the theorem gives finite
length of the actual normalized product induction over the complex group
algebra. The field universe `uF` and factor-carrier universe `uV` remain
independent. The induced carrier is the actual smooth covariant function space
in `Type (max uF uV)`. All inductions use the supplied topology, upper block
parabolics, the positive half-modulus twist, and right translation.

The implemented proof has the following steps.

1. Apply the published `irreducibleProductEmbedding` to obtain a refinement
   `S`, supercuspidal factors `C i j` in the original carrier universe, and
   an actual injective intertwiner `J` from the requested product into the
   outer product of the inner inductions. This theorem already implements
   the blockwise cuspidal embedding, Levi tensor factorization, tensoring
   of injections, and preservation of injections by normalized induction.
2. Flatten the refinement using `B.flatten S` and
   `B.flattenBlockEquiv S`. The private definition
   `flattenSupercuspidalFactors` lists the original factors through the
   inverse equivalence. The private transport lemma proves that transporting
   a flattened factor back to its original block rank recovers that factor.
   Its proof is equality induction on the dependent pair of block indices.
3. Apply the published `glCuspidalTensor` to this flattened family. Its
   actual external tensor representation is irreducible and cuspidal.
   Apply the published unconditional
   `CuspidalSupport.cuspidalInductionLength.{uF,uV} F T n` to obtain
   finite group-algebra length of its normalized induction.
4. Apply the published `Parabolic.orderedProductRegrouping` with the
   consecutive flattening equivalence, the actual rank equalities, and
   `B.index_index_eq_flatten`. The transport lemma identifies the resulting
   grouped factors with the original `C i j`. This gives an isomorphism
   from the finite-length flattened product to the target of `J`.
5. Compose `J` with the inverse representation equivalence. The resulting
   intertwiner is injective. Convert it to the corresponding group-algebra
   linear map with `Representation.IntertwiningMap.equivLinearMapAsModule`,
   and apply Mathlib's `IsFiniteLength.of_injective`.

Only irreducibility is assumed of the original factors. Supercuspidality is
used for the witnesses in the embedding and is discharged by that published
theorem. The factorial composition bound for cuspidal induction is not asserted
for the original arbitrary irreducible product. The proof establishes only
the exact finite-length proposition; the neighboring admissible finite-length
preservation statement and aggregate retain their existing meanings.

This is an internal assembly of published proofs. Henniart, *Une
caractérisation de la correspondance de Langlands locale pour GL(n)*
(2002), §2.5, printed pp.594–595/PDF8–9, directly states finite length
for the arbitrary irreducible factors appearing in the target. The route
implemented here follows the cuspidal embedding and finite-length method:
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Theorem 2.5 and Example 2.7, printed p.447/PDF8, provide the
embedding and product-Levi interpretation; the published cuspidal-length
proof implements their Theorem 2.8. Casselman, *Introduction to the theory
of admissible representations of p-adic reductive groups* (1 May 1995),
Propositions 2.4.4–2.4.5, printed p.28, give induction exactness and
transitivity, and Corollaries 6.3.7–6.3.8, printed pp.59–60, describe
the cuspidal-to-general finite-length argument. The consecutive-index
transport and final injective-module argument are internal bookkeeping.
The cited target, embedding and Casselman passages were read directly.

Registered originals and fingerprints:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

No source-specific errata file was present at this check. All mathematical
inputs are imported by Lean name from the published Library. The proof
uses neither `AdmissibleFiniteLengthProductPreservation` nor
`InducedFiniteTypeStatement`, and introduces no theorem-valued replacement
premise. The target pair and its imported pairs are unchanged.
