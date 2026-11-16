# Abstract extension degree and concrete fixed-field degree

`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractExtension_degree_eq_finrank`
proves exactly the published
`finiteAbstractExtension_degree_eq_finrankStatement k Ω K L hLK hnormal hKfinite hLKfinite`.
It retains the source's Type-0 fields, field/algebra/Galois instances, closed
subgroups `L ≤ K`, relative normality, and both finite-quotient hypotheses.
The actual positive degree of `FiniteAbstractExtension.ofInclusion L K hLK`,
coerced to a natural number, equals the actual module finrank of
`abstractRelativeFixedField k Ω hLK` over `abstractFixedField k Ω K`.

## Implemented proof and dependencies

The main proof installs the normality, finite-quotient, relative
finite-dimensionality and relative Galois witnesses locally. Its calculation
passes through four equal quantities:

1. The abstract extension's natural-valued degree equals the index of
   `extensionSubgroup K L hLK`. The private `degree_eq_index_local` proves
   this by `rfl`, unfolding the published positive degree and quotient
   constructions and Mathlib's subgroup index.
2. `Subgroup.index_eq_card` identifies that index with `Nat.card` of the
   relative quotient.
3. `Nat.card_congr` for the published
   `abstractExtensionQuotientEquivGaloisGroup` identifies this cardinality
   with that of the concrete relative Galois group.
4. Mathlib's `IsGalois.card_aut_eq_finrank` identifies the last cardinality
   with the required field degree.

The unpublished prerequisites are implemented only as private lemmas with
distinct names. `relativeFiniteDimensional_local` is the M099.018 scalar-tower
proof: use the published `FiniteGaloisSubextension.finite_extension_trans`
(M040.024) and `abstractFixedField_finiteDimensional` (M099.005), then
`FiniteDimensional.right`. `relativePresentationFiniteDimensional_local`
is the M099.019 identity-carrier linear-equivalence transport.
`relativeFixedFieldGalois_local` is the M099.012 proof: apply
`InfiniteGalois.normal_iff_isGalois` to the published
`abstractRelativeFixingSubgroup_normal` (M099.011). The quotient equivalence
import supplies the last proof transitively; the focused M099.006 import
supplies the fixed-field inclusion.

The private degree bridge replaces the still-unpublished M010.092 call in
the required direction using only the published definitions. These private
proofs make this candidate independent of pending prerequisite publications;
no second public copy of any adapted prerequisite name is introduced. The
statement and its imports are unchanged, and all new instances are local.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`.
In `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`
(SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`),
the public theorem is M099.020, signature lines 367–377 and proof lines
378–404. Private source copies are M099.018, lines 306–335; M099.019,
lines 339–363; and M099.012, lines 184–192.
The degree bridge corresponds to M010.092,
`ClassFormation.DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean:782–786`:
our helper is specialized to `ofInclusion`, states the equality in the
opposite direction, and uses definitional reduction in place of the source's
rewrite with `degree_coe`.

Both files are retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The port isolates the theorem and needed private proofs, prefixes the namespace
with `Langlands.NYLL`, replaces source imports by focused published modules,
states the exact published `Statement` application, and changes prerequisite
calls to the private names described above. The other proof bodies and the
main cardinality route follow the source. Unused namespace openings and
unrelated declarations are omitted. The private degree helper omits the
unused section Galois instance. This proves only the specified NYLL
support result.

The original copyright, authorship and Apache-2.0 header are retained.
The original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
