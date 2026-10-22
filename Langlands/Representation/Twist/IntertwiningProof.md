# Proof of the functorial laws for twisted intertwiners

Worker 4 authored the Lean proof and its initial explanation in task draft
revision 1, content key
`79fe5b7a16e268b0588d96c323baa6e7afa4c3263d588eeb9983ca0d0f7ec2ed`.
Worker 20 checked the accepted sources, all eight laws, and whole-target
coverage, and expanded this explanation. Worker 4 is retained as coauthor.

The eight reusable component lemmas establish the identity and composition
laws for `twistIntertwining` and `untwistIntertwining`, the reflexivity, inverse,
and composition laws for `twistEquiv`, and its compatibility with projection
to the underlying intertwiner.

Every component applies Mathlib's extensionality principle for the relevant
morphism type. After evaluation at a vector, the two sides are definitionally
equal: each twist construction retains the underlying linear map or linear
equivalence. The proofs close by reflexivity.

The final theorem `Langlands.twistIntertwiningCompatibility` introduces the
quantified character and three representations and assembles all eight
results, including the original universally quantified intertwiner and
equivalence arguments. For `g.comp f`, `f` is applied first; for `e.trans f`,
`e` is applied first. All endpoints and composition orders agree with the
accepted target and the pinned Mathlib operations.

The proof preserves arbitrary commutative-ring, group and module hypotheses
with five independent universes. It assumes no topology, smoothness,
finite dimension, irreducibility, or additional project result. The eight
component lemmas are retained together in this coherent proof module.

| Reusable declaration in `Langlands` | Equality after evaluation |
| --- | --- |
| `twistIntertwining_id` | Both sides send `v` to `v`. |
| `twistIntertwining_comp` | Both sides send `v` to `g (f v)`. |
| `untwistIntertwining_id` | Both sides send `v` to `v`. |
| `untwistIntertwining_comp` | Both sides send `v` to `g (f v)`. |
| `twistEquiv_refl` | Both sides send `v` to `v`. |
| `twistEquiv_symm` | Both sides apply the underlying inverse of `e`. |
| `twistEquiv_trans` | Both sides send `v` to `f (e v)`. |
| `twistEquiv_toIntertwiningMap` | Both sides send `v` to `e v`. |

Each component is tagged `@[simp]`; none assumes another project theorem.
The five universes independently parameterize `R`, `G`, `V`, `W`, and `U`.
The closing theorem has exactly the ambient instances of the accepted
proposition and introduces the character and representations inside its
proof. Its composition clauses preserve the target's quantifier order
`f` then `g`, even though the reusable composition lemmas take `g` then `f`.

The pinned Mathlib definitions are
`RepresentationTheory/Intertwining.lean`: `IntertwiningMap.id` at lines
199-201, `IntertwiningMap.comp` at 213-215, `Equiv.refl` at 374-376,
`Equiv.symm` at 396-400, and `Equiv.trans` at 424-427.
The common-twist cancellation argument is already proved within the
accepted `untwistIntertwining` construction. These eight laws require only
its unchanged underlying map, not an additional cancellation hypothesis.

## Exact accepted target and dependencies

- Target: `Langlands.TwistIntertwiningCompatibility`, artifact
  `9ced0943-6c7a-4eaa-8fcd-30fead271dd5`, version 1.
- Entry module: `Langlands.Representation.Twist.IntertwiningStatement`.
- Statement publication: `ae49c910fc083b371808e295df748d1d9c58b533`.
- Independent statement publication receipt:
  `42ec18f4-fb93-474a-8b51-1a996d22beb1`.
- Exact target fingerprint:
  `89c294dd3eceea50f3cac9406a206825c555167142a5a46ae10fea73001565bc`.
- Statement Lean SHA-256:
  `3d17e95add48ef32759a582c61ae075085186def31fda6ff5b11fd218feb54dc`.
- Statement Markdown SHA-256:
  `65b3f74d39687d503809e946521eb9ec052d3cd1c9562aee74011057c7f9ed63`.
- Twist construction:
  `c83db975-8b79-4fbb-9901-2db836910a0a`, version 1,
  `Langlands.Representation.Twist.Definitions`.
- Definition publication: `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`,
  independent receipt `f01ba766-11c9-4ebc-ae7c-c211f8fa9b27`.
- Definition Lean SHA-256:
  `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
- Definition Markdown SHA-256:
  `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc`.
- Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
  Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 20 read the complete initial and final semantic reports for the
target and construction, verified their current Library membership at
`ae49c910fc083b371808e295df748d1d9c58b533`, and matched all four source
hashes above. The proof imports only the accepted target, which imports
the accepted twist construction and its pinned Mathlib dependencies.

`IntertwiningStatement.md` records the motivating scalar-twist convention in
Henniart 2000, Section 1.2(2), printed page 440. These morphism laws are
internal consequences of the accepted constructors, not an assertion of
Henniart's local Langlands theorem. The actual implemented proof is the
extensionality argument above.

Worker 20 reread the retained Henniart original at Section 1.2(2),
printed page 440 (PDF page 2), and Section 1.1 footnote 1 on printed page 439.
The former uses the positive scalar tensor twist; the latter distinguishes
continuous quasicharacters from unitary characters. This algebraic proof
requires a unit-valued homomorphism only, with the broader scope explicitly
documented in the accepted definitions.

- Literature ID: `henniart-2000-simple-proof`.
- Verified source SHA-256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Retained original:
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.

Native compilation and complete-target inspection succeeded, and the closing
theorem's inspected axiom closure contains only `propext` and `Quot.sound`.
These are development checks. Acceptance requires the registered independent
proof checker and independent semantic review; Library publication is a
separate recorded step. No placeholders or project axioms are introduced.
