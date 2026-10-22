# Proof that continuous complex quasicharacters have open kernel

Worker 4 authored the Lean proof. Worker 21 checked the accepted target,
the implementation and its dependencies, retained the Lean source unchanged,
and prepared this paired contribution for independent checking and review.
Both workers are actual coauthors.

The proof supplies the required complex-analytic argument directly.
`complex_eq_one_of_forall_norm_pow_sub_one_lt` says that if every nonnegative
power of a complex number `z` has distance less than `1/2` from 1, then `z=1`.
Every power has real part at least `1/2`, so the sum of `n` powers has real
part, and hence norm, at least `n/2`. Multiplying this sum by `z-1` gives
`z^n-1`, whose norm is less than `1/2`. If `z` differs from 1, choose
`n > 1 / norm (z-1)` by the Archimedean property. The two bounds contradict
each other. The Lean argument uses the finite geometric-sum identity,
norm multiplicativity, real-part bounds, and arithmetic inequalities.

For the topological conclusion, continuity gives the open identity
neighborhood on which the character's value has distance less than `1/2`
from 1. `NonarchimedeanGroup G` supplies an open subgroup `K` contained
in that neighborhood. Every power of each element of `K` remains in `K`;
the complex lemma forces its character value to equal 1. Thus `K` lies in
the character kernel. Mathlib's theorem that a subgroup containing an open
subgroup is open concludes `isOpen_ker_of_continuous_complex_character`.

`continuousComplexCharacterOpenKernel` closes the complete proposition by
introducing its explicitly quantified nonarchimedean instance, character,
and continuity proof. The carrier universe remains arbitrary. No local
compactness, Hausdorffness of `G`, unitarity of the character, or unproved
assertion about small subgroups is assumed. The supporting complex lemma
and topological lemma are retained in this one proof module.

## Exact accepted target and dependencies

- Target: `Langlands.ContinuousComplexCharacterOpenKernel`, artifact
  `f56acc86-4146-4652-ace8-72cda7a39b7f`, version 1.
- Entry module:
  `Langlands.Representation.Twist.ContinuousCharacterStatement`.
- Statement publication: `18345ab3a6bd6ae07173195fa2be198e72d0f2f0`.
- Independent statement publication receipt:
  `a3eb48e4-cf9a-4c76-a077-fccba5c8f4f0`.
- Exact target fingerprint:
  `71fb79dc67fd0fd5a3cd7fc48f94c2d92ab84cbdd2d79e678bc81f065c0b5100`.
- Statement Lean SHA-256:
  `78a1e542d56cbdfe0f0cf448a0010e6ca2f3331fb3af7437e8d03927de7210c0`.
- Statement Markdown SHA-256:
  `0791b592e84c04c73f41709e1391c23f874061e8991bf57f5bf750dba5367b3a`.
- No project definition dependencies.
- Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
  Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 21 read the complete final statement review and confirmed that the
effective source hashes and target fingerprint match the local statement.
Fresh registry reads confirm the statement is accepted, published and current,
with no changed files or unavailable dependencies, and that the pinned
environment is accepted and public. The statement supplies the quasicharacter
convention; this proof is the internal geometric-sum and open-subgroup argument
described above.

The bound proof task is `745f8453-6791-4cc3-91e0-afaf64adb387`, revision 1.
Its proof module is `Langlands.Representation.Twist.ContinuousCharacterProof`,
and its closing declaration is `Langlands.continuousComplexCharacterOpenKernel`.
The closing theorem introduces the entire target's nonarchimedean hypothesis;
it does not require that hypothesis as an extra parameter outside the target.

Worker 21's development check compiled both modules without errors or warnings.
The closing theorem retains the arbitrary universe `uG`; its inspected axiom
closure and the proof module's closure contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no declared or disallowed axioms.
Development compilation and inspection do not replace the registered
independent checker, semantic review or publication. No concrete p-adic group
instance or local Langlands correspondence is established by this module.
