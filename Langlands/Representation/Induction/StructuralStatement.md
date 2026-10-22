# Structural induction statements

Worker 8 states the structural properties of Worker 15's accepted actual
induction construction. The proposition is a target for a separate proof;
defining it does not assume its truth. No assumed theorem fields or arbitrary
replacement predicates occur here.

`Langlands.Induction.StructuralStatement` has seven coherent clauses:

1. Frobenius reciprocity for smooth induction, as an actual complex-linear
   equivalence of intertwiner spaces whose formula is evaluation at the
   identity.
2. Preservation of short exact sequences by both smooth and compact induction,
   for the actual postcomposition maps, with injectivity, image equals kernel,
   and surjectivity all explicit. Smoothness of the middle representation
   suffices, since the end terms inherit it.
3. When the coset space is compact and the input is admissible, the canonical
   inclusion from compact induction to smooth induction is bijective and the
   latter is admissible.
4. Compatibility with a smooth scalar character of the ambient group, using
   actual representation equivalences whose function formula is
   `f(x) ↦ chi(x) * f(x)`. Both smooth and compact induction are included.
5. Preservation of a prescribed central scalar action when the ambient center
   lies in the inducing subgroup.
6. Transitivity of both smooth and compact induction through a closed subgroup
   `P` containing `H`. The inner inducing subgroup is the actual subgroup
   `H.subgroupOf P`; its representation is transported along Mathlib's canonical
   `Subgroup.subgroupOfEquivOfLe`. The equivalences flatten the nested functions
   by evaluation at the inner identity: `(e F)(x) = F(x)(1)`.
7. When `H` is open, compact induction is left adjoint to restriction. This is
   an actual complex-linear equivalence of intertwiner spaces, characterized
   on functions supported in `H` by `(e T)(f(1)) = T(f)`. Both representations
   are smooth.

The seven factors are the concrete definitions `SmoothFrobeniusClause`,
`InductionExactnessClause`, `CompactQuotientClause`, `InductionTwistClause`,
`InductionCentralActionClause`, `InductionTransitivityClause`, and
`OpenSubgroupAdjunctionClause` in the same namespace and file. They are not
arbitrary proposition parameters or assumed theorems. The aggregate target
places their conjunction under the common ambient hypotheses and closedness
of `H`; naming its factors does not change those hypotheses or conclusions.

All clauses use complex coefficients. The ambient group is a Hausdorff
topological group with an explicit compact-open neighborhood basis, and the
inducing subgroup is closed. These are the `l`-group and closed-subgroup
hypotheses of Bernstein and Zelevinsky. The group and three module universes
are independent. The function carriers have the necessary maximum universes;
no small-universe resizing, topology on the modules or finite-dimensional
carrier hypothesis is imposed.

The actual functions satisfy `f(h*x) = sigma(h)(f(x))`, with one open
subgroup fixing the entire function on the right. The action is
`(g*f)(x) = f(x*g)`. Compact induction uses compact projected nonzero support
in `H \ G`. These are unnormalized subgroup induction functors.
For normalized parabolic induction the input must first be inflated from the
Levi subgroup and twisted by the actual positive half-modulus character.
That specialization and its compatibility with normalized Jacquet reciprocity
remain separate work. This file does not identify an arbitrary supplied
character with the actual modulus.

## Originals read and correspondence

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Section 1.1 on printed page 442 / PDF page 3 defines an
`l`-group by Hausdorffness and a compact-open neighborhood basis.
Sections 1.2-1.8 on printed pages 443-444 / PDF pages 4-5 supply the category,
admissibility, characters, induction functions and right translation.
Section 1.9 on printed page 445 / PDF page 6 states:

- (a) exactness;
- (b) the adjunction;
- (c) transitivity;
- (e) coincidence and admissibility when the coset space is compact;
- (f) twist compatibility.

These passages were read in the original. Specialize its subgroup `U` to the
trivial group, its character to the trivial character, and its `M` to this
file's closed subgroup `H`. Its module factor is then one, so its `I` and `i`
are exactly the unnormalized subgroup constructions used here. The evaluation
formula in clause 1 determines the usual Frobenius equivalence.
The central-action clause is a direct derived consequence of covariance:
for central `z` in `H`, `f(x*z)=f(z*x)=sigma(z)f(x)`. It is not presented as
a separate numbered claim in the original.
For transitivity, specialize both unipotent subgroups in 1.9(c) to the trivial
group. The source's `M` is `P` and its `N` is `H`, viewed inside `P`.
Evaluation at the inner identity fixes the usual transitivity equivalence and
its orientation. The function formula is compatible with postcomposition by
intertwiners; no abstract replacement functor or unidentified subgroup is used.

The open-subgroup left adjunction in clause 7 is a derived consequence of the
same actual definition in 1.8, rather than an attribution to 1.9(b), which is
the other adjunction. Here is the derivation determining the statement and
the convention. For `v` in the inducing module, let `f_v` equal `sigma(h)v`
on `h` in `H`, and zero outside `H`. Openness of `H` and smoothness of
`sigma` make this a smooth induced function, with compact quotient support
consisting of the identity coset. A `G`-intertwiner `T` restricts to the
`H`-intertwiner `v ↦ T(f_v)`. Conversely, an `H`-intertwiner `A` gives
`T_A(f) = sum_{H*x} tau(x^(-1))(A(f(x)))`.
The sum has finitely many nonzero terms because `H \ G` is discrete and
the projected support of `f` is compact. Replacing `x` by `h*x` leaves
each summand unchanged by covariance and `H`-equivariance. Right translation
shows `G`-equivariance, and decomposition into functions supported on
individual cosets proves the two maps inverse. This argument needs no
choice of Haar measure and no topology on the module. The Lean formula
quantifies over the existing compact functions supported in `H`; it does
not introduce an assumed injection or an unproved canonical constructor.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- PDF SHA256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Original file:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Casselman Chapter II, Sections 11, Propositions II.11.1 and II.11.3,
printed/PDF pages 16-17, is a corroborating source lead. Its notation uses
normalized induction and therefore includes a relative modular-character
factor in Frobenius reciprocity. This draft does not silently remove that
factor from a normalized statement; its primary source specialization above
is explicitly unnormalized.

The later normalized duality, parabolic specialization, geometric lemma and cuspidal
support obligations remain with Worker 8. This pair is not full coverage of
the structural family.

## Exact accepted dependencies

The import is Worker 15's accepted definition artifact
`93ed47bc-5f1b-4f09-a702-ed2951bf683f`, version 1.
Its construction pair is `Langlands/Representation/Induction/Definitions`.
The Lean source SHA256 is
`2936c54b7596b3bfebc6f6f881c7a12c1eb34179290bfcb02068b1c50b8a3643`;
its Markdown SHA256 is
`9fc03b58ebdce911b5ff1046da802cb01419833f20eca318efbc53b354d5ac04`.
The complete pair was read. A fresh fetch confirms accepted, public and current
status at Library commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`,
with no missing or changed files and no unavailable dependencies. Its effective
bundle snapshot is
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
The implementation remains Worker 15's; this pair authors only the new proposition.

The construction's recorded exact prerequisites are smooth predicates
`665022df-625b-44ae-9dbd-425f6e266bab` version 1, smooth-part definitions
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1, and scalar-twist definitions
`c83db975-8b79-4fbb-9901-2db836910a0a` version 1. Fresh fetches of all three
confirm accepted, public and current status at that same Library commit.
The local Lean and Markdown hashes match their accepted effective bundles.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
All theorem proofs remain separate obligations.

The complete seven-clause proposition compiled successfully with the pinned native Lean
executable on October 16, 2026, with no diagnostics. A subsequent `#check` and
`#print` inspection confirmed the four independent universes, the complex
module hypotheses, the topology assumptions inside the proposition, and every
clause's premises and conclusion. Compilation and inspection are development
evidence; independent semantic acceptance and publication remain separate.
