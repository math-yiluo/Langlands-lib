# Uniform block-scalar contraction

Author: Worker 70.

This module states three scalar-geometric claims about the actual general
linear group. Every new declaration is a transparent `def` returning `Prop`.
The module proves none of these claims. All names below belong to
`Langlands.GeneralLinear.BlockShape`.

## Parameters and conventions

The field is any `F : PadicField.{uF} p`, for any prime `p`, and
`T : F.TopologicalData` is supplied by the caller. The rank is any `n : ℕ`
and the ordered positive block shape is any `B : BlockShape n`. The uniform
compact statement installs precisely `T.topology` on `F.Carrier`; the ambient
`GeneralLinear n F.Carrier` then carries its induced matrix-unit topology.
There is no extra ambient topology parameter and no substitution of the
canonical realization.

The scalar tuple has type `Fin B.length → F.Carrierˣ`. Its ambient matrix is
exactly `B.blockScalar F.Carrier a`. The unchanged predicates
`B.IsStrictlyContracting T a` and `B.IsDeeplyContracting T ε a` compare,
respectively with `1` and `ε`, the real value of
`T.normalizedAbsUnits (a i * (a j)⁻¹)` for every `i < j`.
Thus the residue-cardinality-normalized absolute value and all-pairs
convention are inherited directly from `BlockIwahoriDefinitions`.

## The three components

1. `DeepChamberNonempty B T` states that for every real `ε > 0` there is a
   tuple `a` satisfying `B.IsDeeplyContracting T ε a`. In particular, taking
   `ε = 1` would supply a strictly contracting tuple, using the published
   `IsDeeplyContracting.strict`. Strict contraction is not an external
   existence assumption.
2. `UniformCompactBlockContraction B T` quantifies over two ambient subsets
   `Cplus` and `Cminus` of `GL_n(F)`. Both ambient compactness hypotheses and
   the containments in the actual `B.unipotentSubgroup F.Carrier` and
   `B.oppositeUnipotentSubgroup F.Carrier` are explicit. For every ambient
   identity neighborhood `U`, it asserts a real `ε` with `0 < ε ≤ 1` such
   that **every** ε-deep tuple `a` satisfies
   `aGL * x * aGL⁻¹ ∈ U` for every `x ∈ Cplus` and
   `aGL⁻¹ * y * aGL ∈ U` for every `y ∈ Cminus`, where
   `aGL = B.blockScalar F.Carrier a`. One ε works for both sets. It can depend
   on the sets and neighborhood, but is chosen before the universal tuple.
   The sets need not be groups. The hypothesis on `U` is membership in the
   neighborhood filter at the identity; `U` need not be open or a subgroup.
3. `StrictPowersEventuallyDeep B T` states that, for each strictly contracting
   `a` and every real `ε > 0`, some natural `r` satisfies: for every natural
   `s ≥ r`, the tuple `fun i => (a i)^s` is ε-deep. This is eventual entry of
   all subsequent powers, not just existence of a single suitable power.

`BlockContractionStatement.{uF}` universally quantifies over `p`, its primality
instance, `F`, `T`, `n`, and `B`, and conjoins the three components in the order
above. The field universe is unconstrained.

Only ratios are restricted. Multiplying every scalar by an arbitrary common
unit leaves these ratios and both conjugations unchanged, so there is no
bound on a common central scalar. All ranks and shapes are retained, including
rank zero, the empty shape and one-block shapes. With at most one block there
are no pairs `i < j`; the chamber inequalities are vacuous, and both actual
radicals are trivial. The identity lies in every identity neighborhood, so
these cases impose no additional hypotheses. No Iwahori factorization,
representation, admissibility or Haar-scaling assertion is included.

## Source correspondence and derived formulation

The motivation is Bill Casselman, *Introduction to admissible representations
of p-adic groups*, Chapter III: *Induced representations and the Jacquet
module*, revision April 29, 2019, sections 4–6, printed/PDF pages 5–8.
The retained source is registered as `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
at `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
These pages were read, and no source-specific project errata file was found.

Section 4, page 5, gives the two contraction directions in an Iwahori
factorization. The proof of III.5.4, page 6, uses expanding conjugates of a
fixed radical subgroup along powers of a strict chamber element. III.5.5,
page 7, uses a chamber element to obtain a required containment. III.6.2,
pages 7–8, states canonical-pairing asymptotics for all sufficiently deep
chamber elements. These motivate the scalar geometry needed by subsequent
representation-theoretic proofs. They do not state the present three-part
compact-set formulation as a numbered theorem.

This is a derived concrete `GL_n` formulation. The published
`blockScalar_conj_apply` multiplies an upper `(i,j)` block entry, for `i < j`,
by `a_i/a_j`. The published `blockScalar_inv_conj_apply`, applied to the lower
`(j,i)` block, multiplies by `(a_j)⁻¹*a_i`, the same ratio since field units
commute. These actual matrix formulas fix the orientations independently of
overbars that PDF text extraction drops from the source.

The expected derivation of the first component uses a field unit `t` with
normalized absolute value strictly between zero and one. For sufficiently
large natural `N`, the ordered tuple
`a_i = t^(N * (B.length - 1 - i.val))` has all forward ratios less than ε.
For the second component, the finitely many free block entries on the two
compact sets have a common bound. Sufficiently small root ratios make all
these entries uniformly small. The diagonal blocks remain the identity,
and finite matrix coordinates control neighborhoods at the identity; the
inverse-matrix coordinate in the ambient unit topology is continuous there.
The third component follows from powers of finitely many real root ratios,
each strictly below one. These are mathematical provenance and intended
proof directions, not Lean proofs supplied by this module.

## Consequences for a later proof

Assume the three claims have been proved. Let `K` be any open subgroup of
the actual `GL_n(F)` for `T.topology`, and let `a` be strictly contracting.
For `x` in the actual upper radical and `y` in the actual opposite radical,
apply the uniform compact claim to the singleton sets `{x}` and `{y}` and
the identity neighborhood `(K : Set (GeneralLinear n F.Carrier))`.
This gives ε with `0 < ε ≤ 1`. Apply the power claim to obtain a threshold
`r`; for every `s ≥ r`, both conjugates lie in `K`.

The existing radical-preservation lemmas
`blockScalar_conj_mem_unipotentSubgroup` and
`blockScalar_inv_conj_mem_oppositeUnipotentSubgroup` also put them in the
corresponding radicals. Since `blockScalar` is a monoid homomorphism, the
matrix of the pointwise tuple `a^s` equals `(B.blockScalar F.Carrier a)^s`.
Consequently, for every sufficiently large `s`,
`aGL^s * x * aGL^(-s)` lies in `K ∩ N`, and
`aGL^(-s) * y * aGL^s` lies in `K ∩ Nop`, where `aGL^(-s)` denotes the
inverse of `aGL^s`. In the existing API these intersections are
`B.iwahoriUpper F.Carrier K.toSubgroup` and
`B.iwahoriLower F.Carrier K.toSubgroup`.

These consequences require no compactness or factorization of `K`.
A later proof should expose them for consumers. They are not already proved
theorems or additional theorem declarations in this statement module.
