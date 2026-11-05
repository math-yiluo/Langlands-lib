# The uniform standard canonical Jacquet section

`Langlands.Jacquet.standardCanonicalSection` proves the exact proposition
`Langlands.Jacquet.StandardCanonicalSectionStatement`. Worker 6 authored the
Lean proof and its original explanation. Worker 1564 prepared the pair for
submission and clarified the documentation.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.6.1, printed pp.176–177 / PDF pp.182–183,
especially (VI.6.1.2), the following single-image isomorphism and decomposition,
and the independence Proposition on printed p.177 / PDF p.183. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The explicit structural inputs come from V.5.2, printed p.123 / PDF p.129,
through the published actual-object basis predicates.

The theorem retains every premise and conclusion of the target. It concerns a
connected reductive group over a nonarchimedean local field of either
characteristic, with the canonical rational-point topology. The field and
representation carrier have independent universes. Its fixed maximal split
torus, standard parabolic, compatible split component and compact open subgroup
are the shared constructions. Standard-cocharacter existence, Levi
normalization and the Chapter V basis-member conditions remain explicit.
Admissibility supplies smoothness and finite dimensionality of the fixed
space; the representation space itself need not be finite dimensional.

The quotient is the actual unnormalized Jacquet quotient, restricted from
K-fixed vectors to the vectors fixed by the literal Levi intersection.
Compression is the actual compact average after applying the group element.
The proof uses the published definitions of these maps and of their all-power
stable image and generalized kernel.

The implemented argument proceeds as follows.

1. Uniform annihilation is proved by span induction on the actual Jacquet
   relations. For a generator `rho(n) v - v`, uniform compact containment of
   the singleton `{n}` gives a positive threshold after which conjugation
   carries `n` into K. Compact averaging is invariant under K, so it kills
   the translated relation. Addition takes the minimum of the two thresholds;
   scalar multiplication preserves the threshold. A finite spanning set of the restricted quotient
   kernel gives one threshold for the entire kernel.

2. Shrink this threshold to at most one. Monotonicity of the actual strict
   epsilon chambers preserves uniform annihilation. Every member then belongs
   to the actual weak and strict chambers; the published assembly theorem
   supplies its Iwahori contraction data from the basis-member hypotheses.

3. For each member, the published generalized-kernel equality and Fitting
   complement identify its single kernel with the quotient kernel. Applying
   compression to the Fitting decomposition identifies its single image with
   the stable image. The published stable-image quotient bijection therefore
   becomes a bijection on the single image, and its kernel and image are
   complementary.

4. The epsilon chamber is nonempty. Lift a standard cocharacter through the
   compatible split component and evaluate it using the common uniformizer
   section. Each outside-J character has a positive integral pairing, hence
   pairing at least one. Its norm is bounded by the inverse residue
   cardinality, strictly below one. One common positive power makes all these
   norms less than the prescribed threshold. This argument also applies when
   the character set is empty and needs no finite-root enumeration.

5. The chamber is closed under multiplication and its members commute:
   character norms multiply, the threshold is at most one, and the component
   is commutative. Published compression multiplicativity puts the product
   image inside both factor images. A nested-subspace lemma upgrades each
   inclusion to equality: surjectivity of the quotient on the smaller
   subspace and injectivity on the larger one determine every vector by its
   quotient. Thus all single images agree.

6. Choose one chamber member and take its published inverse restricted
   quotient, `compressedImageLift`, as the section. Its inverse and range laws
   give the right-inverse identity and the common range. Equality of inverse
   lifts on equal images proves equality with every lift throughout the
   chamber, for every proof of its restricted quotient's bijectivity.

This is an alternate proof route for the same target. Renard first uses
III.2.9 to find a compact open radical subgroup averaging the whole kernel to
zero, then uses dimension equalities for the single-image decomposition and
independence. The Lean proof instead uses span induction and a finite kernel
spanning set, reuses the published Fitting results, and uses quotient
injectivity and surjectivity for the nested-image equalities. It introduces no
additional structural or representation-theoretic assumptions.

The theorem proves independence of the contracting element in one chosen
nonempty epsilon chamber for the specified data and K. It does not establish
the global existence of the Chapter V basis, independence of the auxiliary
standard presentation or component, independence of K, second adjointness, or
whole-book completion.
