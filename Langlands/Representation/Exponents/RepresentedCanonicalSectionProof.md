# The canonical Jacquet section for a represented parabolic

Module `Langlands.Representation.Exponents.RepresentedCanonicalSectionProof`.
The theorem
`Langlands.Aubert.General.RepresentedParabolic.representedCanonicalSection`
proves exactly the published `RepresentedCanonicalSectionStatement.{u,v}` in the
same namespace. It retains all its hypotheses and universe parameters.
The target statement and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
version dated 9 July 2026, VI.6.1, display (VI.6.1.2) and the Proposition,
printed pp.176–177 / PDF pp.182–183. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The geometric input comes from the proved two-sided split-component contraction
and the companion `representedChamberIwahoriContraction`. The statement's paired
Markdown explains the choice of a small chamber for an arbitrary compact open
subgroup with the given ordered Iwahori decomposition.

## Generic helpers and their provenance

The private helpers in this module adapt the generic private arguments in the
published `Langlands.Representation.Jacquet.StandardCanonicalSectionProof`.
They retain its averaging and linear algebra proofs. This reuse is explicit
because those original private declarations cannot be imported by name.
All helpers below are derived internal lemmas, rather than additional source
statements.

`average_apply_of_mem` proves that the average over `K` of `ρ(k)v` equals the
average of `v` for `k ∈ K`, by identifying the two finite orbits. For an arbitrary
monotone family `Ω(ε)` of ambient subsets, `uniform_relations_average_zero`
uses the containment of any compact radical subset in
`t⁻¹(K ∩ N)t`, uniformly over `t ∈ Ω(ε)`, to show that the average of
`ρ(t)v` vanishes for every radical relation `v`, once `ε` is small enough.
The proof is induction on the span of the generating differences `ρ(n)w - w`.
For a generator it applies the averaging identity to `tnt⁻¹ ∈ K`;
sums use the minimum of the two thresholds, and scalar multiples use linearity.

`uniform_fixedKernel_compression_zero` then uses finite dimension of `V^K`.
The kernel of the fixed Jacquet map has a finite spanning set. The preceding
lemma kills every vector of that set uniformly on a suitable chamber; taking
the minimum of finitely many positive thresholds kills their span. This gives
`ker j ≤ ker C_t`, the content of (VI.6.1.2). Finite dimension is supplied by
admissibility in the final application.

`singleCompression_consequences` treats one Iwahori contraction satisfying that
kernel inclusion. The proved Iwahori contraction lemmas identify the supremum
of the power kernels with `ker j`. It follows that `ker C_t` is already that
supremum. The finite dimensional splitting into the power-kernel supremum and
the stable image then shows `range C_t = stableImage`. The proved stable-image
Jacquet bijection gives bijectivity on `range C_t`, and the helper also obtains
the kernel equality and complementary-subspace assertion.

`submodule_eq_of_quotient_bijective` states that two nested submodules on which
one map is respectively surjective and injective must agree.
`common_compression_range` applies it to the range of `C_{tt'}` inside the ranges
of `C_t` and `C_{t'}`. It uses `compressedAction_mul_of_factor` to write
`C_{tt'} = C_t C_{t'}`, commutativity of `t,t'`, closure of `Ω` under products,
and the Jacquet bijections on all three ranges.

## Geometric input and assembly

For the supplied root presentation, put
`Δ = {f ≫ α | α is simple and α ∉ J}` and define `Ω(ε)` to be the image in `G(k)`
of all points `t ∈ A(k)` satisfying `characterNorm α t < ε` for every `α ∈ Δ`.
This family is monotone in `ε`.

For a compact subset `Γ` of the radical point group, its ambient image is compact.
Apply `splitComponentOppositeContraction` to that image, the empty opposite
compact set, and the neighbourhood `K`. For every point in the resulting
chamber, `tΓt⁻¹ ⊆ K`. Its image belongs to the Levi and normalizes the radical,
so in fact `tΓt⁻¹ ⊆ K ∩ N`. Rewriting conjugation gives exactly the containment
required by `uniform_fixedKernel_compression_zero`.

Take the minimum of the positive threshold supplied by that helper and the
threshold from `representedChamberIwahoriContraction`. This minimum is positive
and at most one. Every point in its chamber gives an Iwahori contraction and
kills `ker j` after compression, so `singleCompression_consequences` applies.

The chosen chamber is closed under products: character norms multiply, are
nonnegative, and are less than a threshold at most one. Its ambient points
commute because `A` is commutative. Thus `common_compression_range` shows that all
compressed actions have the same range. The companion
`represented_chamber_nonempty` supplies a point `t₀` in the chosen chamber.
Define `s` to be `compressedImageLift` for its ambient image, using the proved
bijection on that compressed range. The identity
`fixedJacquetMap_compressedImageLift` makes `s` a section of `j`.

For each point of the chamber, the generic single-compression result supplies
clauses 2–6, and the uniform kernel argument supplies clause 1.
`range_compressedImageLift` and equality of all compressed ranges give clause 7.
Finally `compressedImageLift_eq_of_range_eq` proves clause 8 for every supplied
proof of bijectivity. Therefore the same section works throughout the chosen
chamber, as required by the Proposition.

The proof concerns all points of `A(k)` in the chamber and assumes only compact
openness and the stated Iwahori decomposition of `K`; no basis-member or
contraction hypothesis is added. The dependence of the threshold on the
admissible representation is exactly the order of quantifiers in the target.
