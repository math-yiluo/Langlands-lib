# Proof of the Artin–Rees bound for ideal tensor kernels

`Langlands.Algebra.artinReesTensorKernelBound.{u,v}` proves the Library
proposition `Langlands.Algebra.ArtinReesTensorKernelBoundStatement.{u,v}`,
imported from `Langlands.Algebra.ArtinReesTensorKernelBoundStatement`. Its
type is exactly that closed proposition, with independent universe levels `u`
(for the ring) and `v` (for the module). The statement pair and its imports are
unchanged.

## Statement proved

Let \(R\) be a commutative Noetherian ring, \(M\) an arbitrary \(R\)-module and
\(I\) an ideal of \(R\). Assume that for every ideal \(J\) and every \(k\) with
\(I^k\subseteq J\), the map \(M\otimes_R J\to M\otimes_R R\) induced by the
inclusion is injective. Then for every ideal \(a\) and every \(n\in\mathbb N\),
the kernel of \(M\otimes_R a\to M\otimes_R R\) lies in \(I^n(M\otimes_R a)\),
written `I ^ n • ⊤` in Lean. Every tensored map is `LinearMap.lTensor M`, that is
\(\mathrm{id}_M\otimes(-)\).

## Helper lemma

`Langlands.Algebra.range_lTensor_inclusion_le_smul_top` takes
`R : Type u`, `M : Type v` (commutative ring, module), ideals `a b K : Ideal R`,
and hypotheses `hba : b ≤ a` and `hb : b ≤ K * a`. It proves
`LinearMap.range (LinearMap.lTensor M (Submodule.inclusion hba)) ≤
(K • ⊤ : Submodule R (M ⊗[R] a))`: if \(b\subseteq a\) and \(b\subseteq Ka\),
then the image of \(M\otimes_R b\to M\otimes_R a\) lies in \(K(M\otimes_R a)\).

Proof: by the default induction principle on \(M\otimes_R b\) it suffices to
treat pure tensors \(m\otimes c\), \(c\in b\), and sums (closure under `add_mem`).
A pure tensor maps to \(m\otimes c\) with \(c\) now viewed in \(a\)
(`LinearMap.lTensor_tmul`). The element \(c\) of \(a\) lies in the submodule
\(K\cdot\top\) of \(a\): by Mathlib's `Submodule.mem_smul_top_iff` this means
\(c\in K\cdot a\) as an element of \(R\), and `Ideal.smul_eq_mul` turns this into
`hb`. The linear map \(y\mapsto m\otimes y\), `TensorProduct.mk R M a m`, carries
\(K\cdot\top\) into \(K\cdot\top\) (`Submodule.smul_top_le_comap_smul_top`), so
\(m\otimes c\in K(M\otimes_R a)\).

## Main proof

1. **Artin–Rees on \(R\).** Mathlib's `Ideal.exists_pow_inf_eq_pow_smul I a`,
   applied to the ideal \(a\) as a submodule of the finite \(R\)-module \(R\)
   (this is where `IsNoetherianRing R` is used), gives \(c\) with
   \(I^m\cdot\top\cap a=I^{m-c}(I^c\cdot\top\cap a)\) for \(m\ge c\). Taking
   \(m=n+c\) and rewriting \(n+c-c=n\) (`Nat.add_sub_cancel`), a short `calc`
   gives `hAR : a ⊓ I ^ (n + c) ≤ I ^ n * a`: first
   \(a\cap I^{n+c}=I^{n+c}\cdot\top\cap a\) (`inf_comm`, `Ideal.smul_eq_mul`,
   `Ideal.mul_top`), then the Artin–Rees equality, then monotonicity
   \(I^n(I^c\cdot\top\cap a)\subseteq I^n a\) (`smul_mono_right` with
   `inf_le_right`). No finiteness of \(M\) is used.

2. **Injectivity for \(a+I^{n+c}\).** The hypothesis, applied with
   \(J=a+I^{n+c}\) and \(k=n+c\) (`le_sup_right`), shows that
   `LinearMap.lTensor M (a ⊔ I ^ (n + c)).subtype` is injective.

3. **Lifting through the intersection.** The published theorem
   `Langlands.Algebra.idealTensorIntersectionKernel`, imported from
   `Langlands.Algebra.IdealTensorIntersectionKernelProof`, proves
   `IdealTensorIntersectionKernelStatement`. Applied to `R`, `M`, `a`,
   `I ^ (n + c)`, the injectivity from step 2 and the kernel element `x`, it
   gives \(z\in M\otimes_R(a\cap I^{n+c})\) whose image under the tensored
   inclusion \(a\cap I^{n+c}\subseteq a\) is \(x\). The intersection/sum diagram
   chase is not repeated here.

4. **Factoring through \(I^n a\).** The inclusion
   \(a\cap I^{n+c}\subseteq a\) equals the composite of the inclusions
   \(a\cap I^{n+c}\subseteq I^n a\) (`hAR`) and \(I^n a\subseteq a\)
   (`Ideal.mul_le_right`); this holds by `rfl`. Functoriality
   (`LinearMap.lTensor_comp`) writes \(x\) as the image of an element of
   \(M\otimes_R I^n a\) under the tensored inclusion \(I^n a\subseteq a\). The
   helper lemma with \(b=I^n a\) and \(K=I^n\) (`le_rfl`) and
   `LinearMap.mem_range_self` place \(x\) in `I ^ n • ⊤`.

The theorem depends only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. The module imports the statement module,
`Langlands.Algebra.IdealTensorIntersectionKernelProof` and
`Mathlib.RingTheory.Filtration` (for the Artin–Rees lemma).

## Sources and attribution

The route is the Artin–Rees step of the proof of Stacks Project Lemma 10.99.7,
tag [00MK](https://stacks.math.columbia.edu/tag/00MK): the kernel \(K\) lies in
the image of \((I\cap\mathfrak m^n)\otimes_R M\), and Artin–Rees (Lemma 10.51.2)
puts it in \(\mathfrak m^{n-c}(I\otimes_R M)\). Here the ideal is on the right of
the tensor product, \(I\) replaces \(\mathfrak m\), the source's \(n\) is
\(n+c\), and the finite-colength injectivity that the source derives from Lemma
10.99.6 (tag [00MJ](https://stacks.math.columbia.edu/tag/00MJ)) is the hypothesis
of the statement. The passage was read in registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00MK.html`. The registered current tag-page snapshot
`stacks-flatness-00mk-00mj-current-2026-10-26`, content SHA256
`867cdedaa7867ff53170db88408b2ad27481210df67727e5af2d3836ff0e5acb`, shows no
comments on `00MK.html` or `00MJ.html`, and no errata note for these sources
exists in the project or Library notes. The source's final completion argument
is not used: the statement stops at the power bounds.

The external implementation lead is `range_lTensor_inclusion_le_smul` and the
power-bound part of `flat_of_torVanish_pow` (lines 440–470 and 518–550) in
namespace
`P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime`,
file `P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`, in
registered source `anthropic-flt-complete-lean-source-6e837e75`, content SHA256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, revision
`6e837e75355538c7f80bab5b956861e86c4eacc2`; that source is Copyright 2026
Anthropic, PBC, under Apache-2.0. Worker 855 read those lines before writing
this module, which follows the same mathematical route (Artin–Rees at \(n+c\),
then factoring the inclusion through \(I^n a\)). No code was extracted: the Lean
text was written for this module and differs from the source. The source proves
its range lemma by nested element induction over `Submodule.smul_induction_on'`;
the helper here instead uses `Submodule.mem_smul_top_iff` and
`Submodule.smul_top_le_comap_smul_top`. The source derives `hAR` elementwise for
all \(m\); here it is a `calc` for the given \(n\) using `smul_mono_right`. The
source obtains the intersection lift from a Tor-vanishing predicate in its own
`ker_le_range_of_torVanish`; here it is the published Library theorem, and the
needed injectivity is the statement's hypothesis. The source's mixed-ring
finiteness and Krull-intersection tail is not used. Neither the external source
nor `P2M.Util` is imported.
