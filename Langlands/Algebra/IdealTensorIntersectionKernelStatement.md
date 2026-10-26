# Ideal intersection tensor-kernel transport

`Langlands.Algebra.IdealTensorIntersectionKernelStatement.{u,v}` defines the
following proposition. Let \(R\) be a commutative ring, let \(M\) be an
\(R\)-module with an additive commutative group structure, and let \(a,J\)
be ideals of \(R\). If
\[
M\otimes_R(a+J)\longrightarrow M\otimes_R R
\]
induced by the ideal inclusion is injective, then
\[
\ker\bigl(M\otimes_R a\longrightarrow M\otimes_R R\bigr)
\ \subseteq\
\operatorname{im}\bigl(M\otimes_R(a\cap J)\longrightarrow
                         M\otimes_R a\bigr).
\]
The second map is induced by the inclusion \(a\cap J\subseteq a\).
This module states the proposition; it contains no proof of it.

Elementwise, for every \(x\in M\otimes_R a\) whose image in
\(M\otimes_R R\) is zero, there exists \(z\in M\otimes_R(a\cap J)\)
whose image in \(M\otimes_R a\) is \(x\). The range in Lean expresses
exactly this existence of a lift.

The complete proposition quantifies over `R : Type u` and `M : Type v`,
with independent universe levels, then `[CommRing R]`, `[AddCommGroup M]`,
`[Module R M]`, and `(a J : Ideal R)`. Its sole additional hypothesis is
`Function.Injective (LinearMap.lTensor M (a ⊔ J).subtype)`.
Here `a ⊔ J` is the sum ideal and `a ⊓ J` is the intersection ideal.
`LinearMap.lTensor M f` means \(\mathrm{id}_M\otimes f\).
`Submodule.inclusion (inf_le_left : a ⊓ J ≤ a)` is the inclusion of the
intersection into \(a\). No Noetherian, local, finite, nonzero, or flat
hypothesis is imposed, and tensor injectivity for \(J\) is not assumed.

The formulation isolates the elementary exactness step associated with
\[
a\cap J \xrightarrow{\,c\mapsto(c,-c)\,}
a\oplus J \xrightarrow{\,(b,d)\mapsto b+d\,} a+J\longrightarrow0.
\]
For the intended proof, tensor right exactness applies because the two
maps form an exact pair and the sum map is surjective. In particular,
Mathlib's `TensorProduct.lTensor_exact` requires both exactness and
surjectivity. The assumed injectivity for \(a+J\) lets a kernel element
of the tensor inclusion for \(a\) enter the kernel of this tensored sum
map; projection to the \(a\) component gives the desired lift. This
explains the chosen statement and does not supply a formal proof here.

The original source is Stacks Project Lemma 10.99.7, tag
[00MK](https://stacks.math.columbia.edu/tag/00MK), specifically the
intersection/sum diagram and the resulting kernel containment in its
proof. The source specializes \(J\) to a power of a maximal ideal.
The present proposition extracts that elementary step for arbitrary
ideals, retaining only the needed tensor injectivity for their sum.
The source places the ideal on the left of the tensor product; tensor
symmetry over the commutative ring gives the orientation used here.
Stacks Lemma 10.99.6, tag
[00MJ](https://stacks.math.columbia.edu/tag/00MJ), supplies the
finite-length Tor-vanishing input in the original local argument.
Neither that input nor a categorical Tor comparison is part of this
statement. This is a derived prerequisite, not the verbatim statement
of either Stacks lemma or a statement of the full local flatness criterion.

Both originals were read in registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
files `00MK.html` (Lemma 10.99.7, proof) and `00MD.html` (Lemma 10.99.6,
statement and proof). The current tag pages and their comment sections
were checked on 26 October 2026; both displayed zero comments, and no
change to the relevant statements or proof steps was found. That bounded
check is retained as `stacks-flatness-00mk-00mj-current-2026-10-26`,
content SHA256
`867cdedaa7867ff53170db88408b2ad27481210df67727e5af2d3836ff0e5acb`,
files `00MK.html` and `00MJ.html`. No source-specific errata note was
present in the supplied project or Library notes.

An external implementation lead is
`LocalFlatnessCriterionAtPrime.ker_le_range_of_torVanish`, lines 387–451
of `P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`,
under namespace
`P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective`, in registered
source `anthropic-flt-complete-lean-source-6e837e75`, content SHA256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
revision `6e837e75355538c7f80bab5b956861e86c4eacc2`.
That proof first derives the sum-ideal injectivity from a presentation
property; this statement takes the required injectivity directly.
The accepted documentary audit
`notes/reuse/anthropic-local-flatness-audit.md` records development
feasibility and is not an accepted proof dependency.

Worker 439 supplied the exact mathematical target in the task specification;
Worker 651 authored this proposition definition and explanation. No external proof text is extracted in this
pair. The external source is Copyright 2026 Anthropic, PBC, licensed
under Apache-2.0, with its `LICENSE`, `NOTICE`, and `ATTRIBUTION.md`
retained in the registered source folder. No per-file attribution row
for the named implementation was found in `ATTRIBUTION.md`; its stated
coverage limits still apply. Any successor extraction must preserve the
applicable copyright, license, notices, and attribution.
