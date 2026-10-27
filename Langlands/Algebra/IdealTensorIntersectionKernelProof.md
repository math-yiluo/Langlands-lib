# Proof of the ideal intersection tensor-kernel transport

`Langlands.Algebra.idealTensorIntersectionKernel.{u,v}` proves the Library
proposition `Langlands.Algebra.IdealTensorIntersectionKernelStatement.{u,v}`,
imported from `Langlands.Algebra.IdealTensorIntersectionKernelStatement`. Its
type is exactly that closed proposition, with independent universe levels `u`
(for the ring) and `v` (for the module). The proof uses only the hypothesis in
the statement: the map \(M\otimes_R(a+J)\to M\otimes_R R\) induced by the ideal
inclusion is injective. No Noetherian, local, finiteness, nonzero, flatness or
Tor hypothesis is used, and tensor injectivity for \(J\) is not assumed.

## Statement proved

Let \(R\) be a commutative ring, \(M\) an \(R\)-module and \(a,J\) ideals of
\(R\). If \(M\otimes_R(a+J)\to M\otimes_R R\) is injective, then every
\(x\in M\otimes_R a\) with zero image in \(M\otimes_R R\) is the image of some
\(z\in M\otimes_R(a\cap J)\) under the map induced by \(a\cap J\subseteq a\).
In Lean, \(a+J\) is `a ⊔ J`, \(a\cap J\) is `a ⊓ J`, and every tensored map is
`LinearMap.lTensor M`, that is \(\mathrm{id}_M\otimes(-)\).

## The implemented proof

1. **The exact pair.** The proof defines the anti-diagonal
   \(f:a\cap J\to a\times J\), \(c\mapsto(c,-c)\)
   (`(Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)`),
   and the addition map \(g:a\times J\to a+J\), \((b,d)\mapsto b+d\)
   (`(Submodule.inclusion le_sup_left).coprod (Submodule.inclusion le_sup_right)`).

2. **Exactness** (`Function.Exact f g`), via Mathlib's
   `LinearMap.exact_of_comp_of_mem_range`. First, \(g\circ f=0\) because
   \(c+(-c)=0\). Second, if \(g(b,d)=0\), then \(b+d=0\) in \(R\), so
   \(d=-b\). Hence \(b=-d\in J\), so \(b\in a\cap J\), and \(f(b)=(b,-b)=(b,d)\).

3. **Surjectivity of \(g\).** An element of \(a+J\) has the form \(b+d\) with
   \(b\in a\), \(d\in J\) (`Submodule.mem_sup`), and it is \(g(b,d)\).

4. **Right exactness of the tensor product.** Mathlib's
   `TensorProduct.lTensor_exact M hfg hg` (it needs both the exactness of
   \(f,g\) and the surjectivity of \(g\)) gives exactness of
   \(\mathrm{id}_M\otimes f\) and \(\mathrm{id}_M\otimes g\).

5. **Entering the kernel.** Let \(x\in M\otimes_R a\) have zero image in
   \(M\otimes_R R\), and let \(\xi=(\mathrm{id}_M\otimes\iota_1)(x)\in
   M\otimes_R(a\times J)\), where \(\iota_1=\) `LinearMap.inl R a J` is the
   first-factor inclusion. The composite
   \(a\xrightarrow{\iota_1}a\times J\xrightarrow{g}a+J\hookrightarrow R\) is the
   inclusion of \(a\) into \(R\) (checked elementwise by `ext; simp`). So by
   functoriality (`LinearMap.lTensor_comp`), the image of
   \((\mathrm{id}_M\otimes g)(\xi)\) in \(M\otimes_R R\) is the image of \(x\),
   which is zero. The assumed injectivity for \(a+J\) then gives
   \((\mathrm{id}_M\otimes g)(\xi)=0\).

6. **Lifting and projecting.** By step 4, \(\xi=(\mathrm{id}_M\otimes f)(z)\)
   for some \(z\in M\otimes_R(a\cap J)\). Let \(\pi_1=\) `LinearMap.fst R a J`.
   Since \(\pi_1\circ f\) is the inclusion \(a\cap J\subseteq a\), and
   \(\pi_1\circ\iota_1=\mathrm{id}_a\) (`LinearMap.fst_comp_inl`,
   `LinearMap.lTensor_id`), the image of \(z\) in \(M\otimes_R a\) is
   \((\mathrm{id}_M\otimes\pi_1)(\xi)=x\). This \(z\) is the required lift.

The theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The module imports only the statement module and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

## Provenance

The route follows the intersection/sum diagram in the proof of Stacks Project
Lemma 10.99.7, tag [00MK](https://stacks.math.columbia.edu/tag/00MK), as
extracted in the statement's Markdown and the proof task's context (the
anti-diagonal and addition maps, right exactness, and projection to the first
factor). There the ideal is on the left of the tensor product and \(J\) is a
power of a maximal ideal; the statement takes the needed sum-ideal injectivity as
a hypothesis instead of deriving it from Tor vanishing (Stacks Lemma 10.99.6,
tag [00MJ](https://stacks.math.columbia.edu/tag/00MJ)). The registered sources
are cited in the statement's Markdown; this proof introduces no further
mathematical source.

Worker 317 wrote this Lean proof from that description using the pinned Mathlib
(commit `5ed2965256430c3649e86755f9576b54eca72435`). After it compiled, it was
compared with the external implementation lead named in the task:
`LocalFlatnessCriterionAtPrime.ker_le_range_of_torVanish`, lines 387–451 of
`P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean` in
registered source `anthropic-flt-complete-lean-source-6e837e75` (content
SHA256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
Copyright 2026 Anthropic, PBC, Apache-2.0). That proof follows the same route
with the same two maps and the same Mathlib lemmas (`lTensor_exact`,
`Submodule.mem_sup`, `LinearMap.fst_comp_inl`), but first derives the sum-ideal
injectivity from a Tor-vanishing predicate. No source text was copied or adapted
from it: the exactness argument, the tactic steps and the names here differ. This
module imports nothing from it, and none of its `P2M.Util` or attribute-reset
machinery.
