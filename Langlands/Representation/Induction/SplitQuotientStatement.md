# Compact induction across a continuous split quotient

Worker 777 states
`Langlands.Induction.CompactInductionSplitQuotient.{uG,uV}`.
This is a proposition definition and a target for a separate proof.

Let `G L : Type uG` be topological groups. Let `r : G →* L` and
`s : L →* G` be group homomorphisms, with hypotheses `Continuous r` and
`Continuous s` and the section equation `r (s l) = l` for every `l : L`.
Let `H` be a subgroup of `G` with `IsClosed (H : Set G)` and
`r.ker ≤ H`. Write

- `H_L = H.comap s`, the Mathlib subgroup of `L` whose elements are the `l`
  with `s l ∈ H`;
- `i = s.subgroupComap H : H_L →* H`, Mathlib's restriction of `s`. Its
  underlying map is `s`, that is, `(i x : G) = s x`.

For every object `A` of the full category `Langlands.SmoothRep.{0,uG,uV} ℂ H`,
write `sigma = A.representation`. The kernel-triviality hypothesis is

`hA : ∀ h : H, r (h : G) = 1 → ∀ v : A, sigma h v = v`.

It says that `H ∩ ker r` acts trivially on the coefficients.

The conclusion is one existentially quantified family

`e A hA : ((compactInduced H sigma).comp s).Equiv
  (compactInduced H_L (sigma.comp i))`.

It is indexed by these objects and their kernel-triviality proofs. Each
`e A hA` is an actual `Representation.Equiv` of `L`-representations, so it is
complex-linear, bijective and `L`-equivariant. The source is the actual
compact induction from `H`, restricted to `L` along `s` by Mathlib's
`Representation.comp`. The target is the actual compact induction from `H_L`
of the coefficients restricted along `i`. Both sides use the published
`CompactFunctions`. Their elements are covariant functions,
`f(h*g) = sigma(h)(f(g))`, with one uniform open right stabilizer for the
entire function. Their projected nonzero support on the coset space is
compact. The induced action is right translation. These conditions are part
of the imported definitions; the statement neither weakens nor repeats them.

The family satisfies three conjuncts.

1. The restriction formula. For every `A`, `hA`, `f : CompactFunctions H sigma`
   and `l : L`,

   `eval H_L (sigma.comp i) (e A hA f).val l = eval H sigma f.val (s l)`.

   So the forward map is `f ↦ f ∘ s`.

2. The inverse formula. For every `A`, `hA`,
   `k : CompactFunctions H_L (sigma.comp i)` and `g : G`,

   `eval H sigma ((e A hA).symm k).val g = eval H_L (sigma.comp i) k.val (r g)`.

   So the inverse map is `k ↦ k ∘ r`.

3. Naturality. For every pair of objects `A`, `B` with proofs `hA`, `hB`, every
   morphism `T : A ⟶ B` and every `f : CompactFunctions H sigma_A`,

   `e B hB (compactInducedMap H (SmoothRep.hom T) f)
     = compactInducedMap H_L (restrictAlongMap i (SmoothRep.hom T)) (e A hA f)`.

   Both sides use the published `compactInducedMap`, which is postcomposition.

The two formulas determine the actual maps. Their existence, bijectivity and
equivariance are asserted, not assumed. The proposition has no further
premise: it assumes no quotient homeomorphism, compact-support preservation,
inverse map, bijectivity, lifting, exactness or comparison.

The coefficient modules are arbitrary complex modules carried by
`Type uV`. There is no topology, norm, completeness, dimension, admissibility
or length restriction on them, and the group universe `uG` is independent of
`uV`. The groups are arbitrary topological groups. The statement assumes no
Hausdorff, local compactness, compact-open basis, discreteness, finiteness or
p-adic matrix structure. Closedness of `H` is kept for the intended induction
setting, although the comparison does not appear to use it.

## Helper

The only new definition is `restrictAlongMap`. For a commutative ring `R`, a
group homomorphism `i : K →* H` and an `H`-intertwiner `T : ρ → σ`, it is the
same linear map `T.toLinearMap`, viewed as an intertwiner between
`ρ.comp i` and `σ.comp i`. Its equivariance at `k` is the original
equivariance at `i k`. In the proposition it restricts `SmoothRep.hom T` along
`i = s.subgroupComap H`. The Library contains a map with the same content,
`Langlands.Derivative.Mirabolic.continuousPullbackMap`. That map lives in a
p-adic mirabolic module, so this file uses a local elementary helper rather
than importing it. The helper adds no function space, quotient model or
subgroup.

## Original source and scope

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, §5.16 (Case IV₁), printed pages 465–466,
PDF pages 26–27. The entire section was read and visually checked, including
its reduction diagram and its continuation on page 466. The setup in
§5.1–5.7 and the start of §5.17 were also read.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Retained PDF:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- SHA-256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

In Case IV the source has `U = {e}` and `G = Q`. Its setup in §5.1 writes
`Q = NV` with `N ∩ V = {e}` and `N` normalizing `V`. In Case IV₁, `V ⊆ M = P`.
The source shows that `V` acts trivially on the coset space and passes to
`V`-coinvariants on `M \ Q`. It then identifies the result with induction
from `M ∩ N` to the complement `N`, which acts transitively on the coset
space. The proof uses the sheaf construction, the fiber computation through
§1.9(g) and §5.11, and the reconstruction of §5.14.

The Library already states and proves the same-ambient step as
`Langlands.Induction.CompactInductionNormalCoinvariants`, proved as
`Langlands.Induction.compactInductionNormalCoinvariants` in
`Langlands.Representation.Induction.NormalCoinvariantProof`. Its target is
compact induction on the original ambient group of coinvariant coefficients.
On that target the normal subgroup acts trivially. The present proposition is
an internal derived step. It converts such a same-ambient induction to
induction on a chosen complement. Here `r` models the quotient `Q → Q/V ≅ N`,
`s` the inclusion of the complement, `H` the subgroup `M`, and `H_L` the
subgroup `M ∩ N`. Kernel-triviality is what the coinvariant coefficients
satisfy after the radical coinvariants are taken.

The source does not print this comparison as a standalone theorem, and these
exact quantifiers and notation are not quoted from it. The proposition uses
unnormalized compact induction and no character. It does not assert the full
normalized parabolic orbit comparison. Normalization, the identification
`Q/V ≅ N` for actual parabolic data, and Case IV₂ in §5.17, which uses quotient
integration, are separate steps.

The intended proof route is provenance only and is not an input to the
statement. The forward map `f ∘ s` keeps covariance for `H_L`. Right
translation by `l` corresponds to right translation by `s l`. The uniform
stabilizer `K` pulls back to the open subgroup `s⁻¹ K`. For the inverse
`k ∘ r`, take `h ∈ H`. Then `s (r h)⁻¹ * h` lies in `ker r ⊆ H`. So
`s (r h) ∈ H`, that is, `r h ∈ H_L`. Kernel-triviality then gives
`sigma(h) = sigma(s (r h))`, which is covariance. The maps `s` and `r` induce
mutually inverse continuous maps between `H_L \ L` and `H \ G`. Both
composites are identities, because `g * s (r g)⁻¹ ∈ ker r ⊆ H`. They carry
the projected supports onto each other, so compactness is preserved.

## Imported constructions

`Induction.Definitions` supplies the actual compact function space,
`compactInduced`, evaluation `eval` and postcomposition `compactInducedMap`.
`Category.Basic`, which the induction module imports, supplies the full smooth
category and the underlying intertwiner `SmoothRep.hom`. Mathlib supplies
`Subgroup.comap`, `MonoidHom.subgroupComap`, `Representation.comp` and
`Representation.Equiv`. `Mathlib.Basic.Complex.Basic` supplies `ℂ`. Every
imported Lean/Markdown pair is preserved unchanged.
