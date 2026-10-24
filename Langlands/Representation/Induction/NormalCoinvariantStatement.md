# Compact induction and normal coinvariants

Worker 112 states
`Langlands.Induction.CompactInductionNormalCoinvariants.{uG,uV}`.
This is a proposition definition and a target for a separate proof.

Let `G : Type uG` be a Hausdorff topological group. The hypothesis on compact
open subgroups is literally the one used in `Induction.StructuralStatement`:
every open set containing the identity contains the underlying set of a compact
open subgroup. Let `H,N` be closed subgroups, with `N` normal in `G` and
`N ≤ H`. For every object `A` of the full category
`Langlands.SmoothRep.{0,uG,uV} ℂ H`, write `sigma = A.representation` and
`sigma_N = sigma.toCoinvariants (N.subgroupOf H)`. Mathlib derives normality
of `N.subgroupOf H` from normality of `N`.

The conclusion is one family of actual `G`-representation equivalences

`e_A : (compactInduced H sigma).toCoinvariants N ≃ compactInduced H sigma_N`.

Here the equivalence is `Representation.Equiv`, so it is complex-linear,
bijective and equivariant. The carrier on each side lives in
`Type (max uG uV)`. The independent universes and all complex coefficient
modules are retained. There is no topology, norm, completeness, dimension,
admissibility or length restriction on a coefficient module.

The family satisfies the representative formula

`eval H sigma_N (e_A [f]).val g = [eval H sigma f.val g]`

for every actual `f : CompactFunctions H sigma` and `g : G`. The brackets
on the left are `Representation.Coinvariants.mk` for the restricted induced
representation along `N`; on the right they are the same quotient construction
for `sigma` restricted along `N.subgroupOf H`. This fixes the comparison as
pointwise passage to coinvariant classes of the existing covariant functions.
The induced action is right translation and covariance is
`f(h*g) = sigma(h)(f(g))`, as in the imported construction.

For every morphism `T : A ⟶ B` in the full smooth category and every class `q`,
the second conjunct states the naturality square pointwise:

`e_B (Coinvariants.map (compactInducedMap T) q)
  = compactInducedMap (Coinvariants.map T) (e_A q)`.

Both occurrences of `Coinvariants.map` are the actual Mathlib maps, after
restriction along `N` and `N.subgroupOf H`, respectively. The family is
existentially quantified before both conjuncts; the statement does not choose
unrelated objectwise equivalences.

The only new packaging helper, `normalCoinvariantsMap`, bundles the actual
`Representation.Coinvariants.map` of `Jacquet.restrictMap T N` as an
intertwiner between `rho.toCoinvariants N` and `tau.toCoinvariants N`.
Its equivariance proof uses quotient extensionality and the original
intertwining equation on representatives. It introduces no new quotient or
function model, and proves no bijectivity or exactness claim. No section,
surjectivity, kernel equality, exactness or comparison equivalence is assumed
in the main proposition.

## Original source and scope

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, §5.16 (Case IV₁), printed pages 465–466,
PDF pages 26–27. The entire section, including its reduction diagram and
continuation on page 466, was read and visually checked.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Retained PDF:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- SHA-256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The source has `U = {1}`, `Q = G`, and `V ⊆ M = P`. Its `V` becomes
this statement's `N`, and its `M` becomes `H`. Its character is specialized
to the trivial character, and the present comparison uses unnormalized
coinvariants and unnormalized compact induction throughout.

The mechanism is that the normal subgroup acts trivially on `H \ G`:
for `n ∈ N`, normality gives `g*n*g⁻¹ ∈ N ⊆ H`, hence `H*g*n = H*g`.
The coinvariant compact-section space therefore retains the action of the
locally constant compactly supported scalar functions on this coset space.
In §5.16, the source forms the associated sheaf and computes its fiber at the
identity coset by localization. It moves the coinvariant functor through the
filtered limit of neighborhoods, citing §1.9(g) and §5.11; the resulting fiber
is the coinvariant quotient of the original fiber. Equivariant sheaf
reconstruction from §5.14 then gives the comparison.

Our proposition records the unnormalized trivial-character mechanism on the
same ambient group `G` on both sides. The target's `N`-action is trivial:
normality, containment in `H`, covariance and the trivial
`N.subgroupOf H`-action on `sigma_N` give this directly. The source also uses
a complementary subgroup (called `N` there) and its normalized functors.
Identifying the present target with induction on a chosen complement and
accounting for normalization are separate steps. No complement or splitting
is required here. This is not the full normalized parabolic orbit comparison.
Case IV₂ in §5.17 uses quotient integration and is outside this statement.

The explicit representative formula and all-morphism naturality express the
canonical pointwise quotient operation underlying that localization argument.
The displayed formulation for arbitrary closed `N ≤ H` is the same-ambient
version of the mechanism, rather than a claim that the original prints these
exact quantifiers and notation. The Lean file states its bijectivity; the
localization argument is provenance, not an implemented proof.

## Imported constructions

`Induction.Definitions` supplies the actual compact function space, right
translation, evaluation and postcomposition. `Jacquet.Coinvariants` supplies
restriction of intertwiners, and imports Mathlib's actual coinvariants and
normal-subgroup quotient action. `Category.Basic`, imported by the induction
module, supplies the full smooth category and its underlying intertwiners.
All imported Lean/Markdown pairs are preserved.
