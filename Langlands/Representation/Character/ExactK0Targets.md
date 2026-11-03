# Actual character additivity, finite-family independence and exact K₀ targets

Author: Worker 184.

This module defines four propositions in `Langlands.Character`. It proves none
of them. They use the published actual distribution character and actual exact
Grothendieck group throughout. No supporting definition, class function or
replacement quotient is introduced.

## Common setting and universes

Each target quantifies over a group `G : Type uG` with continuous multiplication
and inversion, Hausdorff locally compact totally disconnected topology, its
Borel measurable structure, and an explicit regular left Haar measure `μ`.
`μ.IsHaarMeasure` includes left invariance, finiteness on compact sets and positive
mass on every nonempty open set; the zero measure is excluded. `μ.Regular`
records regularity separately. No right invariance or unimodularity is assumed.
These are the Library's locally profinite hypotheses for an l-group.

All objects are actual bundled smooth complex representations. Their carriers
have complex vector-space structures without a carrier topology or a
finite-dimensionality assumption. `SmoothRep.IsAdmissible` is the published
predicate on the actual action; it includes smoothness and finite-dimensional
fixed vectors for every open subgroup. `HasFiniteLength` means finite length
over the group algebra `ℂ[G]`.

The complete declarations are closed proposition definitions: the group,
instances, measure, representations and maps are quantified in their bodies.
`DistributionShortExactAdditivityStatement.{uG,uA,uB,uC}` has three independently
sized carriers. Each of the other three declarations has universes `.{uG,uV}`.
In particular `uV` is independent of `uG`; it is never replaced by `max uG uV`.
The dependent carrier `(A i)` of a family member can vary with `i` within
`Type uV`.

For every admissible action `ρ`, `distribution μ ρ hρ` is the actual finite-rank
trace of its integrated action on locally constant compactly supported test
functions. It is an element of `HarmonicAnalysis.Distribution G`, the complex
algebraic dual of `SchwartzBruhat G`. Neither an abstract assigned character nor
ordinary ambient trace on an infinite-dimensional space occurs here.

## The four target declarations

`DistributionShortExactAdditivityStatement` quantifies actual smooth objects
`A`, `B`, `C`, their admissibility proofs and actual equivariant linear maps
`f : A.representation.IntertwiningMap B.representation` and
`g : B.representation.IntertwiningMap C.representation`. Its sole remaining
premise is the published `SmoothRep.IsShortExact f g`: `f` is injective, `g` is
surjective and the range of `f` equals the kernel of `g`. Its conclusion is

\[
  \Theta_{B,\mu}=\Theta_{A,\mu}+\Theta_{C,\mu}.
\]

It covers nonsplit sequences; no splitting, finite-length condition or finite
dimension of the carriers is assumed.

`FiniteFamilyLinearIndependenceStatement` quantifies `r : ℕ`, a family
`A : Fin r → SmoothRep.{0,uG,uV} ℂ G` and admissibility of every member. It
requires irreducibility of every member and

```
Pairwise (fun i j =>
  ¬ Nonempty ((A i).representation.Equiv (A j).representation))
```

Here `Representation.Equiv` is a genuine equivariant complex linear
equivalence. For distinct indices, such an equivalence must be absent; this is
not merely a requirement that their carriers or actions differ. The conclusion
is `LinearIndependent ℂ (fun i => distribution μ (A i).representation (hA i))`.
It states independence over all complex coefficients, including the empty
family case. It asserts no finite-length admissibility theorem.

`ExactK0CharacterRealizationStatement` explicitly quantifies the premise

```
hAdm : ∀ (A : SmoothRep.{0,uG,uV} ℂ G),
  A.HasFiniteLength → A.IsAdmissible
```

and asserts existence of a unique integer-linear map

```
χ : SmoothRep.FiniteLengthGrothendieckGroup.{0,uG,uV} ℂ G →ₗ[ℤ]
  HarmonicAnalysis.Distribution G
```

satisfying, for every actual object `A` and every `hA : A.HasFiniteLength`,

```
χ (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
  distribution μ A.representation (hAdm A hA).
```

The domain is the published quotient of the free integral module on genuine
finite-length isomorphism classes by the integral span of `[B] - [A] - [C]`
for all actual short exact sequences at this carrier universe. In particular,
all nonsplit relations are imposed. Neither the carrier nor its label type is
resized. The codomain uses its canonical integer module structure as an
abelian group. Uniqueness is among all integer-linear maps with every displayed
generator value.

`ExactK0CharacterInjectivityStatement` quantifies the same `hAdm` and every
integer-linear map `χ` of that exact type. Assuming the same formula for every
actual finite-length object, it concludes `Function.Injective χ` on the entire
exact quotient. The premise prescribes all generator values directly; there
is no assumption of injectivity on irreducibles, linear independence of their
characters, existence of a preferred map, or an inverse. This target is useful
even when a consumer supplies the map by another construction.

## Original source and derived provenance

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Representations of the group GL(n,F) where F is a non-Archimedean local field*,
Russian Mathematical Surveys 31:3 (1976), 1–68. Source ID:
`bernstein-zelevinsky-1976-representations-gln`; content SHA256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The readable original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
Worker 184 read and visually checked printed/PDF p.21 for this target family.
No source-specific errata note was present in the supplied Library or workspace.

Section 2.17 defines the character by the finite-rank trace of the integrated
action after choosing a left Haar measure. Proposition 2.19 states independence
of the characters of any finite family of pairwise inequivalent irreducible
admissible representations of an l-group. Thus the independence target is a
source-backed statement in its general l-group scope, despite the paper's
GL(n,F) title. Its printed proof chooses one compact open subgroup whose fixed
spaces are all nonzero, applies the corner correspondence of 2.10 to obtain
pairwise inequivalent irreducible finite-dimensional corner representations,
and invokes finite-dimensional character independence. Corollary 2.20 on the
same page is only the two-representation equivalence criterion. The published
`Langlands.characterSeparation` proves that criterion; it does not discharge
the stronger finite-family target here.

The additivity and exact-K₀ targets are derived mathematical interfaces. The
page cited above does not explicitly construct this exact-K₀ quotient or state
these three declarations. Their intended proof dependencies are:

1. **Exact trace additivity.** The actual integrated actions commute with the
   supplied intertwiners. An exact trace-additivity argument for their
   finite-rank operators, or for their finite-dimensional compact-open fixed
   spaces, should prove the short-exact character identity. A fixed-space route
   also needs exactness of fixed vectors, including surjectivity on the quotient,
   via compact-open averaging. Pointwise equality on all actual test functions
   then gives equality of distributions. The available
   `distribution_eq_subspace` and `distribution_eq_fixedVectors` provide the
   character-to-finite-stage comparisons. These dependencies remain proof
   obligations, not hypotheses silently added to the target.
2. **The actual exact quotient's universal property.** Under `hAdm`,
   `distribution_eq_of_equivariant` supplies well-defined character values on
   genuine finite-length isomorphism classes. Short-exact additivity supplies
   `FiniteLengthGrothendieckGroup.IsExactAdditive`. The published `lift` and
   `existsUnique_lift_iff` descend those values through all exact relations;
   `hom_ext_object` gives uniqueness from all actual generator values. This is
   the intended route to realization.
3. **Finite-family independence and the published irreducible realization.**
   `SmoothRep.irreducibleGrothendieckStatement` from
   `Langlands.Representation.Smooth.IrreducibleGrothendieckProof` already proves
   bijectivity of `realizeIrreducibles` onto this exact quotient, at independent
   group and carrier universes. An element therefore has a finite integral
   expansion in genuine irreducible labels. Actual irreducibles have finite
   length, so `hAdm` makes representatives admissible. The generator formula for
   `χ` and finite-family independence force every coefficient of a kernel
   element to vanish, using the injective embedding of integers into `ℂ`.
   Bijectivity of the published realization then gives injectivity on the
   whole quotient. This is the intended route to the fourth target.

The module imports only the character construction, the exact quotient and
Mathlib's linear-independence definitions. The proof dependencies just listed
are a plan for proof successors, not proofs imported to establish these
propositions. This target publication leaves their truth to those successors.

## Consumer boundary

These generic targets support actual general reductive exact-K₀ comparisons.
They do not prove finite-length admissibility for an ambient reductive group or
its Levi. The explicit `hAdm` is the interface to those separately owned actual
proofs; it does not authorize an extra hypothesis in the final rational Aubert
theorem. No induction or Jacquet finite-length result, Levi conjugacy,
classification, geometric lemma or induction-character comparison is supplied.
The existing character, exact-K₀ and irreducible-realization pairs and their
imports are preserved.
