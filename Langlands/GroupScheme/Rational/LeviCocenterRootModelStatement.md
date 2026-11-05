# Root models for actual Levi cocenters

Author: Worker 1282.

This module gives a derived geometric prerequisite for the fundamental-weight
proof of inducedness of a simply connected group's split-torus-centralizer
cocenter. It defines the prerequisite and proves naturality of the actual
character pullback. It does not prove existence of the root model.

The construction is intended for general connected reductive groups; it neither
assumes simple connectedness nor asserts integral coroot generation.

## Actual restriction and descent data

`characterLattice.baseChangePullback k E g` is the integral linear map
`X*(Q_E) → X*(T_E)` given by precomposition with the actual base change of a
commutative-group homomorphism `g : T → Q`. The theorem
`baseChangePullback_galois` proves that it commutes with the already defined
ordinary Galois actions, by the published `galoisRepresentation_precompose`.

For a supplied actual root datum `P` on `X*(T_E)` and `X_*(T_E)`, a root base `B`
and a subset `s` of its simple-root indices, `CocenterRootDescentData` asserts:

- the actual pullback is injective, with image exactly the characters whose
  pairings with the `s`-indexed simple coroots vanish;
- for each `σ ∈ Aut_k(E)`, there are integral linear correction maps `w_σ` on
  characters and `v_σ` on cocharacters, and a permutation `e_σ` of all simple
  indices;
- `w_σ` fixes the entire actual pullback image;
- the twisted maps `w_σ ∘ σ` and `v_σ ∘ σ` preserve the root-datum pairing,
  carry each simple coroot to the one indexed by `e_σ`, and preserve `s`.

Neither correction map is required to satisfy a group law, and the predicate
does not require them to be supplied as actual Weyl-group elements. It records
the consequences of the Weyl corrections needed for lattice descent. It does
not itself supply a basis of either lattice.

## The geometric existence statement

`SplitTorusCentralizerCocenterRootModelStatement.{u}` concerns every connected
reductive `G` over every field `k : Type u`, every split subtorus `a : A → G`,
every representative `j : M → G` of its centralizer, every actual derived
subgroup `d : D → M`, and every commutative fppf quotient `q : M → Q` by its
range. Connected reductivity of `M` and the torus property of `Q` are explicit
premises. Thus proving this prerequisite does not also require constructing the
centralizer or its cocenter, or discharging their structural properties.

The output is a maximal `k`-torus `t : T → M`, a finite Galois extension `E/k`
with `E : Type u` splitting both `T` and `Q`, and a finite reduced actual root
datum `P` for the base change of `t ≫ j`. The statement explicitly requires that
this base-changed torus be maximal in `G_E`. It also supplies `B` and `s` with
`CocenterRootDescentData` for the actual composite `T → M → Q`. In particular
the character map in the conclusion is fixed by the supplied group morphisms.

## Provenance and proposed geometric route

This is a derived packaging of standard Levi and based-root descent arguments,
not a numbered theorem transcribed verbatim from a source.

Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, states in 25.25, printed p.550 (zero-based PDF
index 565), that a split-subtorus centralizer is a Levi subgroup of a parabolic.
Section 25.c, printed pp.551–552 (PDF indices 566–567), describes the correction
of the ordinary Galois action by Weyl elements to preserve a chosen root base.
That discussion uses a maximal split torus. Applying the same Borel-restoration
argument to the parabolic with the present Levi is a further derived step.

The geometric argument required here is to choose a maximal torus of `M` and,
over a separable closure, a Borel of `G` inside that parabolic containing the
torus. The Levi simple coroots cut out the characters of the actual cocenter.
This character identification is an additional quotient/root-group argument,
not a conclusion quoted from 25.c. The parabolic is defined over `k`, so the
Weyl corrections restoring its Borels lie in the Levi Weyl group. They act
trivially on cocenter characters. They preserve the pairing and permute the
simple coroots, preserving the Levi subset. Descent to a sufficiently large
finite Galois splitting extension yields precisely the witnesses stated here.
All these existence and comparison steps remain proof obligations.

The full official 2017 author errata snapshot, registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, was checked. Its correction to
25.24 restricts that paragraph's final maximal-split-central-torus assertion to
minimal parabolics; the unrestricted final sentence of 25.24 is not used here.
It does not change 25.25 or the based-root construction on pp.551–552.

The consumer is the general argument recorded in the Markdown of
`SplitTorusCentralizerCocenterStatement`. Once integral coroot generation for
simply connected groups is supplied separately, the simple coroots form a
basis, their dual fundamental weights outside `s` model the cocenter lattice,
and the correction laws give a permuted basis. None of those conclusions is
claimed as a theorem in this statement module.
