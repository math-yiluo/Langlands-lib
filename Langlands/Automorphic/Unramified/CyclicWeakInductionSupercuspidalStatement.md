# Supercuspidality at a nonsplit place of cyclic weak induction

`Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement`
is an unproved, derived global input for the prime-degree branch of Harris's
Proposition 4.8. It uses actual cuspidal realizations, their genuine local
spectral presentations, arithmetic Galois transport, and the published weak
induction relation.

For a cyclic prime-degree number-field extension `E/F`, choose a generator
`σ` of its actual automorphism group. Let `v` be a finite place of `F` with
exactly one place `w` of `E` above it. Let `T` be a cuspidal realization over
`E` with unitary central character, and `P` an actual spectral presentation
of `T`. Suppose:

- `P.localComponent w` is supercuspidal;
- for every `0 < i < [E:F]`, there are an actual realization `U` and a
  spectral presentation `Q` such that `U` is the arithmetic conjugate of
  `T` by `σ^i`, `Q.localComponent w` is supercuspidal, and it is not
  smoothly isomorphic to `P.localComponent w`.

Then any actual cuspidal realization `S` over `F` that is weakly
automorphically induced from `T` has a supercuspidal component at `v`.
The rank equation `[rank S] = [E:F] [rank T]` is already part of the weak
induction relation. Here ranks are positive: the Lean indices `r` and `m`
mean ranks `r+1` and `m+1`.

## Source and derivation

G. Henniart and R. Herb, *Automorphic induction for GL(n) (over local
non-archimedean fields)*, Duke Math. J. 78 (1995), 131–192, Proposition 5.5,
printed pp.152–153, proves the following local result. If a supercuspidal
representation `τ` has Galois stabilizer of order `d₁`, its `κ`-lift is
normalized parabolic induction of the `d₁` indicated determinant twists
of a supercuspidal representation. In particular, stabilizer order one
makes the lift supercuspidal. The theorem concerns the local `κ`-lift;
it does not by itself identify the local component of a supplied global
weak induction with that lift.
The printed pages are physical PDF pages 22–23, indices 21–22 when
counting from zero.

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, proof of Proposition 4.8,
printed p.203, applies precisely this local criterion to the automorphic
induction in the non-singleton branch. The present declaration isolates
the global consequence of that application. The original local theorem
and Harris's application, rather than a separately assumed local
Langlands correspondence, are its provenance.

Its eventual proof retains all of these obligations:

1. The unique-place hypothesis identifies the decomposition group with
   `Gal(E/F)` and gives a cyclic extension `E_w/F_v` of full degree.
2. Arithmetic transport of actual global realizations transports the
   local component at this fixed place by the induced completion
   automorphism. The proof must identify the supercuspidal local factors
   of `P` and `Q` with the irreducible local components of their containing
   global realizations. Both local factors are explicitly supercuspidal,
   hence irreducible and admissible. A reducible multiple of the conjugate
   cannot witness the displayed condition. After this comparison, the
   unequal irreducible local classes give trivial local Galois
   stabilizer. Existence of the displayed conjugates and supercuspidal
   factors is a premise; their comparison with local arithmetic transport
   remains a proof obligation.
3. The global automorphic induction used by Harris has local component
   at `v` equal to the Henniart–Herb `κ`-lift. Global/local matching,
   including its normalizations, remains a proof obligation.
4. A supplied cuspidal weak induction has the same unramified parameters
   as that global induction and is identified with it by strong
   multiplicity one. The local criterion then gives a genuine
   supercuspidal spectral presentation downstairs. Neither rigidity nor
   existence of global induction is proved by this declaration.

The assumption on local conjugates is explicit. Nonisomorphism of global
conjugates alone would not assert the needed nonisomorphism at `w`.
The use of the inverse arithmetic-conjugacy convention does not change
the condition, since the nontrivial powers of the generator are closed
under inversion.

The statement has independent field universes `uF,uE` and local-factor
universes `uV,uW`. Compactness of the two adele quotients is the explicit
parameter required by the existing cuspidal APIs. It adds no `n < p`
condition and makes no claim about ramified local–global compatibility
of Galois representations. It is a proposition definition, not a proof.
