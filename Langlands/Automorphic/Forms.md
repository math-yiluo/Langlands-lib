# Automorphic forms and finite adelic translation

For a number field `K : Type u` and every natural rank `n`, this module assembles
actual complex automorphic forms on `GL_n(A_K)` from the published function
spaces. Rank zero is included. The carrier consists of continuous complex
functions invariant under rational left translation; its infinite slices are
real `C∞` functions and its finite slices are locally constant. These properties
are inherited from `SmoothRationalFunctions`, with the existing completion and
restricted-product topologies.

`IsAutomorphicForm K n f` imposes four additional conditions:

1. One compact open subgroup of the finite adelic group fixes the whole function.
2. The right translates by `standardInfiniteCompact K n` span a finite-dimensional
   complex vector space of functions.
3. The entire family of infinite slices has one finite-dimensional orbit under
   the genuine complex enveloping-center differential action.
4. Each fixed finite slice has polynomial growth in the actual archimedean
   matrix and inverse height. The constant and exponent may depend on that slice.

The standard infinite subgroup is the published product of real orthogonal and
complex unitary factors, transported to the actual infinite adelic group. Its
compact maximality is proved in `ArchimedeanCompactMaximalityProof`. The finite
compact open subgroup used below is the actual standard integral matrix subgroup;
its compactness is proved in `FiniteAdelicGL.StandardIntegralCompact`.

## Construction and proved identifications

`hasFiniteLevel_iff_mem_finiteSmooth` removes the supplied-compact-subgroup
parameter from the earlier smoothness comparison. A compact finite level is an
open stabilizer. Conversely, the earlier intersection construction intersects any
open stabilizer with the now proved compact open standard integral subgroup.

`automorphicSubrepresentation` is an actual subrepresentation of finite adelic
right translation on `FiniteSmoothRationalFunctions`. Its submodule is the
intersection of the simultaneous center-finite submodule and the inverse image
of the compact-finite and growth submodules. The three published preservation
lemmas prove closure under finite translation. In particular, center finiteness
uses a common condition on all slices, rather than separate finiteness for each
slice. `mem_automorphicSubrepresentation` identifies membership with
`IsAutomorphicForm` after the injective inclusion in the smooth ambient space.
`isAutomorphicForm_iff_exists_finiteSmooth` proves that every smooth function
satisfying that predicate has this concrete realization; finite level supplies
the common open stabilizer.

`AutomorphicForms` is this submodule's carrier. `automorphicFiniteRightAction`
is its inherited complex-linear representation of `FiniteAdelicGL K n`.
The existing open stabilizer of each function proves that this representation
is smooth. `automorphicFiniteSmoothInclusion` is an injective intertwiner into
the finite-smooth representation. `automorphicToContinuous` is the injective
linear realization in the actual continuous rational-invariant functions.
The action formula is exactly

\[
 (R(d)f)(x)=f(x\,\operatorname{ofFinite}(d)).
\]

`isAutomorphicForm_iff_source_conditions` expands the two less explicit
conditions. It requires one ideal `I` in the actual enveloping center with finite
complex quotient, annihilating every infinite slice. The bound becomes

\[
 \forall b\in GL_n(A_{K,f}),\quad
 \exists C\ge0,\ \exists d\in\mathbb N,\quad
 \forall a\in GL_n(K_\infty),\quad
 |f(a,b)|\le C\,h(a)^d,
\]

where `h` is the published Hilbert norm of the scalar-augmented standard plus
inverse-adjoint representation. The proof uses the published common-ideal
criterion and the proved matrix/Hilbert growth equivalence. Zero constants and
zero exponents are allowed; the Hilbert norm is at least one, so the existential
growth condition also permits positive exponents as in the source.

## Source correspondence and scope

The original source is A. Borel and H. Jacquet, *Automorphic forms and automorphic
representations*, Corvallis Part I (1979). Section 4.1, printed p.194
(one-based PDF page 189), specifies joint continuity and slice smoothness.
Section 4.2, printed pp.194–195 (PDF pages 189–190), specifies rational invariance,
a simple Hecke element fixing the function, one finite-codimensional center
ideal, and growth separately on each finite slice. The paragraph after 4.2
authorizes taking the finite Hecke element to be a compact-open averaging
idempotent. Section 3.2, printed p.194 (PDF page 189), identifies its fixing
condition with finite-level invariance. Section 1.5(1), printed p.190 (PDF page
185), gives the equivalent compact-finite formulation used here. The norm
convention comes from section 1.2, printed pp.189–190 (PDF pages 184–185), via
the already published Hilbert norm and growth comparison.

Thus the definition implements this equivalent compact-finite formulation of
the source conditions. Lean proves the concrete submodule and finite action
constructions and the expanded common-ideal/Hilbert-growth criterion. It does
not formalize equivalence with Hecke idempotents. The construction is derived
from the cited definition and published ingredients, not an assumed automorphic
existence or classification theorem. Cuspidality, specified central characters,
differential preservation of this complete space, and the full Hecke or
`(g,K)` representation category are further constructions. No full infinite-group
action on compact-finite forms is asserted.

Registered source: `borel-jacquet-1979-automorphic`.
Original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
