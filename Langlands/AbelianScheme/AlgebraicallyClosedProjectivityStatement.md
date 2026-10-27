# Projectivity of abelian group schemes over an algebraically closed field

`Langlands.GroupScheme.AlgebraicallyClosedProjectivityStatement` is a
universe-polymorphic `Prop`-valued definition. This module states the
projectivity result and supplies no proof.

For every field `K : Type u` with `IsAlgClosed K`, every actual
`G : Grp (Over (Spec (CommRingCat.of K)))`, and every commutativity instance
`IsCommMonObj G.X`, it asserts

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  Langlands.AlgebraicGeometry.IsHProjective G.X.hom.
```

The field, the instance `IsAlgClosed K`, the group object, the commutativity
instance and the three geometric hypotheses are exactly those of the
published `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`.
Equivalently, they are the binders of the published arbitrary-field
`Langlands.GroupScheme.FieldAmpleExistenceStatement` with algebraic closure
as the only added restriction. Only the conclusion differs: an actual
projective embedding replaces an ample line bundle. The module imports
neither ample-existence statement and is not their proof.

Worker 750 implemented this pair. The hypothesis pattern adapts the published
ample-existence statements by Workers 420 and 299. Worker 404 supplied the
focused specification and coordinates the downstream ample-existence
assembly.

## The H-projectivity predicate

The conclusion uses the published `IsHProjective` from
`Langlands.AlgebraicGeometry.ProjectiveSpace` unchanged. For
`p = G.X.hom : G.X.left ⟶ Spec (CommRingCat.of K)` it unfolds
definitionally to

```text
∃ (n : ℕ) (i : G.X.left ⟶ ProjectiveSpace K n),
  IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec K n = G.X.hom.
```

A private development check confirmed this unfolding by `Iff.rfl`. It also
confirmed that the binders above, followed by `IsHProjective G.X.hom`, are
definitionally the named proposition.

`ProjectiveSpace K n` is the actual scheme
`Proj (projectiveSpaceGrading K n)`. Here the grading is the total-degree
grading of `MvPolynomial (Fin (n + 1)) K`, with every coordinate in degree
one. `projectiveSpaceToSpec K n` is Mathlib's `Proj.toSpecZero`, followed by
`Spec.map` of the constants homomorphism `K → (degree-zero part)`. The
embedding `i` is a scheme morphism into this Proj. `IsClosedImmersion i` is
Mathlib's actual closed-immersion predicate. The equality makes `i` a
morphism over `Spec K`. The dimension `n` is an arbitrary natural number,
so `n = 0` is permitted. No abstract projective model, comparison
certificate or line bundle is a parameter.

The source of this convention is the registered original
`stacks-projective-space-twists-morphisms-2026-10-26`, directory SHA256
`e21fdf382a193a228965d8a018149e752c04561e3a229faae7ead34fda0d85c5`,
retained in
`literature/Stacks Project - Projective space, twists and projective morphisms (HTML snapshot 2026-10-26)`.
Its `01W7.html` (Section 29.44, tag 01W7), SHA256
`5b54ea82a89cf7fe2ea3bf0527ccec5522a48386d983ba7ca06498ecbde59dc6`,
was read directly. [Definition 29.44.1(2), tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
calls `f : X → S` H-projective if there is an integer `n` and a closed
immersion `X → P^n_S` over `S`. Clause (1) instead allows a closed
subscheme of a projective bundle `P(E)` of a quasi-coherent finite type
module. Lemma 29.44.3 (tag 01W9) shows that H-projective implies
projective. Over an affine base, the proof of Lemma 29.44.4 (tag 01WB)
embeds `P(E)` in some `P^n` by a closed immersion. So over `Spec K` the two clauses agree mathematically.
The Lean statement uses only clause (2). It asserts no comparison with
clause (1), and none with Stacks' base-change model of `P^n` from `P^n_Z`.
The construction comparison is recorded in the `ProjectiveSpace` pair.

## Original source: Milne's Theorem 7.1 over an algebraically closed field

The original is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic
Geometry* article, author corrected version January 2, 2022. It is
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
and retained as
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is the
original. Printed and one-based PDF page numbers agree. Pages 2–3, 10–12
and 42 were read directly.

Theorem 7.1, p.10, states: "Every abelian variety is projective." Its proof
begins: "We first prove this under the assumption that the abelian variety
`A` is defined over an algebraically closed field." The proof recalls
Hartshorne II.7.8.2: a variety is projective if it has a very ample linear
system, meaning one that separates points and tangent vectors. On pp.10–11
it chooses finitely many prime divisors `Z_i` through `0`. Their intersection
is `{0}`, and together they separate tangent vectors at `0`. Using the
theorem of the square (6.7, 6.9), it shows that `|3D|`, for `D = Σ Z_i`, is
very ample. This algebraically closed part of the proof is the statement
formalized here.

The Hartshorne reference is Milne's citation; Hartshorne is not a
registered source of this pair. Mathematically, a very ample linear system
on a complete variety over `K` defines a closed embedding over `K` into
`P^n_K`. Here `n` is the dimension of the linear system, which is finite
because the variety is complete. So Milne's projectivity over `K` is the
existence of some `n` and a closed immersion into `P^n_K` over `K`, as in
clause (2) above. The Lean conclusion asks for existence only; it does not
require the particular system `|3D|` or any particular dimension.

## Distinction from the arbitrary-field theorem

On pp.11–12, the final step of the proof passes from `A_{k̄}` to `A` over an
arbitrary ground field `k`. Steps (a)–(d) construct an ample divisor on `A`
from one over a finite extension. Step (c) sums Galois conjugates over a
finite Galois extension. Step (d) uses a characteristic-power multiple over
a finite purely inseparable extension. That descent is not part of the
present statement. The present proposition is restricted by `IsAlgClosed K`.
It does not state projectivity, or ample existence, over a general field.
It is a strictly weaker intermediate target than the arbitrary-field
projectivity theorem, which would drop that instance.

Within the project, this statement supplies the geometric part of the
algebraically closed input to the ample-existence workflow coordinated by
Worker 404. The published `AlgebraicallyClosedFieldAmpleExistenceStatement`
and `FieldAmpleExistenceStatement` are downstream of projectivity in that
route. The same holds for the symmetric statement
`FieldSymmetricAmpleExistenceStatement`, which follows Corollary 7.2, p.12.
None of them is available as a proof of the present prerequisite.

## From the actual group scheme to Milne's variety convention

The opening definition of Section 20, p.42, calls a group scheme over `S` an
abelian scheme if it is proper and smooth with connected geometric fibres.
In the presence of the first condition, this is equivalent to the fibres
being abelian varieties. For `S = Spec K` this gives the three geometric
hypotheses of the Lean statement. They are kept in the parent's form, so
`GeometricallyConnected` is not replaced by connectedness even though `K`
is algebraically closed. Mathlib's `GeometricallyConnected` asks for
connectedness after every field-valued base change, and connectedness
includes nonemptiness.

Milne's conventions, pp.2–3, take a variety over `k` to be a separated
scheme of finite type whose base change to `k̄` is integral. A group variety
has multiplication, inverse and a rational identity `ε ∈ V(k)`. An abelian
variety is a complete connected group variety, and a group variety is
automatically nonsingular. Over an algebraically closed `K`, the base change
to the algebraic closure is the scheme itself up to isomorphism.

Mathematically, the Lean hypotheses give such an abelian variety.
Properness supplies separatedness, finite type and completeness. Smoothness
over the algebraically closed `K` gives regularity, and finite type gives
noetherianity. A connected noetherian regular scheme is integral, because
its irreducible components are disjoint and open. The unit of the actual
group object `G` is a `K`-point. The group-object axioms in
`Over (Spec K)` give the group laws on points. Corollary 2.4, p.3, shows
that the group law of an abelian variety is commutative. The instance
`IsCommMonObj G.X` is retained only to match the parent statements.

These comparisons explain the source correspondence; this module proves
none of them in Lean. The local finite type, quasi-compactness,
separatedness, nonemptiness and geometric-integrality clauses are the
separate published statement
`Langlands.GroupScheme.FieldAbelianVarietyPresentationStatement`, with exact
proof task `2d28e6bb-86ce-4f1e-8ab2-c7264d1cbef3`. That task reuses the
geometric-integrality proof task `13d3f4b1-fadd-43c6-b422-d793dc9adf5f`. The
present module neither imports nor assumes that presentation statement.

Dimension zero is not excluded. Mathematically, a connected smooth proper
group scheme of dimension zero over an algebraically closed field is
isomorphic to `Spec K`. Then `P^0_K`, the Proj of `K[X_0]`, is also
isomorphic to `Spec K`. So the allowed value `n = 0` covers this case
without a separate hypothesis.

## Errata

The complete [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read in the registered retained original
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`, file
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
The page states that all listed corrections are incorporated into the
xnotes version used here. Its entries are keyed to the printed pages
104–145 of the 1986 article. Its imperfect-field correction concerns
Proposition 12.1. The two printed-p.145 entries correct Corollary 19.4 and
its proof, which precede Section 20. No listed entry concerns Theorem 7.1,
the conventions or Section 20. No source-specific project errata note
exists for either registered source in the current Library.

## Provenance and scope

The provenance is derived. The algebraically closed case of Milne's
Theorem 7.1 is translated through Section 20's group-scheme presentation
and the variety conventions of pp.2–3. Projectivity is expressed as the
published H-projectivity of Stacks Definition 29.44.1(2), over the
Library's actual polynomial-Proj projective space. The hypotheses are those
of the published arbitrary-field ample-existence statement plus
`IsAlgClosed K`.

The statement covers every universe, every characteristic and dimension
zero. Its only restriction beyond the arbitrary-field hypotheses is
algebraic closure. It adds no projectivity, ample sheaf, polarization,
geometric-integrality, finite-type, separatedness or supplied comparison
premise. An eventual proof must derive such geometric inputs from the
given hypotheses.

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. Substantial missing geometric prerequisites belong in focused
definition, statement and proof tasks, in that order. The existing
source-presentation and geometric-integrality owners are to be reused
rather than duplicated. Worker 404 retains coordination of the actual
twisting sheaf, the ampleness comparison and the final arbitrary-field
assembly. This module adds no axiom and discharges none of those proof
obligations.
