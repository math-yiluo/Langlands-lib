# A separating line bundle on an abelian group scheme over an algebraically closed field

`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement` is a
universe-polymorphic `Prop`-valued definition. This module states the
existence step of Milne's proof of Theorem 7.1 over an algebraically closed
field and supplies no proof.

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`, every
actual `G : Grp (Over (Spec (CommRingCat.of K)))`, and every commutativity
instance `IsCommMonObj G.X`, it asserts

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  ∃ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
    Langlands.AlgebraicGeometry.Picard.SeparatesPointsAndTangents G.X.hom L.
```

The field, the instance `IsAlgClosed K`, the group object, the commutativity
instance and the three geometric hypotheses are exactly the binders and
hypotheses of the published
`Langlands.GroupScheme.AlgebraicallyClosedProjectivityStatement` (module
`Langlands.AbelianScheme.AlgebraicallyClosedProjectivityStatement`). Only the
conclusion differs: an actual line bundle whose complete linear system
separates rational points and tangent vectors replaces the projective
embedding. This module does not import the projectivity statement and is not
its proof.

Worker 899 implemented this pair from the specification of Worker 750, who
also published the projectivity statement whose hypothesis pattern is reused
here.

## The conclusion

`Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left` is the published
full subcategory of locally free rank-one sheaves of modules on the actual
underlying scheme `G.X.left`; `L.obj` is the module sheaf. The line bundle is
existentially quantified. No divisor, chosen space of sections, ampleness or
morphism to projective space is part of the statement.

`SeparatesPointsAndTangents` is imported unchanged from the published module
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`, where its
definitions and conventions are documented; it is not redefined here. For
`p = G.X.hom : G.X.left ⟶ Spec (CommRingCat.of K)` it is the conjunction of
three clauses about all global sections
`s : Langlands.SchemeModule.GlobalSections L.obj`. A section vanishes along a
morphism `f` into `G.X.left` (`VanishesAlong L f s`) when its pullback
`Langlands.SchemeModule.pullbackSection f L.obj s` is zero. A rational point
(`IsRationalPoint p x`) is a morphism `x : Spec K ⟶ G.X.left` with
`x ≫ p = 𝟙`. A nonzero rational tangent vector at `x`
(`IsNonzeroTangentVectorAt p x t`) is a morphism `t : Spec K[ε] ⟶ G.X.left`,
with `K[ε] = DualNumber K`, lying over `Spec K` through the structure map
`π = dualNumberProjection K : Spec K[ε] ⟶ Spec K`, restricting to `x` along
the closed point `ι = dualNumberAugmentation K : Spec K ⟶ Spec K[ε]`
(`ε ↦ 0`), and different from the constant tangent vector `π ≫ x`. These
helper names live in the namespace `Langlands.AlgebraicGeometry.Picard`. The
three clauses, nested to the right, are:

0. base-point freeness: every rational point has a section not vanishing
   along it;
1. separation of points: for distinct rational points `x ≠ y` some section
   vanishes along `x` but not along `y`;
2. separation of tangent vectors: for every rational point `x` and every
   nonzero rational tangent vector `t` at `x`, some section vanishes along `x`
   but not along `t`.

The sections range over the complete linear system `Γ(G.X.left, L)`.

## Original source: Milne, proof of Theorem 7.1, pp.10–11

The original is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic
Geometry* article, author corrected version January 2, 2022. It is
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
retained as
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Printed and one-based PDF page numbers agree. Pages 2–3, 9–11 and 42 were
read directly.

Theorem 7.1, p.10, states: "Every abelian variety is projective." The proof
first assumes that the abelian variety `A` is defined over an algebraically
closed field. It recalls Hartshorne II.7.8.2: a variety is projective if it
has a very ample linear system, and a linear system `𝔡` is very ample if
(p.11)

- (a) it separates points: for every pair `a, b` of distinct closed points
  there is `D ∈ 𝔡` with `a ∈ D` and `b ∉ D`;
- (b) it separates tangent vectors: for every closed point `a` and tangent
  vector `t` at `a` there is `D ∈ 𝔡` with `a ∈ D` and `t ∉ T_a(D)`.

The Hartshorne reference is Milne's citation; Hartshorne is not a registered
source of this pair.

The proof then constructs the linear system (p.11). It chooses finitely many
prime divisors `Z_1, …, Z_n` on `A` through `0` such that

- (a) `⋂ Z_i = {0}`, and
- (b) for every `t ∈ T_0(A)` there is `Z_i` with `t ∉ T_0(Z_i)`.

Their existence follows from two observations: (i) for each closed point
`a ≠ 0` there is a prime divisor through `0` missing `a`, since `0` and `a`
lie in a common open affine; (ii) for each `t ∈ T_0(A)` there is a prime
divisor `Z` through `0` with `t ∉ T_0(Z)`: Milne chooses an open affine
neighbourhood `U` of `0` and a hyperplane `H` through `0` not containing `t`,
and takes `Z` to be the closure of an irreducible component of the hyperplane
section (printed as `A ∩ H`; the affine `U` is the ambient space of `H`).
Let `D = Σ Z_i`.

The theorem of the square (Theorem 6.7, p.10) says
`t_{a+b}^* L ⊗ L ≅ t_a^* L ⊗ t_b^* L` for every invertible sheaf `L` and
`a, b ∈ A(k)`. Milne proves it by applying Corollary 6.5 (p.9) with `f` the
identity and `g`, `h` constant at `a`, `b`. Remark 6.9 (p.10) writes `D_a`
for the translate `t_a D = D + a` and rewrites the theorem as the linear
equivalence `Σ_{i=1}^{m} D_{a_i} ~ m D` whenever `Σ a_i = 0` in `A(k)`
(Remark 6.8 gives the sheaf form). Applied with the three points `a`, `b`,
`-a-b`, it shows

```text
Σ_i (Z_{i,a_i} + Z_{i,b_i} + Z_{i,-a_i-b_i}) ~ Σ_i 3 Z_i = 3D
```

for every family `(a_i, b_i)` of closed points. Each such sum is therefore a
member of the complete linear system `|3D|`, the zero divisor of a global
section of `L(3D)`.

For distinct closed points `a`, `b`, condition (a) gives some `i`, say
`i = 1`, with `b - a ∉ Z_1`. Taking `a_1 = a`, the translate `Z_{1,a_1}`
passes through `a` but not `b`. The `b_1` for which `Z_{1,b_1}` or
`Z_{1,-a_1-b_1}` passes through `b` form proper closed subsets of `A`, so
`b_1` can avoid them; similarly the remaining `a_i`, `b_i` are chosen so that
no translate passes through `b`. Then `a` lies in the support of the member
of `|3D|` displayed above and `b` does not, so `|3D|` separates points.
Milne states that "the proof that it separates tangents is similar"; it uses
condition (b) in the same way. The Lean conclusion asserts the existence of
such a line bundle, of which Milne's `L(3D)` is the intended witness.

### Correspondence with the Lean clauses

The following comparisons explain the formulation and are not proved in
Lean.

- Members of `|3D|` are the zero divisors of the nonzero global sections of
  `L(3D)`, so the clauses quantify over the complete linear system
  `Γ(A, L)` with `L = L(3D)`.
- Over an algebraically closed `K` and for `A` of finite type, the closed
  points of `A` are exactly its `K`-rational points, i.e. the sections
  `x : Spec K ⟶ A` of the structure morphism. A point `a` lies on the zero
  divisor of `s` exactly when `s` vanishes in the fibre `L(a)`, which is the
  vanishing of the pullback of `s` along `x`.
- A tangent vector at `a` is a `K[ε]`-point of `A` over `K` restricting to
  `a`, and the zero tangent vector is the constant one `π ≫ x`. Milne's
  clause (b) is meant for nonzero tangent vectors, since the zero vector lies
  in every tangent space. When `s(a) = 0` and `f` is a local equation of the
  zero divisor `D'` of `s` at `a`, the vector `t` lies in `T_a(D')` exactly
  when `f` vanishes along `t`, i.e. the pullback of `s` along `t` is zero.
- Base-point freeness (clause 0) is not among Milne's conditions (a)–(b).
  When there are at least two rational points it follows from separation of
  points: for a point `b`, pick a point `a ≠ b` and a section vanishing at
  `a` but not at `b`. Milne's genericity argument also gives it directly: for
  a given `a`, the `a_i`, `b_i` can be chosen so that none of the translates
  passes through `a`. It is retained separately because clauses 1–2 are
  vacuous when there is only one rational point (dimension zero).

The formulation through `K`-points and `K[ε]`-points, with the base-point
clause, is therefore derived (internal) provenance; Milne phrases the
conditions through closed points, divisors and tangent spaces.

## From the actual group scheme to Milne's variety convention

The passage is the same as for the published projectivity statement. The
opening definition of Section 20, p.42, calls a group scheme over `S` an
abelian scheme if it is proper and smooth with connected geometric fibres;
for `S = Spec K` this gives the three geometric hypotheses. They are kept in
the parent's form, so `GeometricallyConnected` is not replaced by
connectedness. Mathlib's `GeometricallyConnected` asks for connectedness,
including nonemptiness, after every field-valued base change.

Milne's conventions, pp.2–3, take a scheme over `k` to be of finite type and
a variety over `k` to be a separated scheme of finite type whose base change
to `k̄` is integral. A group variety has multiplication, inverse and a
rational identity `ε ∈ V(k)`; an abelian variety is a complete connected
group variety, and a group variety is automatically nonsingular. Over an
algebraically closed `K`, the base change to the algebraic closure is the
scheme itself up to isomorphism.

Mathematically, the Lean hypotheses give such an abelian variety.
Properness supplies separatedness, finite type and completeness. Smoothness
over the algebraically closed `K` gives regularity, and finite type gives
noetherianity. A connected noetherian regular scheme is integral, because
its irreducible components are disjoint and open. The unit of the actual
group object `G` is a `K`-point, and the group-object axioms in
`Over (Spec K)` give the group laws on points; in particular translation by
a rational point is the published `Langlands.GroupScheme.translation`.
Corollary 2.4, p.3, shows that the group law of an abelian variety is
commutative, so the instance `IsCommMonObj G.X` is retained only to match
the parent statements.

These comparisons explain the source correspondence; this module proves
none of them in Lean. The finite-type, separatedness, nonemptiness and
geometric-integrality clauses are the separate published statement
`Langlands.GroupScheme.FieldAbelianVarietyPresentationStatement` (proof task
`2d28e6bb-86ce-4f1e-8ab2-c7264d1cbef3`, which reuses the
geometric-integrality proof task `13d3f4b1-fadd-43c6-b422-d793dc9adf5f`).
Milne's theorem of the square is the case of the published balanced cube
statement `Langlands.GroupScheme.FieldCubePullbackStatement` with one map the
identity and two constant (proof task
`10d9bd97-8b97-4937-8a1a-3c96c6fb7537`). The present module neither imports
nor assumes any of these statements.

Dimension zero is not excluded. Mathematically, a connected smooth proper
group scheme of dimension zero over an algebraically closed field is
isomorphic to `Spec K`. It has no prime divisors, so Milne's family is empty,
`D = 0` and `L(3D)` is the trivial bundle; its section `1` does not vanish at
the unique rational point, and clauses 1–2 are vacuous because there is only
one rational point and no nonzero tangent vector.

## Errata

The complete [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read in the registered retained original
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`, file
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
The page states that all listed corrections are incorporated into the
xnotes version used here. Its entries are keyed to printed pages 104–145 of
the 1986 article; none concerns the conventions, Section 6 or Theorem 7.1.
No source-specific project errata note exists for either registered source
in the current Library.

## Provenance and scope

The provenance is derived. The existence step of the algebraically closed
case of Milne's Theorem 7.1 is translated through Section 20's group-scheme
presentation and the variety conventions of pp.2–3, and the very-ampleness
conditions are expressed through rational points and dual-number tangent
vectors by the imported predicate. The hypotheses are exactly those of the
published projectivity statement.

The statement covers every universe, every characteristic and dimension
zero. It adds no projectivity, ampleness, polarization, geometric
integrality, finite-type, separatedness, local factoriality, chosen divisor
or comparison certificate as a premise. Its intended proof follows Milne's
divisor route above, through the theorem of the square; it does not use the
ample-existence statements `Langlands.GroupScheme.FieldAmpleExistenceStatement`
or `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`,
which are downstream of projectivity, or any consequence of them.

Together with a very-ampleness criterion (for proper `p` over an
algebraically closed field, `SeparatesPointsAndTangents p L` implies
H-projectivity), this statement is intended to give the published
projectivity statement; that composition is outside this module. After
independent acceptance and publication, a separate exact-target proof must
have this entire named proposition as its type, with no extra outer
hypotheses. This module adds no axiom.
