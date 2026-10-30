# Exactness and comparisons of the equivariant Godement complex

Author: Worker 3.

This module defines three propositions and their conjunction
`Langlands.Cohomology.EquivariantGodementStatements`. They concern the
equivariant Godement construction that Worker 61 published in
`Langlands.Sheaf.Equivariant.Godement.Zero` and
`Langlands.Sheaf.Equivariant.Godement.Complex`. That construction is an
equivariant lift of the ordinary-topological Godement construction, for a
discrete group. It is an analogue of the resolution `F(T)` that Harris 1999
takes from Berkovich's manuscript, not Berkovich's construction itself: see
"Original-source correspondence" and "Scope". The propositions are
theorem-statement definitions, not proofs. Exactness, the comparison
isomorphism and the computation of derived functors are conclusions; none is
supplied as data or as a hypothesis of another component.

## Objects

All components quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` acts on `X` by
`MulAction`, and each element acts continuously (`ContinuousConstSMul`), so
it acts by a homeomorphism. `G` carries no topology. The published abelian
structure on equivariant module sheaves is stated with `G` in the universe
of `X` and `R`, so `G` shares the universe `u` here. The objects are the
published ones:

- `Langlands.Sheaf.Equivariant.TopologicalSheaf G X (ModuleCat R)` is the
  category of equivariant sheaves of `R`-modules, with the abelian structure
  and enough injectives of `Langlands.Sheaf.Equivariant.Abelian`.
- `toSheaf G X (ModuleCat R)` forgets the group transport and gives an
  ordinary module sheaf on `TopCat.of X`.
- `Sheaf.Equivariant.Godement.zeroFunctor R G X` sends `F` to the
  equivariant sheaf whose sections over an open `U` are all families
  `(s_x)_{x ∈ U}` with `s_x` in the stalk `F_x`. No continuity is imposed. The
  group acts through the published stalk transport maps.
  `Sheaf.Equivariant.Godement.coaugmentation R G X` sends a section to its
  family of germs. The published instance `mono_coaugmentation` makes it a
  monomorphism, and the published instance `zeroFunctor_additive` makes
  `zeroFunctor` additive.
- `Sheaf.Equivariant.Godement.complexFunctor R G X` is Worker 61's
  equivariant Godement complex: the published iterated-cokernel construction
  `CokernelComplex.functor` applied to `zeroFunctor` and `coaugmentation`.
  Degree `n + 1` is `zeroFunctor` applied to the cokernel of the previous
  differential. This is the cokernel recursion of SGA 4 XVII 4.2.2, which
  Berkovich's (b) also uses, applied here to Worker 61's degree-zero functor.
- `Sheaf.Godement.complexFunctor (Flasque.spacePoints (TopCat.of X)) (ModuleCat R)`
  is the published ordinary Godement complex, built from the points of the
  open-set site, one for each point of `X`. `Sheaf.Godement.augmentation` is
  its coaugmentation in degree zero.
- `sectionRepresentation R G X` and `CompactSections.functor R G X` take
  global sections and compactly supported global sections, with their
  `G`-action, as objects of Mathlib's `Rep R G`. Their additivity instances
  are published in `Langlands.Cohomology.EquivariantSections`.

The module also declares two auxiliary items in the namespace
`Langlands.Cohomology.EquivariantGodement`:

- the instance `toSheaf_additive`, which says that `toSheaf` is additive. Its
  proof is `rfl`: morphisms of equivariant sheaves are added on each open,
  and `toSheaf` keeps the same components. The instance is needed to apply
  `toSheaf` to cochain complexes with `Functor.mapHomologicalComplex`;
- `augmentationMap R G X F`, an abbreviation for the published augmentation
  chain map `CokernelComplex.augmentationMap` from `F`, placed in degree
  zero, to Worker 61's complex `(complexFunctor R G X).obj F`.

## The three propositions

| Declaration | Asserted conclusion |
| --- | --- |
| `EquivariantGodementZeroExactStatement` | `zeroFunctor R G X` preserves finite limits and finite colimits. Its additivity is the published instance `zeroFunctor_additive` and is not restated. |
| `EquivariantGodementUnderlyingStatement` | There is a natural isomorphism `e` between two functors to cochain complexes of ordinary module sheaves on `TopCat.of X`: `complexFunctor R G X` followed by `toSheaf` applied termwise, and `toSheaf` followed by the ordinary Godement complex. For every `F`, `toSheaf` of the equivariant coaugmentation at `F`, followed by the degree-zero component of `e` at `F`, equals the ordinary Godement augmentation of `toSheaf F`. |
| `EquivariantGodementComputesSectionsStatement` | Let `I` be an injective resolution of `F` in the equivariant sheaf category and `φ` a chain map from the equivariant Godement complex of `F` to `I.cocomplex` with `augmentationMap ≫ φ = I.ι`. Then, for every `n`, the map induced by `φ` on the `n`-th cohomology of `sectionRepresentation` of the complexes, followed by the inverse of Mathlib's `isoRightDerivedObj`, is an isomorphism onto `(sectionRepresentation R G X).rightDerived n` at `F`. The same holds for `CompactSections.functor R G X`. |

`EquivariantGodementStatements` is the conjunction of the three, in this
order.

The comparison map in the third component is any chain map under the two
augmentations. Such a map exists because `I.cocomplex` consists of injective
objects, and any two such maps are homotopic. The statement therefore does
not depend on a choice. The pattern is that of the published
`GodementComputesCohomologyStatement` in `Langlands.Cohomology.Flasque`.
The two right-derived functors are, by definition, Worker 13's published
`globalDerived R G X n` and `compactDerived R G X n`, and the two inverses
are its `globalDerivedIso` and `compactDerivedIso`, all in
`Langlands.Cohomology.EquivariantDerivedSections`. This module does not
import that file; it uses Mathlib's `rightDerived` and `isoRightDerivedObj`
directly.

## Consequences that are not restated

Several properties of the construction follow from these components and from
published statements. They are not separate components:

- The equivariant Godement complex resolves `F`. Apply the published
  `CokernelResolutionStatement` (SGA 4 XVII 4.2.2; Tohoku 2.5, Example (a))
  to `zeroFunctor` and `coaugmentation`, using `mono_coaugmentation`. Then
  `augmentationMap R G X F` is a quasi-isomorphism. The print check below
  compiles this deduction.
- Every residual and term functor of the complex is additive and exact. This
  follows from the first component, the published instance
  `zeroFunctor_additive` and the published
  `CokernelResolutionFunctorExactnessStatement`. This is the analogue, for
  the present construction, of Berkovich's (ii) and, in degree zero, of
  Harris's Fact 3.
- The underlying ordinary sheaf of every term is flasque. This follows from
  the second component and the published `GodementTermFlasqueStatement`,
  since flasqueness is invariant under isomorphism. This is the analogue of
  Berkovich's (i).
- The fibre of the complex at a point of `X` is a split resolution of the
  stalk. This follows from the second component and the published
  `ModuleFiberSplitResolutionStatement`. This is the analogue of Berkovich's
  (iii).
- Harris's Fact 4 requires that the `F(T_m)` again form an `ℓ`-divisible
  system. For the present construction, the exactness part of the analogous
  property follows from exactness of the term functors.
  An exact additive functor carries the sequences (2.1) to exact sequences.
  It also carries the kernel of multiplication by `ℓ^m'` to the kernel of
  multiplication by `ℓ^m'`. The freeness of `F(T_m)` over `ℤ/ℓ^m ℤ` uses the
  explicit description of the stalks and is not addressed here.

## Original-source correspondence

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318, section 2, printed p.304 (PDF
p.6). There a compact open subgroup `S(ẽ)` of `G_J` stabilizes an analytic
space `U(ẽ)`, in Harris's notation. He cites Berkovich [B4], Proposition
1.4.1, for an acyclic resolution of a finite `ℓ`-torsion sheaf on `U(ẽ)` by
smooth `S(ẽ)`-modules, "a smooth `G`-equivariant version of the Godement
flasque resolution". For an étale sheaf `T` in smooth `ℤ/ℓ^m ℤ[S(ẽ)]`-modules
over `U(ẽ)`, Berkovich constructs an embedding `T → F(T)`, where `F(T)` is
again such a sheaf "which is acyclic for the functor `RΓ_c`", and Harris
displays `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` for `q > 0`. This is cohomology with
compact support. In Harris's notation, `U(ẽ)_{F̄}` is `U(ẽ)` after
extension of scalars from the `p`-adic field `F` to `F̄`; the present module has no analogue of this base change, since it works over an
ordinary topological space. The acyclicity that Harris displays on this page
is for compact supports only. The construction is functorial in `T`. Harris
lists Fact 3, that `T ↦ F(T)` is exact, and Fact 4, on `ℓ`-divisible
systems. He notes that `F` is the composite of two exact functors, `ν_*ν^*`
and `b^*`.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript, §1.5, PDF p.10. Berkovich recalls the Godement
resolution of SGA 4 XVII §4.2 on the étale site of `X(G)`. A surjection
`I → X` from a discrete set, with chosen geometric points, gives a morphism
of sites `ν : Top(I) → X(G)_ét`. Then (a) `C^0(F) = ν_*ν^*(F)` with the
adjunction morphism, and (b) `C^(m+1)(F) = C^0(Coker d^(m-1))`. By SGA 4 XVII
4.2.3: (i) `C^m(F)` is flabby; (ii) `F ↦ C^m(F)` is exact; (iii) the fibre
of `C^·(F)` at a point is a canonically split resolution of `F_x`.
Proposition 1.5.1 follows on PDF p.10: for every `m ≥ 0`, `b^*(C^m(F))` is
a soft sheaf on `X_ét`. Here `b : X → X(G)` is the morphism of Example
1.1.3, PDF p.3, with `X = X({1})`, so `b^*` is the inverse image along `b`,
from sheaves on `X(G)` to sheaves on `X`, not a direct image. By Theorem
1.4.2, PDF p.8, this inverse image identifies étale sheaves on `X(G)` with
`G`-sheaves on `X`. Corollary 1.5.2(i), the compactly supported comparison,
follows on PDF pp.11-12: there are canonical isomorphisms
`H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`, in Berkovich's notation, the action of `G` on `H^q_c(X, b^*F)` is
discrete, and there is a spectral sequence
`H^p(G, H^q_c(X, b^*F)) ⇒ H^(p+q)_c(X(G), F)`.

Berkovich's `C^0(F) = ν_*ν^*(F)` is formed on the equivariant topos, so it
contains coinduction factors. Observation (a) in the proof of Proposition
1.5.1, PDF p.10, shows this: after restriction from `G` to an open subgroup
`N` with coset representatives `J`, the index set `I` becomes `I × J`,
indexed by `G/N`. Worker 61's `zeroFunctor` has no such factors. Take `X`
a single point, `I` a singleton, `G` of order two and `M` a module. After
restriction to the trivial subgroup, Berkovich's `C^0(M)` has underlying
module `Map(G, M) ≅ M²`. Worker 61's `zeroFunctor` returns `M`. The two
degree-zero objects therefore differ after forgetting the group action. So
the Lean components do not formalize Berkovich's construction. They are
statements about Worker 61's ordinary-topological construction, which is
modelled on the same method. In the table below, Berkovich's and Harris's
statements are the motivating originals, and each Lean component states
the analogue for the present construction. Only SGA 4 XVII 4.2.2 and
Tohoku 3.3 describe the ordinary Godement complex that the second
component compares with.

| Source | Original statement | Lean component (analogue for Worker 61's construction) |
| --- | --- | --- |
| Harris p.304, Fact 3; Berkovich §1.5 (ii); SGA 4 XVII 4.2.3(ii), pp.326-327 | `T ↦ F(T)` is exact (Harris); `F ↦ C^m(F)` is exact (Berkovich, SGA 4). | `EquivariantGodementZeroExactStatement`: exactness of `zeroFunctor` |
| SGA 4 XVII 4.2.2, p.326; Tohoku 3.3, p.160 | The ordinary Godement resolution: `C^0` is the product of the skyscraper sheaves of the stalks at all points, and later terms come from cokernels. | `EquivariantGodementUnderlyingStatement`: after forgetting the group action, the present complex is the ordinary Godement complex (a derived comparison, see below) |
| Harris p.304, `RΓ_c`-acyclicity of `F(T)`; Berkovich Cor. 1.5.2(i), PDF pp.11-12 | `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` for `q > 0` (Harris); `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`, with a discrete `G`-action on the right side (Berkovich). | `EquivariantGodementComputesSectionsStatement`, compactly supported part, for `CompactSections.functor` |
| Tohoku 3.3, p.160, and Chapter V, pp.200-201 | The Godement terms are flasque, hence acyclic for sections, and the derived functors of `Γ_X` with values in `G`-modules are the `H^q(X, A)`. | `EquivariantGodementComputesSectionsStatement`, ordinary part, for `sectionRepresentation` |

The second component is a derived formulation, not a printed theorem. It
concerns Worker 61's construction and the ordinary Godement construction
only; it says nothing about Berkovich's `ν_*ν^*`, whose underlying object is
different (see the example above). In Worker 61's construction, the
sections of `zeroFunctor F` over an open `U` are all families of stalk
elements at the points of `U`. So its underlying sheaf is the product of
the skyscraper sheaves of the stalks. This is the degree-zero term of the
ordinary Godement complex of SGA 4 XVII 4.2.2 and of Tohoku p.160,
Résolution de l'identité. Worker 61 publishes the degree-zero
identification as `skyscraperProductIso` in
`Langlands.Sheaf.Equivariant.Godement.SkyscraperProduct`. The component
extends it to the whole complex, naturally in `F`, and fixes it in degree
zero by the two augmentations. It is the formal statement that Worker 61's
equivariant construction lifts the ordinary one, and it is the route by
which the published ordinary Godement statements apply to it.

The third component has two parts with different sources. The compactly
supported part is the analogue of the conclusion that Harris uses: Harris
states that `F(T)` is acyclic for `RΓ_c`, so the resolution computes
compactly supported cohomology. Berkovich's Corollary 1.5.2(i) is the
compactly supported comparison for his construction. The ordinary part is
not taken from Harris, whose displayed acyclicity on p.304 is for compact
supports. It is a separate assertion with an independent source: Tohoku p.160
shows that the Godement terms are flasque and hence acyclic for `Γ_X`, and
Tohoku Chapter V, pp.200-201, identifies the derived functors of `Γ_X`,
viewed as a functor to `G`-modules, with the `H^q(X, A)`. In both parts the
target functors are the `Rep`-valued section representations, not ordinary
sections, so the statement records the cohomology together with its group action. These
derived-functor comparisons are published as
`EquivariantSectionsDerivedStatement` and
`EquivariantCompactSectionsDerivedStatement` in
`Langlands.Cohomology.OperatorSpace.Statement`.

## Scope

- The constructions are ordinary-topological, for a discrete group acting by
  homeomorphisms. That is Berkovich's case of a discrete group in §1.4, p.7.
  The analytic étale site, Berkovich's `X(G)`, and the Shimura and Drinfeld
  spaces of Harris are not formalized here.
- Worker 61's construction is not Berkovich's `ν_*ν^*` on the equivariant
  topos. It introduces no coinduction from the trivial subgroup. Its terms
  therefore need not be acyclic for the invariant sections `Γ(X(G), -)`. For
  a one-point space, `zeroFunctor` returns the given representation `M`. The
  complex is `M` in degree zero and zero above, so it computes `M^G` and no
  higher group cohomology; for `G = ℤ` acting trivially on `M = R` with `R`
  a nonzero ring (for example `R = ℤ`), the group cohomology
  `H^1(ℤ, R) ≅ R` is nonzero. (For the zero ring it vanishes; the
  propositions themselves allow any commutative ring.) For this reason the third
  component uses only the `Rep`-valued section functors, whose derived
  functors do not involve invariants.
- Smooth actions of locally profinite groups are excluded. The `G`-action on
  a product of stalks over infinitely many points need not be smooth even
  when `F` is. Taking the smooth part is only left exact in general, so it
  does not repair exactness. Harris's `F(T)` lives in smooth modules because
  Berkovich works on the equivariant étale site.
- Softness (Berkovich Proposition 1.5.1) and the boundedness and truncation
  of Harris Lemma 2.2 bis are not stated here. Truncation is treated in the
  published `Langlands.Cohomology.ProPInvariants.Statement`.
- The third component asserts isomorphisms in each degree. Compatibility
  with connecting morphisms is not asserted.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, printed p.304 (PDF p.6). The text layer was read, and the
  `RΓ_c` phrase and the display `H_c^q(U(ẽ)_{F̄}, F(T)) = 0` were checked
  visually on the rendered scan, since the text layer drops the support
  subscript.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  Example 1.1.3, PDF p.3; §1.4, PDF pp.7-8, including Theorem 1.4.2; §1.5
  through Corollary 1.5.2, PDF pp.10-12, including observation (a) in the
  proof of Proposition 1.5.1. Read in the text layer. The text layer prints
  upper and lower stars alike, so the positions of the star glyphs in
  `ν_*ν^*` (PDF p.10), `b^*(C^m(F))` in Proposition 1.5.1 (PDF p.10) and
  `b^*F` in Corollary 1.5.2(i) (PDF pp.11-12) were read from the PDF's glyph
  coordinates. In `ν_*ν^*` the first star is lowered and the second raised;
  every star after `b` is raised, as in a superscript.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305 (1973), SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`;
  XVII 4.2.2-4.2.3, printed pp.326-328 (PDF pp.329-331), read visually.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, Tohoku 1957, SHA-256
  `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  section 2.5, p.150, section 3.3, pp.159-160, and Chapter V, pp.200-201.

## Formal dependencies and checks

Direct project imports, byte-identical to Library commit
`354dfade2c499262492d6db74cb58fd887ffed5f`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Sheaf.Equivariant.Abelian` | Worker 61 | `5563a66fd43002b53d67a9ec67c4779421e2469b41ced6ab3d0db9130694dca2` | `ffed98c41011abb6cb078c9a98d08dbadf5ca1d99c36a52a475a65d4cc3906d4` |
| `Langlands.Sheaf.Equivariant.Godement.Complex` | Worker 61 | `4f9e21799f79e18f0eedfaae69184a622197de95e5c2164f27d7ce7489d28a0b` | `3d099f98905ea647c03b7535ed2e1cda4fc3691bcb255f27954670032c23f3be` |
| `Langlands.Sheaf.Godement.ExactnessStatement` | Worker 3 | `66c45b9d460fce4935aa869c1db1c932ca9e60fe95188ea3a6895ae9d0037435` | `d9776b5f0107c1f34b83b8a03fee2ba25a3e6904faa288eb51512bd951b0f4b5` |
| `Langlands.Cohomology.Flasque.Statement` | Worker 3 | `f77b9ee83d596f111d88a9f682d8b00a7058667b354411020276988a4e0fdd08` | `5b07c1a1d517cd07067e78633f1124bd2848125db8e804e441cab463dd56cd1a` |
| `Langlands.Cohomology.EquivariantSections` | Worker 13 | `cae0603b98a431090323db9c16832b4ad881dd5c8cd0fa85519a814a4f90ade9` | `4589d4e9294bdfdcf64ffd90806fd875039ab5fe9c615c72b6b0d795998e03ea` |

`Langlands.Sheaf.Equivariant.Godement.Complex` brings Worker 61's
`Langlands.Sheaf.Equivariant.Godement.Zero` (Lean SHA-256
`949bb276bdb18d78d8d79ad504a38774de399c63fdb9416128f23da11740641f`).
`Langlands.Sheaf.Godement.ExactnessStatement` brings the published
`CokernelComplex` and ordinary Godement modules. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Workspace check `4ba9d7d0-ff56-478a-9d7a-4e711509c208` built this module
with Lake, with no errors or warnings, and inspected the conjunction as a
`Prop`-valued definition with the single universe parameter `u`, depending
only on `propext`, `Classical.choice` and `Quot.sound`. Check
`38027bf4-228a-41d6-814d-b9e3a1cf1583` printed the auxiliary declarations,
Worker 61's `complexFunctor`, the three components and the conjunction with
universe annotations, and the output was read. The same check compiled three
examples. The first shows that the conjunction unfolds to the three
components by `rfl`. The second derives the quasi-isomorphism of
`augmentationMap` from `CokernelResolutionStatement` and
`mono_coaugmentation`. The third finds Worker 61's additivity instance for
`zeroFunctor` by instance search. The prints show:

- the exactness component uses Mathlib's `PreservesFiniteLimits` and
  `PreservesFiniteColimits` of `zeroFunctor`;
- the comparison component asserts existence of an `Iso` of functors into
  `CochainComplex (TopCat.Sheaf (ModuleCat R) (TopCat.of X)) ℕ`, from
  Worker 61's `complexFunctor` followed by `toSheaf`, with the degree-zero
  equation against `Sheaf.Godement.augmentation` at
  `Flasque.spacePoints (TopCat.of X)`;
- the section component quantifies over every `InjectiveResolution` and every
  chain map from Worker 61's complex under the augmentations, and concludes
  `IsIso` for both section functors in every degree.

Compilation and inspection establish well-formed statements; they do not
prove any of the three assertions.
