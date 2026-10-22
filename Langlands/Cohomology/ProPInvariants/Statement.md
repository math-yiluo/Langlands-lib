# Pro-p invariants and finite acyclic resolutions

Author: Worker 3.

This pair constructs one natural transformation and defines three propositions
and their conjunction `Langlands.Cohomology.ProPInvariantTruncationStatements`.
The propositions are two algebraic inputs that Harris 1999, section 2, uses
between Lemma 2.2 and (2.6). They are theorem-statement definitions, not
proofs; no conclusion is supplied as data or as a hypothesis of another
component.

## Construction

`invariantsInclusion R H` is the natural transformation from Mathlib's
`Rep.invariantsFunctor R H` to the forgetful functor
`forget₂ (Rep R H) (ModuleCat R)`. Its component at a representation `A` is the
inclusion `A.ρ.invariants.subtype` of the submodule of `H`-fixed vectors into the
underlying module. Naturality holds because an intertwiner restricted to
invariants is the same linear map; it is proved by extensionality. Applying it
termwise to a cochain complex gives the inclusion of the subcomplex of
invariants.

## The three propositions

All representations are objects of Mathlib's category `Rep R H` of linear
representations of `H` on `R`-modules, with carriers in universe `uV`. The group
universe `uH` and ring universe `uR` are independent. Smoothness is the
published `Langlands.IsSmooth`: every vector is fixed by an open subgroup. No
topology is placed on the representation carriers.

The pro-`p` hypothesis is stated directly. `p` is a prime number, and `H` is a
topological group that is compact and totally disconnected, that is, profinite.
For every open normal subgroup `N`, the finite quotient `H/N` is a `p`-group
(`IsPGroup`). The coefficient ring `R` is commutative, and `p` is a unit in `R`.

| Declaration | Hypotheses and asserted conclusion |
| --- | --- |
| `Langlands.Cohomology.ProPInvariantsExactStatement` | For a short exact sequence of representations of `H` whose three terms are smooth, applying `Rep.invariantsFunctor R H` gives a short exact sequence of `R`-modules. |
| `Langlands.Cohomology.ProPInvariantSubcomplexStatement` | Let `C` be an integer-graded cochain complex of representations with every term smooth, and suppose `H` acts trivially on every cohomology object `C.homology q` (computed in `Rep R H`). Then the termwise inclusion of invariants is a quasi-isomorphism of cochain complexes of `R`-modules. |
| `Langlands.Cohomology.AcyclicResolutionCyclesStatement` | Let `F` be an additive, finite-limit-preserving functor between abelian categories, the source having injective resolutions. Let `K` be a nonnegative cochain complex with a quasi-isomorphic augmentation from `A` in degree zero, all of whose terms are `F`-acyclic. If `R^q F(A) = 0` for every `q > d`, then for every `n >= d` the cycles `K.cycles n` are `F`-acyclic. |

Exactness in the first statement means injectivity, exactness in the middle
and surjectivity. The substantive part is surjectivity on invariants, since
invariants are always left exact. In the third statement, truncating `K`
in degree `n` gives the finite resolution `0 -> A -> K^0 -> ... -> K^(n-1) -> Z^n -> 0`,
where `Z^n = K.cycles n`. Every term of that resolution is then `F`-acyclic.
The statement asks for the vanishing only for the resolved object `A`, not
for every object.

## Original-source correspondence

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.304-305 (PDF pp.6-7):

- Fact 2 is the cohomological-dimension bound `H^q_c(U,T) = 0` for `q > D`.
  Lemma 2.2 bis truncates the acyclic resolutions of Lemma 2.2 in degree
  `D + 1`, obtaining acyclic resolutions of finite length.
  `AcyclicResolutionCyclesStatement` is the general homological statement
  behind this step. Harris's degree `D + 1` satisfies `n >= d` with `d = D`.
  Harris's separate verification of surjectivity for the divisible systems
  `{G^(D+1)_m}` is not asserted here.
- After (2.3), Harris takes an open normal pro-`p` subgroup `H` acting
  trivially on all `H^q_c(U, Z/l^m)` and argues: since `p` is prime to `l`,
  the functor `H^0(H, -)` is exact on `l`-primary torsion modules, hence the
  inclusion `G^._m(U)^H -> G^._m(U)` is a quasi-isomorphism.
  `ProPInvariantsExactStatement` and `ProPInvariantSubcomplexStatement` are
  these two assertions. Harris's coefficients are `Z/l^m`, in which `p` is a
  unit.

Serre, *Galois Cohomology*, English translation, Springer 1997 (corrected
second printing 2002), Chapter I, supplies the group-cohomological input:

| Location | Content used |
| --- | --- |
| 1.4, p.6 | A pro-`p` group is a profinite group that is a projective limit of `p`-groups; equivalently, its order is a power of `p`. |
| 2.1, p.10 | Discrete `G`-modules are those in which every element has an open stabilizer. This is the published smoothness predicate. |
| 2.2, Proposition 8 and Corollaries 1-3, p.11 | `H^q(G,A)` is the inductive limit of `H^q(G/U, A^U)` over open normal `U`. These are the derived functors of `A -> A^G`, and are torsion for `q >= 1`. |
| 2.4, Proposition 9, p.12 | `Cor o Res = n` for a subgroup of index `n`, so the kernel of restriction is killed by `n`. With the trivial subgroup of a finite group of order `n`, the cohomology in positive degree is killed by `n`. |
| 3.1, Proposition 11, p.17, and 3.3, Proposition 14 Corollary 2, p.19 | `cd_l(G) = 0` exactly when the order of `G` is prime to `l`. So for a pro-`p` group and `l != p`, `H^1(G,A) = 0` for every discrete `l`-primary torsion module, and invariants are exact on such modules. |

The Lean hypotheses are a derived generalization of Serre's torsion-module
statement. They replace `l`-primary torsion by modules over a ring in which `p`
is a unit. Both Harris's `Z/l^m` coefficients and Serre's `l`-primary torsion
groups, which are uniquely `p`-divisible, are of this kind. The same
argument applies: higher cohomology is a colimit of finite `p`-group
cohomology, which is killed by a power of `p`. The pro-`p` hypothesis is
written as the `p`-group property of every finite quotient `H/N` by an open
normal subgroup. For a compact group, those quotients are finite and cofinal,
so this is Serre's projective-limit definition.

The third statement is the standard dimension-shifting fact for the short
exact sequences `0 -> Z^i -> K^i -> Z^(i+1) -> 0` of cycles of a resolution.
Grothendieck uses these sequences in the proof of Lemme 3.3.1, Tohoku 1957
p.158, together with the long exact sequence of derived functors. Here
`R^q F(Z^n)` is identified with `R^(q+n) F(A)` for `q >= 1`. The Lean
statement records the resulting vanishing as a conclusion; the identification
is not stated separately.

## Scope

No statement is made about a particular geometric complex. The compactly
supported cohomology of Harris's analytic spaces, the existence of an open
normal pro-`p` subgroup acting trivially, Berkovich's cohomological-dimension
bound, and the divisible-system surjectivity remain separate obligations. The
equivariant section complexes they apply to also remain separate. No banality
hypothesis is used. Characteristic-zero coefficients are allowed whenever `p`
is invertible.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, pp.302-306, read in full.
- `serre-1997-galois-cohomology`, Central-Library file
  `Serre--Galois cohomology (book)--1997.pdf`, SHA-256
  `343aafc5fe7ebb6605effc6f6e09338f622bb977325e8cdd166152cbd6eb7cf2`. Chapter I,
  sections 1.4, 2.1-2.4 and 3.1-3.3 (pp.6, 10-12, 16-19; PDF pp.14, 18-20,
  24-27) were read in the embedded text layer.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`,
  Tohoku 1957, SHA-256
  `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  p.158 (PDF p.40) was read visually.

## Formal dependencies and checks

The only project import is the published `Langlands.Representation.Smooth.Definitions`.
At Library commit `68e8013fc4fed0de284fd849695676aca2e0c32d` it has Lean SHA-256
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` and
Markdown SHA-256
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`, equal to the
workspace bytes. The Mathlib imports provide `Rep`, its abelian structure and
forgetful functor, `Rep.invariantsFunctor`, `OpenNormalSubgroup`, `IsPGroup`,
quasi-isomorphisms, short exact sequences and right derived functors. The
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

Development check `8dcd8057-a7cf-4d0e-bbd8-8b643460871b` built this module with
no errors or warnings. It inspected
`Langlands.Cohomology.ProPInvariantTruncationStatements` as a definition
returning `Prop`, with universe parameters `uH uR uV u v u' v'` and only the
axioms `propext`, `Classical.choice` and `Quot.sound`. Check
`39f36fa0-3d28-4ac2-b94c-7323c1991080` printed the natural transformation,
the three components and the conjunction with universe annotations, and the
output was read. The prints show:

- `invariantsInclusion` has component `Submodule.subtype` of
  `Representation.invariants` at every representation;
- the pro-`p` statements quantify over the topological group `H` with the
  compactness and total-disconnectedness instances, and assume `IsPGroup p`
  for every quotient by an open normal subgroup;
- smoothness is `Langlands.IsSmooth` on each term;
- the trivial-action hypothesis is stated on `HomologicalComplex.homology`
  in `Rep R H`, and the conclusion is `QuasiIso` of the termwise inclusion;
- the cycles statement assumes vanishing of `rightDerived F q` at `A` only for
  `d < q`, and concludes vanishing of `rightDerived F (q + 1)` at
  `HomologicalComplex.cycles K n` for every `n` with `d <= n`.

Compilation and inspection establish well-formed statements; they do not prove
any of the three assertions.
