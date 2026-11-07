# Conditional generic irreducibility on actual unramified characters

`Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`
is a Prop-valued target for the existence of a nonempty open set of
unramified parameters at which actual normalized parabolic induction is
irreducible. It is stated for an irreducible square-integrable inducing
representation. This module does not prove this representation-theoretic
target.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Proposition IV.2.2(i), printed p.284 / PDF p.50, asserts irreducibility
for square-integrable, G-regular inducing representations. Its proof on
printed p.285 uses unitarity, semisimplicity, Corollary III.7.3 and Frobenius
reciprocity. The beginning of IV.3 on that same page states that the
irreducible-induction locus in the complex unramified orbit is nonempty
and Zariski open, and says that the square-integrable case follows from
IV.2.2. The present target is an adapted, weaker character-space open-locus
consequence of those passages. It does not state the full IV.2.2, its
intertwiner regularity or invertibility assertion, or an identification
of a character space with an algebraic orbit.

## Actual groups, split center and parameters

The field `F : Type u` is any nonarchimedean local field, with the existing
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. `G` is a connected reductive group
scheme over `Spec F`, without a splitness, quasi-splitness or
characteristic restriction. Its affineness and smoothness are taken from
`IsConnectedReductive`. `G(F)` has the canonical
`rationalPointTopology F G.X` and the proved topological-group structure.
Local compactness, `NonarchimedeanGroup` and Hausdorffness of this actual
point group remain explicit structural premises.

The supplied maps are `p : P → G`, `l : M → P`, `a : A → M` and
`n : U → P`, with `A` a commutative group scheme and `M` affine.
The existing `ParabolicRootPresentation p l a` supplies its full
compatibility data: actual rational parabolic and Levi, maximal split
central component of `M`, ambient maximal split torus, generic
cocharacter, simple-root subset, standard image equalities, factorization,
minimality and a cocharacter realizing the parabolic and Levi images.
The supplied `n` satisfies `LeviSubgroup.IsGeometricUnipotentRadical`.
The target does not assert existence of these presentations or radicals.

At the identity test `Spec F`, `Ppt` is the value of `range p`, `Mpt` is
the literal `parabolicLeviPointSubgroup p l`, and `Upt` is the value of
`range (n ≫ p)`. The target quantifies an actual semidirect decomposition
`h` of these subgroups, closedness of `Ppt` and `Upt`, and continuity of
the actual Levi projection `h.projection`. Their subgroup topologies are
inherited from the canonical topology on `G(F)`.

The quotient subgroup is exactly

```text
C = range(parabolicSplitComponentPointHom r : A(F) → Mpt).
```

Thus square-integrability is tested on the actual `Mpt / A(F)` quotient,
not on a quotient by a freely chosen central subgroup. The point map is
the existing canonical homeomorphism `M(F) ≃ₜ* Mpt` composed with
`a(F)`. The helper
`parabolicSplitComponentPointHom_range_le_center` proves `C ≤ Z(Mpt)`:
take an actual image element, lift any other Levi element through that
homeomorphism, use centrality of `a` from the split-component predicate,
and map its commutation equality through the homeomorphism. Normality of
`C` then follows from `Subgroup.normal_of_le_center`. Neither centrality
nor normality is a new structural premise.

The Borel measurable structure on the quotient and a Haar measure `qMeasure` on
it are explicit inputs. `π : SmoothRep.{0,u,uV} ℂ Mpt` is the canonical
smooth object, with independent carrier universe `uV`. The two
representation hypotheses are `π.IsIrreducible` and
`IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure`.
Irreducibility includes nonzeroness and does not mean finite dimension.
The square-integrability predicate requires admissibility, a unitary
character of the full abstract center, and membership in `L²(qMeasure)` of the
norm of every smooth-dual matrix coefficient. The quotient itself uses
the actual split component specified above. No separate finite-length,
temperedness or induced-irreducibility premise is supplied.

The parameter space is the existing `unramifiedCharacters ν` for
`ν = parabolicLeviRationalNormCharacters r`, indexed by **all** rational
characters of the specified Levi scheme. These are their actual norm
characters transported to `Mpt` by the canonical homeomorphism. The
common norm kernel and existing continuous-character topology are
retained; the parameter space is the full complex unramified-character
space and is not restricted to its unitary subgroup.

## Conclusion and consumer boundary

The target concludes the existence of a set `D` in this full character
space such that `IsOpen D`, `D.Nonempty`, and for every `χ ∈ D`,

```text
(UnramifiedLeviInduction h hU ν χ π).IsIrreducible.
```

`UnramifiedLeviInduction` is the existing actual smooth induction of
`π.twist χ`, with the positive Levi Haar half-modulus and right translation
on the ambient group. It is exactly the induction model used by the
continued-intertwiner scalar construction. No placeholder action or
replacement category is introduced. The statement uses that source
normalization directly; it adds no radical-unimodularity assumption to
identify it with the separate full-parabolic normalization.

`IsOpen` here is the existing topology on continuous unramified
characters. The conclusion is deliberately weaker than a Zariski-open
locus on an algebraic isomorphism-class orbit. In particular it supplies
no orbit descent, saturation, maximality of `D`, density assertion,
regularity of standard intertwiners, or irreducibility at every unitary
parameter. Such irreducibility would be false in general. Once proved,
the target supplies the local irreducibility premise used by scalar
continuation, after transporting parameters through
`parabolicLeviUnramifiedCharactersHomeomorph`. The independent open-set
density results used there still require their own displayed actual
rational-character hypotheses. Ambient separability required by Schur is
also separate.

Generic irreducibility is a representation-theoretic proof obligation,
never an external Chapter V structural fact. The source route through
III.7.3, unitarity and Frobenius reciprocity remains to be proved and
connected to these models. This statement and its elementary centrality
helper do not close IV.2.2, IV.3, standard-integral convergence or
rationality, global j or mu, or any Plancherel completion condition.
