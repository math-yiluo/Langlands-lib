# Statement: the trivial locus of a homomorphism into a separated group is closed

Worker 738.

`Langlands.GroupScheme.MultiplicativeTypeTrivialLocusClosedStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- Mathlib's `AlgebraicGeometry.Morphisms.Separated`, for `IsSeparated`.

It uses the notation of the Library statement
[`MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md),
whose clause 3 (Corollaire 5.3) contains the same set.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X`. The
scoped notation of `CategoryTheory.MonObj` is open, so for every `S`-scheme `T` the set of
morphisms `T ⟶ G.X` carries the group structure induced by the group law of `G`, and `1`
is its unit: the composite of the structure morphism `T → S` with the unit section of `G`.

## Objects and predicates used

- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre
  `u_s : H_s ⟶ G_s` of `u` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map u`.
- **Trivial homomorphism.** For a homomorphism `f`, `f.hom.hom = 1` says that `f` is the
  unit homomorphism: its underlying morphism is the unit of the group of morphisms, so every
  point of the source maps to the unit. Thus `u_s.hom.hom = 1` says that `u_s` is trivial.
- `IsSeparated G.X.hom` says that the structure morphism `G → S` is separated.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` over
  each member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian
  group `Λ`. In particular `H` is of finite type over `S`, as SGA 3 assumes.
- `IsClosed` is closedness of a subset of the underlying topological space of `S`.

## Statement and quantifiers

For every scheme `S : Scheme.{u}`, every `S`-group `H` of multiplicative type, every
`S`-group `G` that is separated over `S` and every homomorphism `u : H ⟶ G`, the set
`{s ∈ S | u_s is trivial}` is closed in `S`.

There is no hypothesis that `S` is locally noetherian or that `G` is of finite
presentation over `S`.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`).

- Corollaire 5.3, recomposed p.49 (page 19 of the PDF, margin 60): "Soient u, H, G, comme
  dans 5.2, supposons de plus G séparé sur S. Soit U l'ensemble des s ∈ S tels que u_s
  soit l'homomorphisme unité. Alors U est une partie ouverte et fermée de S, et
  u_U : H_U → G_U est l'homomorphisme unité." Corollaire 5.2 (same page) assumes "H de
  type multiplicatif et de type fini, et S localement noethérien ou G de présentation
  finie sur S".
- The proof of Corollaire 5.3, recomposed p.50 (page 20 of the PDF): "Il reste à prouver
  seulement que U est fermé. Or soit K = Ker(u), comme G est séparé sur S, K est un
  sous-préschéma fermé de H, et U est l'ensemble des s ∈ S tels que K_s = H_s. On voit
  alors facilement que U est fermé, par exemple comme application de VIII 6.4 (H étant
  essentiellement libre sur S d'après VIII 6.3), ou en notant qu'on peut supposer S
  réduit et U dense dans S, donc schématiquement dense dans S, ce qui implique H_U
  schématiquement dense dans H puisque H est plat sur S, et comme u et l'homomorphisme
  unité coïncident sur H_U, ils coïncident sur H." The editors' note (31) on this
  sentence adds "et de présentation finie sur S, cf. EGA IV₃, 11.10.5 (ii) et 11.9.10
  (ii)".

## Derivation from the source

This is the closedness half of Corollaire 5.3, the part of its proof quoted above, stated
as a separate assertion.

- **The set.** "L'ensemble des s ∈ S tels que u_s soit l'homomorphisme unité" is
  `{s : S | u_s.hom.hom = 1}`, with the same Lean expression as in clause 3 of the Library
  statement of Théorème 5.1.
- **Hypotheses.** The source states Corollaire 5.3 under the hypotheses of Corollaire 5.2:
  `S` locally noetherian or `G` of finite presentation. Those hypotheses serve the openness
  half, which comes from Corollaire 5.2. The first closedness argument in the source uses
  only that `G` is separated (so that `K = Ker(u)` is a closed subscheme of `H`) and that
  `H` is essentially free over `S` (VIII 6.3). It does not use either alternative
  hypothesis, so this statement omits them. The second argument, by schematic density,
  needs `H` of finite presentation, which holds for groups of multiplicative type.
- **Why the statement holds without them (explanation only, not formalized here).**
  Being closed can be checked after pulling back along an fppf cover, because flat
  morphisms locally of finite presentation are open. Triviality of `u_s` is unchanged by
  extension of the residue field. So one may assume `S = Spec R` affine and `H = D(Λ)`,
  with `H = Spec R[Λ]`. Since `G` is separated, its unit section is a closed immersion, so
  `Ker(u)` is a closed subscheme `V(I)` of `Spec R[Λ]`. Because `R[Λ]` is free over `R`
  on the basis `Λ`, `u_s` is trivial exactly when every coefficient of every element of
  `I` lies in the prime ideal of `s`. That is an intersection of closed sets.

## Scope

All schemes are in universe `u`. Only closedness of the trivial locus is stated, not its
openness nor the triviality of `u` over it. It is meant as one step of the proof of clause 3
of the Library statement `Langlands.GroupScheme.MultiplicativeTypeCentralRigidityStatement`,
whose other steps (openness and triviality over the locus) come from Corollaire 5.2.
