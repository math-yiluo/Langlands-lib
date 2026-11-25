# Statement: canonical factorization of homomorphisms from groups of multiplicative type

`Langlands.GroupScheme.MultiplicativeTypeKernelFactorizationStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, `SubgroupFunctor.range`;
- [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md), for the scheme-theoretic
  kernel `GroupScheme.kernel u` and its inclusion `GroupScheme.kernelι u`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X` and
underlying morphism of schemes `u.hom.hom.left`. `q ≫ v` is composition of homomorphisms.

## Objects and predicates used

- **Kernel.** `kernel u : GroupScheme S` is the pullback of `u` along the unit section of
  `G`, with its induced group structure, and `kernelι u : kernel u ⟶ H` is the inclusion.
  Its `T`-points are the `x ∈ H(T)` with `u(x) = 1` (`kernelPointsEquiv`). This is
  `Ker u` of SGA 3.
- **Quotient map.** `RelativeRoot.IsFppfQuotient N q`, for a subgroup functor `N` of `H`
  and a homomorphism `q : H ⟶ Q`, says that the underlying morphism of `q` is flat,
  surjective and locally of finite presentation, and that the kernel of `q` has the same
  points as `N` on every test scheme (`SubgroupFunctor.range (kernelι q) = N`). Then `Q`
  represents the fppf sheaf quotient `H/N`, and `q` is the canonical map `H → H/N`. Here
  `N = SubgroupFunctor.range (kernelι u)` is the subgroup functor of `H` given by
  `Ker u`, so `Q` is `H/Ker u`.
- **Faithfully flat and affine.** Flatness and surjectivity of `q` (faithful flatness) are
  part of `IsFppfQuotient`. `IsAffineHom q.hom.hom.left` says that `q` is an affine
  morphism.
- **Monomorphism.** `Mono v.hom.hom` says that the underlying morphism of `v : Q ⟶ G` is a
  monomorphism; a morphism in `Over S` is a monomorphism exactly when its underlying
  morphism of schemes is one.
- `IsLocallyNoetherian S` is Mathlib's predicate. `IsSeparated G.X.hom`,
  `LocallyOfFinitePresentation G.X.hom`, `QuasiCompact G.X.hom` and
  `QuasiSeparated G.X.hom` are the corresponding properties of the structure morphism
  `G → S`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.

## Statement and quantifiers

For every scheme `S : Scheme.{u}`, all `S`-groups `H, G` and every homomorphism
`u : H ⟶ G` such that `H` is of multiplicative type, `G` is separated over `S`, and `S` is
locally noetherian or `G` is of finite presentation over `S`
(`LocallyOfFinitePresentation ∧ QuasiCompact ∧ QuasiSeparated` for `G → S`):

- the kernel `kernel u` is of multiplicative type; and
- there exist an `S`-group `Q` and homomorphisms `q : H ⟶ Q`, `v : Q ⟶ G` such that `Q` is
  of multiplicative type, `q` is an fppf quotient map with kernel `Ker u`, `q` is affine,
  `v` is a monomorphism and `q ≫ v = u`.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Théorème 6.8, p.55 (margin 67): "Soit u : H → G un homomorphisme de S-préschémas en
  groupes, avec H de type multiplicatif et de type fini, et G séparé sur S. On suppose de
  plus S localement noethérien ou G de présentation finie sur S. Alors K = Ker(u) est un
  sous-groupe de type multiplicatif et de type fini de H, et u se factorise en
  H → H/K → G (maps u′, u″), où H/K est de type multiplicatif et de type fini, u′ est
  l'homomorphisme canonique et est fidèlement plat (et affine), et u″ est un
  monomorphisme."

SGA 3 notes that it suffices to prove that `K` is of multiplicative type, the rest following
from IX 2.7 and IV 5.2.6. In the finitely presented case it reduces to `H = D_S(M)`
diagonalizable, uses the classification of subgroups of `D_{κ(s)}(M)` (IX 8.1), Corollaire
5.2 and Corollaire 6.6; the locally noetherian case uses X 4.6. This is explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and groups.** "S-préschémas en groupes" are group schemes over a scheme
  `S : Scheme.{u}` (Mathlib's schemes are not assumed separated, matching *préschéma*).
  "H de type multiplicatif et de type fini" is `IsMultiplicativeType H` (see Scope).
- **Hypotheses.** "G séparé sur S" is `IsSeparated G.X.hom`. "S localement noethérien ou G
  de présentation finie sur S" is the disjunction above, finite presentation being, as in
  EGA (IV₁, 1.6.1), which SGA 3 follows, local finite presentation together with
  quasi-compactness and quasi-separatedness.
- **"K = Ker(u) est un sous-groupe de type multiplicatif et de type fini de H".** The kernel
  is `kernel u`, a subgroup of `H` through `kernelι u`; the assertion is
  `IsMultiplicativeType (kernel u)`.
- **The factorization.** `H/K` is represented by `Q`, and "u′ est l'homomorphisme
  canonique" is `IsFppfQuotient (SubgroupFunctor.range (kernelι u)) q`: `q` is an fppf
  quotient map whose kernel is `K`. "Fidèlement plat" is flat and surjective, both part of
  `IsFppfQuotient`; "affine" is `IsAffineHom q.hom.hom.left`. "u″ est un monomorphisme" is
  `Mono v.hom.hom`, and "u se factorise en H → H/K → G" is `q ≫ v = u`.
- **Local finite presentation of `q`.** `IsFppfQuotient` also requires `q` to be locally of
  finite presentation. This adds nothing to the source: `H` and `Q` are of multiplicative
  type, hence of finite presentation over `S`, so any `S`-morphism `H → Q` is locally of
  finite presentation.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's "de type multiplicatif et de type fini" is therefore exactly
  `IsMultiplicativeType`, and the statement is the full Théorème 6.8.
- All schemes are in universe `u`.
- Not stated here: the N.B. after Théorème 6.8 (`u″` is a closed immersion when `G` is
  affine, or of finite presentation, over `S`; IX 2.5, 2.6 and Remarque 6.6.1).
