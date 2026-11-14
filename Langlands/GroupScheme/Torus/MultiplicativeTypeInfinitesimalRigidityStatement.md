# Statement: infinitesimal rigidity of homomorphisms from groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalRigidityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1) and,
transitively, the base-change functor `GroupScheme.baseChange`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `f : H ⟶ G` in it is a homomorphism of
group schemes over `S`, with underlying morphism of `S`-schemes `f.hom.hom : H.X ⟶ G.X`. The
scoped notation of `CategoryTheory.MonObj` is open, so for every `S`-scheme `T` the set of
morphisms `T ⟶ G.X` carries the group structure induced by the group law of `G`, and `1` is
its unit: the composite of the structure morphism `T → S` with the unit section of `G`.

## Objects and predicates used

- `A : Type u` is a commutative ring, `S = Spec A`, and `J` is an ideal of `A` with
  `IsNilpotent J`, that is, `J ^ m = 0` for some natural number `m`.
- `Spec.algebraMap A (A ⧸ J) : Spec (A/J) ⟶ Spec A` is the closed immersion
  `S₀ ⟶ S` defined by `J`.
- `(GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f : H_{S₀} ⟶ G_{S₀}` is the
  base change `f₀` of `f` to `S₀`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.
- For a homomorphism `f`, the equation `f.hom.hom = 1` says that `f` is the trivial
  homomorphism: its underlying morphism `H.X ⟶ G.X` is the unit of the group of
  morphisms `H.X ⟶ G.X`, so every point of `H` maps to the unit of `G`.

## Statement and quantifiers

For every commutative ring `A : Type u`, every nilpotent ideal `J` of `A`, all group
schemes `G H` over `Spec A` and every homomorphism `f : H ⟶ G`: if `H` is of multiplicative
type and the base change `f₀` of `f` to `Spec (A/J)` is trivial, then `f` is trivial.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Corollary B.2.7, p.287: "Let S = Spec(A) and S₀ = Spec(A/J) for an ideal J of A such
  that J^{n+1} = 0 for some n ≥ 0. An S-homomorphism f : H → G from a multiplicative type
  S-group H to an arbitrary S-group scheme G is trivial if its restriction f₀ over S₀ is
  trivial." The source adds that this rigidity property is SGA3 IX, Cor. 3.5.
- Definition B.1.1, p.280, defines `S`-groups of multiplicative type.

The source introduces the corollary with "Via induction, the preceding corollary
immediately yields". That preceding result, Corollary B.2.6 (p.287), assumes that `G` is
smooth over an affine `S = Spec A`, that `H` is an affine `S`-group and that `J` is a
square-zero ideal, and lets `H₀` act on `Lie(G₀)` through `Ad_{G₀} ∘ f₀`. It says that,
when `f₀` lifts to an `S`-homomorphism, "the set of such lifts taken up to conjugation by
ker(G(S) → G(S₀)) is a principal homogeneous space for the group H¹(H₀, Lie(G₀) ⊗ J)".
So the first Hochschild cohomology group classifies conjugacy classes of lifts, not the
lifts themselves. Remark B.2.4 (p.285) gives `Hⁱ(H, ·) = 0` on quasi-coherent objects
for `i > 0` when `H` is of multiplicative type over an affine base. In that case there is
exactly one conjugacy class of lifts. When `f₀` is trivial, that class contains the
trivial homomorphism, and every conjugate of the trivial homomorphism is trivial. The
source does not explain how the smoothness hypothesis of Corollary B.2.6 is removed for
an arbitrary `G`; for the general statement it refers to SGA3, IX, Cor. 3.5. This is
explanation only and is not formalized here.

## Derivation from the source

- **Nilpotent ideal.** "J^{n+1} = 0 for some n ≥ 0" is equivalent to `IsNilpotent J`. One
  direction is immediate. Conversely, if `J ^ m = 0` with `m > 0`, then `J ^ (n + 1) = 0`
  for `n = m > 0`, since `J ^ (m + 1) ⊆ J ^ m`. If `m = 0`, then the unit ideal `J ^ 0` is zero, so
  `A` is the zero ring and `J ^ 2 = 0` as well.
- **Restriction over `S₀`.** "Its restriction f₀ over S₀" is the base change of `f` along
  the closed immersion `S₀ ⟶ S`.
- **Trivial.** A homomorphism is trivial when it factors through the unit section, which
  is `f.hom.hom = 1` and, over `S₀`, `f₀.hom.hom = 1`.
- **No hypotheses on `G`.** `G` is an arbitrary group scheme over `S`, as in the source.

## Scope

`A` and all schemes are in universe `u`. Only the stated rigidity is formalized: if `f₀`
is trivial, then so is `f`. The statement does not formalize the classification of lifts
of a nontrivial homomorphism in Corollary B.2.6. That classification holds only up to
conjugation by `ker(G(S) → G(S₀))`, and distinct lifts can be conjugate.
