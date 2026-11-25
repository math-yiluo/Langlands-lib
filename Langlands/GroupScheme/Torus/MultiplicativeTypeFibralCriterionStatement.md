# Statement: the fibral criterion for groups of multiplicative type

`Langlands.GroupScheme.MultiplicativeTypeFibralCriterionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType` on group schemes over a field;
- [`Reductive.Basic`](../Reductive/Basic.md), for the geometric fibre `geometricFiber`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), for the residue-field
  fibre `RelativeIdentityComponent.residueFiber`;
- [`AbelianScheme.Torsion`](../../AbelianScheme/Torsion.md), for the `n`-torsion subgroup
  `torsion` of a commutative group scheme;
- [`FiniteEtale.GeometricCardinality`](../../AlgebraicGeometry/FiniteEtale/GeometricCardinality.md),
  for `FiniteEtale.coordinateAlgebra`, the algebra structure on global sections induced by a
  structure morphism to the spectrum of a field.

`GroupScheme S` is `Grp (Over S)`; `H.X : Over S` is its underlying scheme over `S`, and
`H.X.left` is the underlying scheme.

## Predicates and constructions used

- `RelativeMultiplicativeType.IsMultiplicativeType H`, for `H : GroupScheme S`: there is an
  fppf cover of `S` on each member `S_i` of which `H_{S_i}` is isomorphic to the
  diagonalizable group `D_{S_i}(Λ_i)` of a finitely generated abelian group `Λ_i`. This is
  Conrad's Definition B.1.1.
- `geometricFiber H s`, for `s : S`: the base change of `H` along the geometric point
  `Spec κ(s)^alg ⟶ S`, where `κ(s)^alg = AlgebraicClosure (S.residueField s)`. It is a
  group scheme over `Spec κ(s)^alg`.
- `IsMultiplicativeType G`, for a group scheme `G` over `Spec k` with `k` a field: there are
  a field extension `K` of `k`, a finitely generated abelian group `Λ` and an isomorphism of
  `G_K` with the diagonalizable group `D_K(Λ)`. Applied to `geometricFiber H s`, it says that
  the geometric fibre is of multiplicative type.
- `RelativeIdentityComponent.residueFiber H s`: the base change of `H` along
  `Spec κ(s) ⟶ S`, the actual fibre `H_s`. `ConnectedSpace (residueFiber H s).X.left` says
  that the fibre `H_s` is connected.
- `[IsCommMonObj H.X]`: the group law of `H` is commutative. Commutativity passes to base
  changes, so each `geometricFiber H s` is commutative.
- `torsion G n`, for a commutative group scheme `G` and `n : ℤ`: the group-scheme kernel
  `kernel (multiplication G n)` of the multiplication-by-`n` endomorphism of `G`, the
  `n`-torsion subgroup `G[n]`.
- `Module.finrank (AlgebraicClosure (S.residueField s)) Γ(X, ⊤)`, for
  `X = (torsion (geometricFiber H s) n).X.left` with the `κ(s)^alg`-algebra structure given
  by `FiniteEtale.coordinateAlgebra` of its structure morphism: the dimension over
  `κ(s)^alg` of the ring of global functions on `H_s̄[n]`. Since `H_s̄[n]` is a closed
  subscheme of the affine scheme `H_s̄`, this is the dimension of its coordinate ring, which
  is the order of the finite group scheme `H_s̄[n]` when it is finite. (`Module.finrank` is
  `0` for an infinite-dimensional space; under the conditions of the statement `H_s̄[n]` is
  finite.)
- `IsLocallyConstant f`, for `f : S → ℕ`: every fibre of `f` is open in `S`, i.e. `f` is
  locally constant for the Zariski topology.

## Statement and quantifiers

The proposition quantifies over every scheme `S` and every `H : GroupScheme S` whose
structure morphism is flat, locally of finite presentation and affine
(`[Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom]`). It asserts
the conjunction of:

1. **Connected fibres.** If every fibre `H_s` is connected, then
   `RelativeMultiplicativeType.IsMultiplicativeType H` holds if and only if
   `IsMultiplicativeType (geometricFiber H s)` holds for every `s : S`.
2. **Commutative groups.** If the group law of `H` is commutative, then
   `RelativeMultiplicativeType.IsMultiplicativeType H` holds if and only if both
   - `IsMultiplicativeType (geometricFiber H s)` holds for every `s : S`, and
   - for every natural number `n > 0`, the function sending `s : S` to the order of
     `H_s̄[n] = torsion (geometricFiber H s) n` (the dimension of its coordinate ring over
     `κ(s)^alg`) is locally constant on `S`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Theorem B.4.1, p.297: "Let S be a scheme and H an fppf S-affine S-group. Then H is of
  multiplicative type if and only if its geometric fibers are of multiplicative type and
  the order of H_s̄[n] is locally constant in s for each n ≥ 1. The fibral torsion
  condition can be dropped if H → S has connected fibers; e.g., tori."
- Paragraph after Theorem B.4.1, p.297: "In the absence of a fibral connectedness
  condition it is necessary to impose some local constancy hypothesis on the type or at
  least its torsion levels, even if we assume H is commutative", with the example of the
  constant group `(ℤ/dℤ)_R` over a discrete valuation ring with the non-identity points of
  the special fibre removed.
- Start of §B.4, p.297: for a finite type group over a field `k` and an extension `K/k`,
  being of multiplicative type is insensitive to passing to `K`, so "it does not matter if
  we consider the actual fibers G_s or associated geometric fibers G_s̄".
- Definition B.1.1, p.280: groups of multiplicative type over a scheme.

Conrad's proof (from p.297) reduces to a strictly henselian local base, lifts a splitting
`D_k(M) ≃ H_k` of the special fibre to an open and closed immersion `D_A(M) → H` by
Theorem B.3.2 and fpqc descent, and shows that it is surjective, by connectedness of the
fibres in the first case and by comparing the orders of `n`-torsion in the second. This is
explanation only.

## Derivation from the source

- **fppf S-affine S-group.** The structure morphism of `H` is flat, locally of finite
  presentation and affine. These are instance hypotheses.
- **Of multiplicative type.** For `H` over `S`, Definition B.1.1, the relative predicate.
  For the geometric fibres over the field `κ(s)^alg`, the field-level
  `IsMultiplicativeType` of the Library. Over an algebraically closed field this agrees
  with being diagonalizable with finitely generated character group, by the insensitivity
  to field extension noted at the start of §B.4.
- **Geometric fibres.** One geometric point per point `s`, through the algebraic closure of
  `κ(s)`, as in Conrad's proof ("using an algebraic closure of k(s)"). By the remark at the
  start of §B.4, the choice of geometric point over `s` does not matter.
- **Order of `H_s̄[n]`.** `H_s̄[n]` is the `n`-torsion subgroup scheme of the geometric fibre.
  Its order is the dimension of its coordinate ring over `κ(s)^alg`. "Locally constant in s"
  is `IsLocallyConstant` on the underlying topological space of `S`. The quantifier
  "for each n ≥ 1" is `∀ n : ℕ, 0 < n →`, with `n` cast to `ℤ` for `torsion`.
- **Connected fibres.** "H → S has connected fibers" is connectedness of each actual
  fibre `H_s` over `κ(s)`, through `RelativeIdentityComponent.residueFiber`. In this case
  part 1 drops the torsion condition, as in the second sentence of the theorem.

## Scope and deviations

All schemes are in universe `u`. The base `S` is arbitrary, as in the source.

- **Commutativity in part 2.** Part 2 assumes that `H` is commutative. The Library's
  `torsion G n` is defined for commutative group schemes only, since for a non-commutative
  group the `n`-th power map is not a homomorphism. A group of multiplicative type is
  commutative, so the forward implication of Conrad's criterion loses nothing; the reverse
  implication is stated only for commutative `H`. The case of a non-commutative `H` whose
  geometric fibres are of multiplicative type is not covered by part 2. Part 1 has no
  commutativity hypothesis.
- **Type.** Conrad remarks that the torsion condition holds when the type (the isomorphism
  class of the character group of `H_s̄`) is locally constant, as in SGA 3, X, 4.8. This
  variant is not stated.
