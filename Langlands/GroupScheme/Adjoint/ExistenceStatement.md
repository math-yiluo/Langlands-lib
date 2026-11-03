# Existence of the actual adjoint quotient: statement

Worker 1400.

This module defines one proposition and proves nothing. It constructs no
quotient. A proof of the proposition is a separate task.

## `AdjointQuotientExistenceStatement`

`AdjointQuotientExistenceStatement.{u}` says: for every field `k : Type u` and
every group scheme `G` over `Spec k` with `IsConnectedReductive G`, there
are a group scheme `A` over `Spec k` and a group-scheme homomorphism
`q : G ⟶ A` with `IsAdjointQuotient q`.

The universe `u` is arbitrary and the field is arbitrary: it need not be
perfect, infinite or of characteristic zero. `A` and `q` live over the same
base `Spec k` and in the same universe as `G`. The only premise is
`IsConnectedReductive G`: `G` is smooth, affine and connected over `Spec k`,
and its base change to `AlgebraicClosure k` has trivial unipotent radical.

`IsAdjointQuotient q` is the published structure of
`Langlands.GroupScheme.Adjoint.Quotient`, used unchanged. All of its fields
are conclusions of this statement, and none is a premise:

1. `IsConnectedReductive G` (this field repeats the premise).
2. `IsAdjoint A`: `A` is connected reductive, its scheme-theoretic centre
   has a finite closed representative, and that centre is trivial, i.e.
   `center A = ⊥` as a subgroup functor.
3. The underlying scheme morphism of `q` is flat, surjective and locally of
   finite presentation. Surjectivity is surjectivity of the map of
   underlying topological spaces, not of rational points.
4. `IsSchemeTheoreticCenter (kernelι q)`: the actual pullback kernel of `q`
   is a closed subgroup whose range functor is the whole centre functor
   `center G`. Membership in `center G` on a test scheme `T` means
   commuting with every point of `G` after every further morphism `T' ⟶ T`.
   The centre is not replaced by its reduced subgroup, its maximal torus,
   or its group of rational points.
5. Group universal property: for every group scheme `H` over `Spec k`, every
   homomorphism `G ⟶ H` killing the centre on all test schemes factors
   uniquely through `q`.
6. Scheme universal property: for every `Y : Over (Spec k)` in universe `u`,
   every scheme morphism `G.X ⟶ Y` invariant under right translation by
   central points on all test schemes factors uniquely through the
   underlying morphism of `q`. Neither `H` nor `Y` is assumed to be of
   finite type, separated or affine.

The statement does not require `q` or its kernel to be finite: the centre of
a connected reductive group can contain a torus, so `q` need not be an
isogeny. It requires no smoothness, reducedness or étaleness of the centre.
It concerns the quotient group by the centre, not the Lie adjoint
representation, and not the simply connected central cover of the derived
group. By `IsAdjointQuotient.quotientIso` any two such `(A, q)` are
canonically isomorphic compatibly with `q`, so the statement determines `A`
up to unique isomorphism over `G`; it asserts only existence.

## Sources

- J. S. Milne, *Algebraic Groups* (2017), source ID
  `milne-2017-algebraic-groups`. Corollary 17.62(e), printed p.372 / PDF
  p.388, with its proof on printed p.373 / PDF p.389: for a reductive group
  `G`, the quotient `G/Z(G)` has trivial centre. Remark 17.63, printed
  p.373 / PDF p.389: an adjoint group is a semisimple group with trivial
  centre, and the quotient of a reductive group by its centre is an adjoint
  group, called the adjoint group of `G`. Milne's reductive groups are
  connected. His centre `Z(G) = C_G(G)` is the scheme-theoretic one
  (Proposition 1.92 and the following definition, printed pp.33–34 / PDF
  pp.49–50), defined by commutation on all `k`-algebras.
- The quotient itself is Milne's Theorem 5.14 (printed p.102 / PDF p.118)
  with Proposition 5.18 (printed p.103 / PDF p.119): every normal algebraic
  subgroup of an affine algebraic group is the kernel of a quotient map
  (a faithfully flat homomorphism, Definition 5.5, printed p.99 / PDF
  p.115) onto an affine algebraic group.
- Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
  source ID `conrad-gabber-prasad-2015-pseudo-reductive`. Definition A.1.10,
  printed p.469 / PDF p.495, defines the scheme-theoretic centre of a smooth
  group through all `k`-algebras; the paragraph before it notes that such
  centralizers need not be smooth (`Z_{SL_p} = μ_p` in characteristic `p`).
  Definition A.1.11, printed p.470 / PDF p.496, takes `G/H` in the sense of
  SGA3 VI_A Theorem 3.2(iv): a faithfully flat map of `k`-schemes
  `G → G/H` that is initial among maps of `k`-schemes invariant under right
  translation by `H`; for normal `H` it is a homomorphism with kernel `H`.
  Example A.1.12 on the same page shows that this quotient property holds
  regardless of whether the kernel is smooth.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no correction to
17.62, 17.63, 1.92, 5.14 or 5.18. It corrects Corollary 12.41 (printed
p.244), cited in the proof of 17.62(e), to require `N` central in `H`. That
proof applies 12.41 to the centre `Z(G)` inside its preimage `Z'`, where
`Z(G)` is central, so the correction leaves 17.62(e) intact.

## Derived packaging

The statement is derived: neither source states this exact proposition.
Milne gives existence of `G/Z(G)` and its adjointness for reductive `G`;
the Lean statement asks for an `A` and `q` satisfying the published
interface. The relation of each conclusion to the sources is:

- `IsAdjoint A`: Remark 17.63 and Corollary 17.62(e). The Library's
  `IsAdjoint` packages Milne's "semisimple with trivial centre" as
  connected reductive with a finite closed centre representative, plus a
  trivial centre functor, following `Reductive/Semisimple.md`.
- Flatness and surjectivity: Milne's quotient maps are faithfully flat.
  Local finite presentation is not named in the sources; it holds because
  `G` and `A` are of finite type over a field. It is recorded so that `q`
  is an fppf morphism.
- Kernel equal to the full centre: Milne Theorem 5.14 and CGP A.1.11, with
  the scheme-theoretic centre of Milne 1.92 and CGP A.1.10.
- The group and scheme universal properties are stated by Milne (Theorem
  5.13, printed p.101 / PDF p.117, and Proposition 5.21, printed p.104 /
  PDF p.120) only for algebraic groups and algebraic schemes. CGP A.1.11
  states the scheme property for all `k`-schemes. The interface keeps the
  full scope: arbitrary group schemes and arbitrary schemes over `Spec k`
  in universe `u`, as documented in `Adjoint/Quotient.md`. This is the
  fppf-sheaf property of the quotient: `G → G/Z(G)` is an fppf covering,
  `G ×_{G/Z(G)} G ≅ G × Z(G)`, and schemes are fppf sheaves. The group
  property for an arbitrary `H` follows from the scheme property applied
  to `G` and to `G × G`.

This module does not prove these derivations; they are obligations of the
proof task for this statement.
