# Actual adjoint quotient interface

This module predicates an actual homomorphism `q : G ⟶ A` over an arbitrary
field `k : Type u`. It records the properties needed to use `A` as the quotient
of the connected reductive group `G` by its full scheme-theoretic centre.
It constructs no quotient and asserts no existence theorem.

## Sources and scope

- J. S. Milne, *Algebraic Groups* (2017), Corollary 17.62(e) and Remark 17.63,
  printed pp.372–373 / PDF pp.388–389. The latter calls the quotient of a
  reductive group by its centre its adjoint group and defines adjoint groups
  to be semisimple with trivial centre. The registered complete official errata
  snapshot of 2026-11-02 has no correction to these passages.
- Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
  Definition A.1.8, printed p.468 / PDF p.494, identifies the actual kernel
  with the functor of points killed by a homomorphism. Definition A.1.10,
  printed p.469 / PDF p.495, uses the scheme-theoretic centre and warns that
  it can be nonsmooth.
- In the same book, Definition A.1.11, printed p.470 / PDF p.496, specifies
  the faithfully flat quotient by a closed subgroup through its universal
  property for right-translation-invariant scheme morphisms. For normal
  subgroups the quotient is a group with the prescribed kernel. Example
  A.1.12 on that page explains that quotient universal properties retain
  nonsmooth kernels.

The Prop-valued structure is derived packaging of these properties on the
Library's `GroupScheme = Grp (Over S)`. Local finite presentation is recorded
explicitly so that the quotient map is fppf. The group universal property is
also recorded explicitly, together with the scheme universal property; the
module does not prove a descent theorem deriving either field from the others.
All targets of the scheme universal property are objects of `Over (Spec k)`
in universe `u`, with no finite-type or separatedness restriction. This is the
categorical quotient interface intended for the later existence task.

## Definitions

`KillsCenter f` says that for every test scheme `T` and every point of the
full centre on `T`, postcomposition with the actual group homomorphism `f`
is the identity. `IsInvariantUnderCenter f` concerns a scheme morphism:
for every `T`, every `G(T)`-point `x` and central `T`-point `z`, it requires
`f(xz) = f(x)`. Both use the existing centre functor, whose membership tests
commutation after every further base morphism. These general definitions
also make sense over arbitrary scheme bases.

`IsAdjointQuotient q` requires:

1. `IsConnectedReductive G` and `IsAdjoint A`, with the finite-centre and
   trivial-full-centre meaning supplied by `Reductive.Semisimple`.
2. Flatness, surjectivity and local finite presentation of the underlying
   scheme morphism of `q`. This asserts no surjectivity on rational points.
3. `IsSchemeTheoreticCenter (kernelι q)`: the actual pullback kernel is a
   closed representative of the entire centre functor.
4. For every group scheme `H`, every `f : G ⟶ H` killing that centre factors
   uniquely through `q` as a group homomorphism.
5. For every scheme over the base, every centre-invariant scheme morphism
   from `G` factors uniquely through the underlying morphism of `q`.

There is no finiteness hypothesis on `q` or its kernel: a connected reductive
group can have a central torus. There is no reducedness, smoothness or
étaleness condition on the centre. The interface concerns the quotient group,
independently of the Lie adjoint representation.

## Intrinsic constructions and proofs

`KillsCenter.isInvariantUnderCenter` uses preservation of multiplication and
the identity by a group homomorphism.

`kernel_range_eq_center` projects the equality of subgroup functors from
the kernel's centre-representation field. `mem_center_iff_comp_eq_one`
combines that equality with the existing `kernelPointsEquiv` and its inverse.
It gives `killsCenter` for `q`.

`kernelCenterPointsEquiv` is the represented-subgroup multiplicative
equivalence on every test scheme. Its value is the actual kernel inclusion;
its naturality equality is associativity of composition, so no point or
infinitesimal information is discarded. `centerKernelIso` applies uniqueness
of represented subgroup functors to any supplied centre representative and
the actual kernel. `centerKernelIso_hom_comp` retains the inclusions into `G`.

`desc` chooses the factorization from the group universal property, and
`comp_desc` is its defining composition equality. `hom_ext` first observes
that any composite through `q` kills the centre, then applies uniqueness of
factorization to compare two maps from `A`. `quotientIso` descends each of two
quotient maps through the other; `hom_ext` and `comp_desc` prove both inverse
identities. `comp_quotientIso_hom` records compatibility with the supplied
quotient maps. Thus any two supplied interfaces are uniquely isomorphic over
`G`; the module does not choose an arbitrary group as its quotient.
