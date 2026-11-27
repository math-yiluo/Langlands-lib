# Homomorphisms of abelian schemes over a connected base are detected at one geometric point

The module `Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessStatement`
defines one proposition, `ConnectedGeometricPointHomFaithfulnessStatement.{u}`.
The module states it and does not prove it.

## The proposition

For every scheme `S : Scheme.{u}` with instances `IsLocallyNoetherian S` and
`ConnectedSpace S`, assume that every positive natural number is a unit in the
global sections of `S`: for every `k : GroupScheme.Tate.Index (fun _ => True)`,
that is every natural number `k > 0`, the image of `k` in `Γ(S, ⊤)` is a unit.
Then for every algebraically closed field `Ω : Type u`, every morphism
`s : Spec Ω ⟶ S`, all abelian schemes `A B : AbelianScheme S` and every
homomorphism `f : A ⟶ B`, if the pullback `(baseChange s).map f` of `f` to
`Spec Ω` is zero, then `f = 0`.

Here `AbelianScheme S` is the Library's bundled abelian scheme
(`Langlands.AbelianScheme.Basic`): a commutative group object in `Over S` whose
structure morphism is smooth, proper and has geometrically connected fibres.
Its homomorphisms are the homomorphisms of the underlying commutative group
schemes, with the pointwise additive group structure, and `baseChange s` is
the Library's pullback functor `AbelianScheme S ⥤ AbelianScheme (Spec Ω)`.

The hypotheses on `S` are the ones under which the Library's geometric fibre
functor for finite étale covers and its torsion arguments apply: the base is
connected and locally noetherian, and all positive integers are invertible,
so that every torsion subgroup scheme is finite étale.

## Mathematical content and source

This is a form of the rigidity lemma for abelian schemes. Mumford, Fogarty
and Kirwan, *Geometric Invariant Theory*, third enlarged edition (1994),
Chapter 6, §1, Proposition 6.1 (rigidity lemma, printed p.115) and
Corollary 6.2 (printed p.116), registered source
`mumford-fogarty-kirwan-1994-git-3rd`, work over a connected locally
noetherian base `S` and a flat proper `p : X → S` with `H⁰(X_s, O) = κ(s)` for
all points `s`. Corollary 6.2 says that two morphisms from `X` to a group
scheme `G` over `S` which agree on the fibre over one point differ by a
section of `G` pulled back along `p`. For abelian schemes `A` and `B`, applied
to `f` and `0` at the image point of the geometric point, it shows that `f`
is the pullback of a section of `B`, which is the zero section because `f`
preserves the unit sections; so `f = 0`. Vanishing of the pullback to an
algebraically closed geometric point implies vanishing on the fibre over its
image point, by faithfully flat base change from the residue field. The
proposition states this for algebraically closed geometric points, under the
additional hypotheses above. It is internal to the Library and records a
prerequisite for descent of homomorphisms of abelian schemes along étale
covers of a connected base.
