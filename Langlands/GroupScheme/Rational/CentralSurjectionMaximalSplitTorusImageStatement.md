# Maximality of a supplied split-torus image under a central surjection

Author: Worker 1457.

This module declares the proposition
`Langlands.GroupScheme.CentralSurjectionMaximalSplitTorusImageStatement`.
It states maximality of a supplied image torus. It supplies neither a proof
nor a construction of that torus.

## Quantifiers and hypotheses

The declaration is polymorphic in every universe `u`. For every field
`k : Type u`, put `S = Spec (CommRingCat.of k)`. It quantifies over actual
group schemes `G H : GroupScheme S` and an actual group-scheme homomorphism
`q : G ⟶ H`, with the following premises:

- `IsConnectedReductive G` and `IsConnectedReductive H`, using the geometric
  reductivity predicate from `Reductive.Basic`. In particular both group
  schemes are smooth, affine and connected over `k`.
- `Flat q.hom.hom.left`, `Surjective q.hom.hom.left`, and
  `LocallyOfFinitePresentation q.hom.hom.left`. These concern the actual
  underlying scheme morphism of `q` and make it an fppf covering morphism.
- `IsCentral (kernelι q)`. The object `kernel q` and its inclusion
  `kernelι q : kernel q ⟶ G` are the actual pullback of `q` along the unit,
  from `Langlands.AbelianScheme.Kernel`. The centrality predicate is from
  `Rational.Characters`: over every test scheme `U` over `S`, every point of
  this kernel maps into the full centre of `G`. Membership in that centre
  means commutation with every point after every further test-scheme base
  change. This includes nonreduced tests and infinitesimal kernel points.

For every such `q`, it then quantifies over actual commutative group schemes
`T T' : CommGroupScheme S` and actual homomorphisms
`i : T.toGrp ⟶ G`, `j : T'.toGrp ⟶ H`, and `p : T ⟶ T'`.
The remaining premises are:

- `IsMaximalSplitTorus i`: `T.toGrp` is split, `i` is a closed immersion,
  and `i` is maximal among split subtori under factorization.
- `IsSplitSubtorus j`: `T'.toGrp` is split and `j` is a closed immersion.
- Flatness, surjectivity and local finite presentation of
  `(CommGroupScheme.groupHom p).hom.hom.left`, the actual underlying scheme
  morphism of `p`.
- The equality of actual group-scheme homomorphisms
  `CommGroupScheme.groupHom p ≫ j = i ≫ q`.

Here `CommGroupScheme.groupHom p` forgets commutativity of the homomorphism.
The underlying scheme morphisms of `i` and `j` are `i.hom.hom.left` and
`j.hom.hom.left`. Thus the last equality gives the actual commuting square
over `S`, also after forgetting to schemes.

The sole conclusion is `IsMaximalSplitTorus j`. The predicates
`IsSplitSubtorus` and `IsMaximalSplitTorus` are the published interfaces in
`Rational.SplitTorus`. Explicitly, the conclusion says that for every actual
commutative group scheme `T''`, split subtorus
`j' : T''.toGrp ⟶ H`, and factorization `f : T'.toGrp ⟶ T''.toGrp` with
`f ≫ j' = j`, the homomorphism `f` is an isomorphism.

Neither kernel finiteness nor kernel smoothness is assumed, for either
`q` or `p`. There is no separability, characteristic or perfectness
hypothesis. Surjectivity concerns schemes, with no assertion of surjectivity
on `k`-points or points of an arbitrary fixed test scheme.

## Source and translation

A. Borel and J. Tits, *Compléments à l'article « Groupes réductifs »*,
Publications Mathématiques de l'IHÉS 41 (1972), 253–276, registered as
`borel-tits-1972-complements-groupes-reductifs`, SHA256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`.
The retained Numdam PDF is
`literature/Armand Borel and Jacques Tits - Compléments à l'article « Groupes réductifs » (1972).pdf`.

- The standing convention on printed p.253 / PDF p.2 takes `G` to be a
  connected reductive group over an arbitrary field.
- Definition (2.2) and Remark (2.3), printed p.254 / PDF p.3, identify a
  central morphism with one whose scheme-theoretic kernel lies in the
  centre. This is the premise `IsCentral (kernelι q)`.
- Theorem (2.20)(ii), printed p.260 / PDF p.9, states that images of maximal
  `k`-split tori under a central surjective `k`-morphism are maximal
  `k`-split tori. The theorem also gives a converse concerning inverse
  images, which this declaration does not include.

This proposition is a derived factorization formulation of the forward
image assertion. The closed immersion `j` presents a split subgroup of `H`;
the fppf covering map `p` and the displayed equality present it as the
supplied image of `i` under `q`. The fppf condition expresses covering
surjectivity without requiring lifts over the original test scheme. The
source's maximality by subgroup inclusion is expressed by the Library's
factorization criterion: an inclusion into a larger split subtorus must be
an isomorphism.

The formulation strengthens the source's surjectivity premise for `q`
to the explicitly requested fppf premise and explicitly assumes the
connected reductivity of the target. It retains nonsmooth scheme-theoretic
kernels. Section 2 is devoted to central morphisms beyond the separable
case; (2.22), printed p.261 / PDF p.10, explicitly invokes (2.20) for a
central isogeny that need not be separable.

Constructing `T'`, `j` and the fppf map `p` is a separate consumer
obligation. The existing adjoint-image existence statement and its imports
are unchanged. Proving the proposition declared here is a separate
successor obligation.
