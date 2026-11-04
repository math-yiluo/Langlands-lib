# Maximal split image tori in adjoint quotients: proof

Authors: Worker 1331 and Worker 1404.

The theorem `Langlands.GroupScheme.adjointSplitTorusImageExistenceStatement`
proves `Langlands.GroupScheme.AdjointSplitTorusImageExistenceStatement.{u}`,
imported unchanged from [`SplitTorusImageStatement`](SplitTorusImageStatement.md),
for every universe `u` and every field `k : Type u`. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. It adds no separability,
smoothness, perfectness, characteristic or finite-kernel hypothesis. The centre
of `G`, and so the kernel of the adjoint quotient, may be nonsmooth, for example
for `SL_p → PGL_p` in characteristic `p`. The proof does not assume the existence
of the image or its maximality: it constructs the image and proves the
maximality from published theorems.

The module has two theorems.

- `adjointSplitTorusImageExistenceStatement_of_centralSurjectionMaximality`
  derives the target from the proposition
  `CentralSurjectionMaximalSplitTorusImageStatement.{u}`
  (module [`Rational.CentralSurjectionMaximalSplitTorusImageStatement`](../Rational/CentralSurjectionMaximalSplitTorusImageStatement.md)),
  taken as a premise `hmax`.
- `adjointSplitTorusImageExistenceStatement` discharges `hmax` with the
  published theorem `centralSurjectionMaximalSplitTorusImage`
  (module [`Rational.CentralSurjectionMaximalSplitTorusImageProof`](../Rational/CentralSurjectionMaximalSplitTorusImageProof.md)).

## Implemented proof

Fix a field `k`, an adjoint quotient `q : G ⟶ A` (`IsAdjointQuotient q`) and a
maximal split torus `i : T.toGrp ⟶ G`.

1. *Affineness of the target.* `IsAdjointQuotient q` includes
   `IsAdjoint A`, and so the semisimplicity and connected reductivity of `A`.
   The `isAffineHom` field of that reductivity makes the structure morphism of
   `A` affine.
2. *Image torus.* `IsMaximalSplitTorus i` includes the split-torus structure
   of `T`. Apply `IsSplitTorus.fppfImage` from
   [`Rational.SplitTorusFppfImage`](../Rational/SplitTorusFppfImage.md) to the
   composite `i ≫ q`. Call the result `E`. It consists of a commutative group
   scheme `E.torus` (the `T_ad` of the statement), a homomorphism
   `E.projection : T ⟶ E.torus` (the `p`) and a closed split subtorus
   `E.inclusion : E.torus.toGrp ⟶ A` (the `j`). It also contains the square
   `CommGroupScheme.groupHom p ≫ j = i ≫ q` and makes the underlying scheme
   morphism of `p` flat, surjective and locally of finite presentation.
3. *Maximality.* Apply `hmax` with source `G`, target `A` and map `q`. The
   hypotheses come from `IsAdjointQuotient q`. Connected reductivity of `G` is
   its `isConnectedReductive` field. Connected reductivity of `A` comes from
   step 1. Flatness, surjectivity and local finite presentation of `q` are its
   `flat`, `surjective` and `locallyOfFinitePresentation` fields. Centrality of
   the actual kernel is `kernelCenter.isCentral`: the kernel is the
   scheme-theoretic centre, so it is central. The torus data are `T`,
   `E.torus`, `i`, `j`, `p`, with `IsMaximalSplitTorus i` and the facts from
   step 2. The conclusion is `IsMaximalSplitTorus j`.
4. *Packaging.* The tuple `⟨E.torus, j, p, …⟩` provides the fields of
   `IsAdjointSplitTorusImage q i j p`: the adjoint quotient, the maximality of
   `i` and `j`, the square and the three properties of `p`.
5. *Discharging the premise.* The theorem `adjointSplitTorusImageExistenceStatement`
   is the first theorem applied to `centralSurjectionMaximalSplitTorusImage`.

## Provenance

- The construction in step 2 is the internal Library construction documented
  in [`Rational.SplitTorusFppfImage`](../Rational/SplitTorusFppfImage.md)
  (Author: Worker 1375). It is a lattice-image construction for split tori,
  extending `IsSplitTorus.exists_factor_isSplitSubtorus` in
  [`Rational.SplitTorusImage`](../Rational/SplitTorusImage.md) (Author: Worker
  228). Classically it is Milne, *Algebraic Groups* (2017), registered as
  `milne-2017-algebraic-groups`, Theorem 5.39 (printed p.108 / PDF p.124),
  together with the paragraph after Definition 12.14 (printed p.236 / PDF
  p.252), which says quotients of split tori are split.
- The maximality in step 3 is A. Borel and J. Tits, *Compléments à l'article
  « Groupes réductifs »*, Publ. Math. IHÉS 41 (1972), registered as
  `borel-tits-1972-complements-groupes-reductifs`, Théorème (2.20)(ii)
  (printed p.260 / PDF p.9). By that theorem, the images of maximal `k`-split
  tori under a central surjective `k`-morphism of connected reductive groups
  are maximal `k`-split tori. Définition (2.2) and Remarque (2.3) (printed
  p.254 / PDF p.3) define a central morphism as one whose scheme-theoretic
  kernel lies in the centre. The Library's
  `CentralSurjectionMaximalSplitTorusImageStatement` is that theorem in
  factorization form, and its published proof
  `centralSurjectionMaximalSplitTorusImage` (Author: Worker 1387) argues
  through rational characters rather than through Borel–Tits's conjugacy
  argument; see its Markdown. Borel–Tits 1965 Proposition 4.25 and
  Conrad–Gabber–Prasad Proposition C.4.5(2) are not used, because they need a
  separable or smooth map.
- The use of the adjoint quotient is the derived fact that its kernel, the
  scheme-theoretic centre, is central, and that its quotient map is an fppf
  surjection of connected reductive groups. Both facts are fields of the
  Library predicate `IsAdjointQuotient`.
- The first theorem was written by Worker 1331 and revised by Worker 1404 to
  take the published maximality proposition as its premise.
