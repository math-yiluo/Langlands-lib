# Reduction of the Picard-trivial central cover to factoriality

This module proves two theorems. Neither uses any unproved hypothesis beyond
the explicit argument of the second.

## Line bundles on affine schemes with trivial Picard group

`lineBundle_nonempty_iso_trivial_of_isAffine` takes an affine scheme `X` whose
ring of global sections `Γ(X, ⊤)` has trivial module Picard group
(`Subsingleton (CommRing.Pic Γ(X, ⊤))`). It proves that every line bundle `L` on
`X` (`Langlands.AlgebraicGeometry.Picard.LineBundle X`) is isomorphic, in the
category of line bundles, to `LineBundle.trivial X`.

Proof. Let `e = X.isoSpec : X ≅ Spec Γ(X, ⊤)`.

1. The pullback of `L` along `e.inv` is a line bundle on `Spec Γ(X, ⊤)`.
   `nonempty_lineBundle_iso_structureSheaf_of_pic_trivial`
   (`Picard/AffineLineBundlePicard`) makes its underlying sheaf isomorphic to
   the structure sheaf. `ObjectProperty.isoMk` lifts this to an isomorphism
   `t'` with the trivial line bundle.
2. `L` is isomorphic to the pullback of `L` along `e.hom ≫ e.inv = 𝟙 X`, by
   `LineBundle.pullbackId` after rewriting with `e.hom_inv_id`.
3. That pullback is isomorphic to the pullback along `e.hom` of the pullback
   along `e.inv` (`LineBundle.pullbackComp`). Applying the pullback along
   `e.hom` to `t'` and then `LineBundle.pullbackTrivialIso e.hom` gives an
   isomorphism with `LineBundle.trivial X`.

## The reduction

`splitSemisimplePicardTrivialCover_of_factorial` proves
`SplitSemisimplePicardTrivialCoverStatement.{u}` from the hypothesis
`SplitSimplyConnectedFactorialStatement.{u}` (the coordinate ring of a split
simply connected group is a unique factorization domain).

Proof. Let `G` be semisimple over a field `k`, with a split maximal torus
`i : T ⟶ G`.

1. The published `splitSimplyConnectedCoverExistence` gives a group `C` and a
   central isogeny `π : C ⟶ G` with `IsSimplyConnected C`. In particular `C`
   is semisimple (`IsSimplyConnected.isSemisimple`).
2. The published `centralIsogenySplitMaximalTorusLift` gives a split maximal
   torus `j : T' ⟶ C` lifting `i` along `π`, so `HasSplitMaximalTorus C`.
3. The hypothesis makes `Γ(C.X.left, ⊤)` an integral domain with unique
   factorization. Mathlib's instances make it a GCD monoid
   (`RingTheory/UniqueFactorizationDomain/GCDMonoid`), so its Picard group is
   trivial (`RingTheory/PicardGroup`, Stacks 0BCH).
4. `C` is affine over `Spec k` (`IsConnectedReductive.isAffineHom`), so
   `C.X.left` is an affine scheme (`isAffine_of_isAffineHom`).
5. The first theorem makes every line bundle on `C.X.left` trivial. So `C`,
   `π` and the semisimplicity of `C` witness the target.

The cover `C` is simply connected, which is more than the target asserts.
