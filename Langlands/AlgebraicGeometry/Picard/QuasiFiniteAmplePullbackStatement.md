# Ample pullback along quasi-finite separated morphisms

`Langlands.AlgebraicGeometry.Picard.QuasiFiniteAmplePullbackStatement` is a
proposition definition (universe parameter `u`). It is a statement only. The
module proves nothing.

## The statement

Let `X Y : Scheme.{u}`, let `f : X ⟶ Y` be a morphism, and let
`M : LineBundle Y` be a line bundle (the Library's `Picard.LineBundle`). Assume:

- `LocallyOfFiniteType f`,
- `LocallyQuasiFinite f`,
- `QuasiCompact f`,
- `IsSeparated f` (all four are Mathlib's predicates), and
- `M.IsAmple` (the Library's ampleness predicate).

Then the pullback `(LineBundle.pullback f).obj M` is ample. Here
`LineBundle.pullback f` is the Library's pullback functor on line bundles, from
`Langlands.AlgebraicGeometry.Picard.LineBundlePullback`.

No noetherian hypothesis is made on `X` or `Y`.

The Library's `L.IsAmple` (module `Langlands.AlgebraicGeometry.Picard.Ample`)
says two things: the scheme is quasi-compact, and every point lies in the open
locus `L.sectionOpen s` of some section `s` of a positive tensor power
`L^{⊗k}` (`k ≥ 1`) with this locus affine. This is the Stacks definition of an
ample invertible sheaf (Properties, Definition 28.27.1).

## Source

The first four hypotheses together say that `f` is quasi-finite and separated in
the sense of Stacks. Stacks Definition 29.21.1 (Tag 01TD; file
`Stacks-29.21.1-01TD.html` of the first source below) reads: "We say that `f` is
quasi-finite if `f` is of finite type and every point `x` is an isolated point of
its fibre." Finite type means locally of finite type and quasi-compact, which are
the first and third hypotheses. For `f` locally of finite type, Mathlib's lemma
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton` says that
`LocallyQuasiFinite f` holds if and only if every fibre `f ⁻¹' {y}` is discrete.
A fibre is discrete exactly when each of its points is isolated in it. So,
given the first and third hypotheses, the second is Stacks' condition on the
fibres.

The statement combines two results.

1. Registered source `stacks-quasi-finite-separated-quasi-affine-2026-11-19`
   (content SHA-256
   `6a6b933ff857bfa0cee90cf8a7b3b4deaf8e00119e94dd4379915c59563ff78b`), file
   `Stacks-37.43.2-02LR.html`, Lemma 37.43.2 (Tag 02LR):

   > Let `f : X → S` be a morphism of schemes. Assume `f` is quasi-finite and
   > separated. Let `S'` be the normalization of `S` in `X`. Then `f'` is a
   > quasi-compact open immersion and `ν` is integral. In particular `f` is
   > quasi-affine.

2. Registered source `stacks-quasi-projective-ample-finite-type-2026-11-19`
   (content SHA-256
   `112270b8b6f437c38228945f1221ccc306b020c84ff13bc87f6c2c6efda77692`), file
   `Stacks-29.38-01VG.html`, Lemma 29.38.7, second sentence:

   > If `M` is ample and `f` quasi-affine, then `f^*M` is ample.

The Lean statement is the composite: if `f` is quasi-finite and separated and `M`
is ample, then `f^*M` is ample.

## Use

Task 7748 (`LargeLevelQuasiProjectivityStatement`) needs an ample line bundle on
a fine moduli scheme `X` of polarized abelian schemes with full level structure
(`LargeLevelAmpleStatement`). The planned route maps `X` to a scheme with an
ample line bundle by a quasi-finite separated morphism and pulls the bundle
back. This statement is that last step.

## Relation to other Library results

The Library already proves two special cases.
`ClosedImmersionPullbackAmpleStatement` covers closed immersions, and the theorem
`LineBundle.IsAmple.pullback_of_isAffineHom` (in
`Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen`) covers affine
morphisms. Neither covers open immersions or general quasi-finite separated
morphisms.
