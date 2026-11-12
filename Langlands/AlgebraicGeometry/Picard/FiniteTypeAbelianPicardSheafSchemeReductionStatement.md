# Scheme representability of the Picard sheaf from the algebraic-space and normal cases

Author: Worker 5067.

## Statement

`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} →
  NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} →
    FiniteTypeAbelianPicardSheafSchemeStatement.{u}
```

All three propositions are published Library statements in namespace
`Langlands.AlgebraicGeometry.Picard`, imported unchanged, at the same universe `u`:

- `FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement` (module
  `Picard/FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement`): for every commutative
  ring `R : Type u` of finite type over `ℤ` and every
  `A : Langlands.AbelianScheme (Spec (CommRingCat.of R))`, the fppf Picard class sheaf
  `RelativePicard.classSheaf A.X.hom` is an algebraic space over `Spec R`
  (`AlgebraicSpace.IsAlgebraicSpace`). It also has an étale surjective scheme atlas that is
  locally of finite presentation over `Spec R`.
- `NormalFiniteTypeAbelianPicardSheafAFSchemeStatement` (module
  `Picard/NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`): for every integrally
  closed domain `R : Type u` of finite type over `ℤ` and every abelian scheme `A` over
  `Spec R`, the presheaf `RelativePicard.classSheafPresheaf A.X.hom` is represented
  (Mathlib `Functor.RepresentableBy`) by some `P : Over (Spec R)` such that every finite
  set of points of `P.left` lies in one affine open
  (`PointTopology.HasFiniteAffineNeighborhoods P.left`).
- `FiniteTypeAbelianPicardSheafSchemeStatement` (module
  `Picard/FiniteTypeAbelianPicardSheafSchemeStatement`): for every commutative ring
  `R : Type u` of finite type over `ℤ` and every abelian scheme `A` over `Spec R`, the
  presheaf `RelativePicard.classSheafPresheaf A.X.hom` is represented by some
  `P : Over (Spec R)`.

So the proposition says: if the Picard sheaf of every abelian scheme over a finite-type
`ℤ`-algebra is an algebraic space, and the Picard sheaf over every integrally closed
finite-type `ℤ`-domain is represented by a scheme in which finite sets of points have
affine neighbourhoods, then the Picard sheaf over every finite-type `ℤ`-algebra is
represented by a scheme.

Both premises are universal propositions over all bases of their class. The conclusion
covers every finite-type `ℤ`-algebra `R`, including nonreduced rings and rings that are
not domains, and every abelian scheme over `Spec R`, with test schemes ranging over the
whole slice `Over (Spec R)`. Nothing is required of the representing scheme in the
conclusion.

## What the statement does not assert

It is an implication between published propositions. It does not assert either premise,
so it does not by itself prove `FiniteTypeAbelianPicardSheafSchemeStatement`. It asserts
no finite-set property, finiteness or separation property of the representing scheme in
the conclusion. It proves nothing: it is a proposition definition only.

## Provenance

This is an internal reduction statement for the proof task
`de799868-75c2-4835-b620-f024e5969aa8` (Task 5600). It records how that task splits its
target. No source states this exact Lean proposition. The split follows the structure of
Deligne's proof of Faltings–Chai, Chapter I, Theorem 1.9, with one gluing step replaced by
a published descent theorem.

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990), registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`, SHA-256
`f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`, Chapter I §1:

- Theorem 1.9(a), printed p.5 (PDF p.17), starts with an abelian algebraic space. For
  `Pic(A/S)` the input that `Pic(A/S)` is an algebraic space is Artin's theorem, recalled
  on printed p.3 (PDF p.15). This is the role of the first premise.
- Deligne's proof, printed p.6 (PDF p.18), reduces to `S = Spec R` with `R` of finite type
  over `ℤ`. For the normalization `T̃` of an irreducible component `T` of `S` it then shows
  that `A_T̃` is projective and that `Pic(A/S)_T̃` is a scheme in which any finite set of
  points lies in an affine open (printed p.6 bottom to p.7 top). This is the role of the
  second premise, for `T̃ = Spec` of the normalization of `R` modulo a minimal prime.
- The proof then glues over `S` by Noetherian induction and amalgamated sums, along the
  irreducible components and along the normalization and its conductor (printed p.7, PDF
  p.19). The present reduction does not use this gluing.

The gluing is replaced by descent of schemeness along finite surjective morphisms with AF
source. This is Philipp Gross, *Tensor generators on schemes and stacks*, Algebraic
Geometry 4 (2017), no. 4, 501–522, registered source
`gross-tensor-generators-schemes-stacks-2017`, SHA-256
`fa20fe6fff07a861f93d6640e553f2cc8f48b694487c49e257a089ce52b45e8b`, Theorem 1.2 (printed
p.502) and Section 3 (printed pp.510–512). In the Library it is the published theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts.exists_representation`,
applied with the published proof `finiteSurjectiveQuasiAffineSourceAF`. The disjoint union
of the normalizations of `R` modulo its minimal primes maps finitely and surjectively to
`Spec R`. Over it the Picard sheaf is represented by an AF scheme, by the second premise
applied to each component. Descent along the induced finite surjective chart of the
algebraic space from the first premise then gives a scheme.

Unlike Theorem 1.9(b), the conclusion keeps no finite-set property of the representing
scheme, matching the published target.

## Use

A proof of this proposition, together with proofs of its two premises, proves
`FiniteTypeAbelianPicardSheafSchemeStatement`. The first premise is the target of task
`3931bd2c-94d1-4d23-acab-fbcd0c8074a7`. Worker 3570 is splitting the second premise into
the existence of an ample line bundle and the projective case.
