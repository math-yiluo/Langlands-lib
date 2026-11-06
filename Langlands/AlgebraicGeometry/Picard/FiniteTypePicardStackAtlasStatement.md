# Smooth scheme atlases of the Picard stack over a finite-type `ℤ`-algebra: statement

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement`.

Authors: Workers 281 and 1603. This pair reuses Worker 281's shared draft
revision 1 for task `07e7cc70-db29-43a4-8bcc-5b1143886686`.

`FiniteTypePicardStackAtlasStatement.{u}` is a proposition, with no proof in
this module. It quantifies over every commutative ring `R : Type u` that is
of finite type over `ℤ` (`Algebra.FiniteType ℤ R`, for the canonical
`ℤ`-algebra structure) and every scheme `X : Over (Spec (CommRingCat.of R))`.
Its two hypotheses are `IsProper X.hom` and `Flat X.hom`. Its conclusion is
the concrete condition
`PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas X.hom`.

Unfolding that condition, write `S = Spec R` and `f = X.hom`. There must
exist an actual scheme `U` over `S` and an actual line bundle `L` on
`U ×ₛ X.left` such that `U → S` is locally of finite type. For every scheme
`T` over `S` and every actual line bundle `M` on `T ×ₛ X.left`, there must
exist a scheme `P` over `T.left` whose lifted Yoneda presheaf is naturally
isomorphic to `PicardGroupoid.pointFiberPresheaf f L M`, with
`P → T.left` smooth and surjective.

At any `Z → T.left`, that point-fibre presheaf retains a map
`(Z → T.left → S) → U` over `S` and an actual isomorphism of the pulled-back
line bundles on `Z ×ₛ X.left`. Its restrictions include the coherent
pullback comparisons of `PicardGroupoid.relative f`. Representation is on
the whole slice over `T.left`, including every test morphism; the definition
uses an explicit universe lift and does not quotient these isomorphisms.
There are no affine, reduced, quasi-compact or nonempty restrictions on
`T` or `Z`.

The predicate is the unchanged published one from
`Langlands.AlgebraicGeometry.Picard.StackAtlas`, the same predicate used by
`FieldPicardStackAtlasStatement`. This module imports only that module and
Mathlib's `Morphisms.Flat`, `Morphisms.Proper` and `RingTheory.FiniteType`.

## Source and derivation

The source is The Stacks Project, in the original HTML snapshots retrieved
1 November 2026 and registered as
`stacks-picard-stack-algebraicity-2026-11-01`. This is the same registered
publication folder, with the same locators, as the published field
statement. The following filenames are in that folder; their `.txt`
companions are mechanical reading aids.

- **`0372.html`, Section 95.16, definition preceding Lemma 95.16.1.**
  The Picard stack has objects `(T, b, M)` with `M` an invertible sheaf on
  `T ×ₛ X`, and arrows given by a base morphism and an isomorphism to the
  pulled-back sheaf. These are the actual line bundles and isomorphisms of
  the published relative Picard groupoid. The direction used to describe
  an isomorphism can be reversed by inversion. The stack fibre product
  with two such families is therefore the point-fibre construction used
  here, with its ordinary pullback restrictions.
- **`0D04.html`, Proposition 99.10.2.** For a morphism `f : X → B` of
  algebraic spaces that is flat, of finite presentation and proper, the
  Picard stack is algebraic. Here `B = Spec R` and `X` is a scheme.
  Flatness is an explicit hypothesis. Finite presentation follows from
  properness: since `ℤ` is noetherian and `R` is of finite type over `ℤ`,
  the Hilbert basis theorem makes `R` noetherian. Over the noetherian
  scheme `Spec R`, the finite type morphism `f` is therefore of finite
  presentation. These reductions are part of the mathematical derivation of
  this specialization and remain obligations for its Lean proof.
- **`026O.html`, Definition 94.12.1, third condition.** Algebraicity supplies
  a scheme `U` over the base with a smooth surjective morphism to the
  stack. A morphism from `U` to the actual Picard stack is given, up to
  isomorphism, by an actual line bundle `L` on `U ×ₛ X`.
- **`0DM9.html`, Lemma 108.8.1.** The Picard-stack diagonal is affine and of
  finite presentation. For any family `M` over any `T`, the space
  `U ×_{Picard stack} T` is affine over the scheme `U ×ₛ T`: it is the
  base change of that diagonal. Hence this space is a scheme. Its
  projection to `T` is smooth and surjective by base change of the atlas.
  Its represented presheaf is the entire actual point-fibre presheaf
  described above. This diagonal argument is needed for the
  scheme-represented point fibres in the concrete Lean condition; an
  arbitrary algebraic-stack atlas alone only gives algebraic-space
  fibres. The source proves the diagonal assertion using the open
  immersion into the coherent-sheaf stack, `0D03.html`, Lemma 99.10.1, and
  its affine finitely presented diagonal, `0DLY.html`, Lemma 108.4.1.
- **`0DM9.html`, Lemma 108.8.2.** The Picard stack is locally of finite
  presentation over the base. A smooth atlas is locally of finite
  presentation over the stack; composing gives `U → Spec R` locally of
  finite presentation, hence locally of finite type as required here. The
  source proves the stack assertion from `0D03.html` and `0DLZ.html`,
  Lemma 108.4.2.

The proposition is a derived specialization of these results, rather
than a verbatim single source assertion. Its full scheme-fibre condition
uses the affine diagonal, and its local finite type condition uses local
finite presentation. Matching the source stack to the actual published
line-bundle pseudofunctor, and proving all these constructions and
reductions in Lean, are part of the future proof.

The retained comments on `0372.html` concern corrected typographical errors
in a base object and the order of composition; those on `0D03.html` concern
a corrected grammatical typo. None changes the cited assertions. The
other cited pages have no comments changing the mathematics.

## Relation to other statements

Over a field `k`, every scheme is flat over `Spec k`, so the published
`FieldPicardStackAtlasStatement` has the same shape with the flatness
hypothesis omitted. The present
statement retains flatness explicitly and covers finite-type integer
algebras such as `ℤ` that are not fields. Abelian schemes over `Spec R`
are proper and smooth, hence flat, so a future proof of this statement
would provide, for every abelian scheme
`A` over `Spec R` with `R` of finite type over `ℤ`, the atlas condition for
`A.X.hom`. That atlas is the missing input for the finite-type abelian
Picard-sheaf representability task.

## Scope and remaining obligations

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and non-connected ones, and the zero
ring. It allows every proper flat scheme over `Spec R`. It assumes no
projectivity, smoothness, reducedness, connectedness, geometric
connectedness of fibres, rational point, section or identification of
global functions with `R`. The bundle `L` belongs to an atlas for the
stack of actual bundles; no universal bundle on a Picard sheaf is
asserted or assumed.

This module proves neither stack descent nor the existence of the atlas.
It states no quotient theorem, no comparison between etale and fppf
sheafifications, and no representability of the actual fppf Picard sheaf.
Those are separate inputs needed for the host representability task.
The statement adds neither a cohomological-flatness hypothesis nor a
finite-presentation hypothesis; the latter is a future deduction from
properness over the noetherian base, as described above. It also leaves
the published generic Hom/Isom representability results unchanged.
