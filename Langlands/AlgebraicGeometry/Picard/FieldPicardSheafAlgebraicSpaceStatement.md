# The fppf Picard sheaf over a field as a separated algebraic space

Authors: Worker 144 and Worker 766.

## Statement

`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement.{u}`
is a proposition. It states: for every field `k : Type u` and every scheme
`X : Over (Spec (CommRingCat.of k))`, the single hypothesis `IsProper X.hom`
implies the three conjuncts below. Write `S` for `Spec (CommRingCat.of k)`,
`F` for the Library sheaf `RelativePicard.classSheaf X.hom`, and
`F.obj = RelativePicard.classSheafPresheaf X.hom` for its underlying presheaf
`(Over S)ᵒᵖ ⥤ Type (u+1)`.

1. `AlgebraicSpace.IsAlgebraicSpace S F`. By the Library definition in
   `Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`, this says that the
   diagonal of `F.obj` is representable by actual schemes over `S`. It also says
   that there are an actual `U : Over S` and a natural transformation
   `a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ F.obj` with
   `AlgebraicSpace.IsEtale a` and `AlgebraicSpace.IsSurjective a`. Both of these
   properties include representability of `a`. They require every represented
   projection to be an etale, respectively surjective, morphism of schemes.
2. `AlgebraicSpace.IsClosedImmersion (Limits.diag F.obj)`. The diagonal
   `F.obj ⟶ F.obj ⨯ F.obj` is formed in the category of presheaves on `Over S`.
   The product of presheaves on the slice is the fibre product over `S`.
   By the Library definition in
   `Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening`, the predicate
   requires representability of the diagonal by actual schemes. It also requires
   that, for every actual `T : Over S` and every map from the functor of points
   of `T` to `F.obj ⨯ F.obj`, the projection of every represented pullback square
   is a closed immersion of schemes. This conjunct is the separatedness of `F`
   over `S`.
3. There exist an actual `U : Over S` and
   `a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ F.obj` with
   `AlgebraicSpace.IsEtale a`, `AlgebraicSpace.IsSurjective a` and
   `LocallyOfFiniteType U.hom`. The last condition is Mathlib's
   scheme-morphism property for the structure morphism `U.left ⟶ S`. This
   conjunct expresses that `F` is locally of finite type over `k` by an actual
   atlas. The atlas need not coincide with the one supplied by conjunct 1.

Here `AlgebraicSpace.schemeYoneda S` is the Library's lifted Yoneda functor.
Its value on `U` at `T` is `ULift (T ⟶ U)`, valued in `Type (u+1)`.

## The actual sheaf and the scope

The definitions are imported unchanged from the Library. `RelativePicard.classSheaf X.hom`
is Mathlib's sheafification in `Type (u+1)`, for `Scheme.fppfTopology.over S`, of the
ordinary class presheaf `RelativePicard.classPresheaf X.hom`. That presheaf sends a
test scheme `T` over `S` to the isomorphism classes of actual line bundles on the
fibre product `T ×_S X`. The sheaf's type
`Sheaf (Scheme.fppfTopology.over S) (Type (u+1))` is by definition the Library's
`AlgebraicSpace.FppfSheaf S`. Thus conjunct 1 is applied to the published sheaf
itself, with no replacement or conversion. The sheaf is not assumed to be a
scheme, and no rigidified or other substitute functor occurs.

- The field `k` is arbitrary, including imperfect fields.
- `X` is an arbitrary proper scheme over `k`. It is not assumed projective,
  smooth, reduced, connected or geometrically integral. It need not have a
  rational point or a chosen section, and `H⁰(X, O_X) = k` is not assumed.
- Test schemes range over all objects of `Over S` with `S : Scheme.{u}`. These
  include nonreduced and non-quasi-compact schemes.
- Sections are all sections of the sheafification. These include sections with
  no global line-bundle representative on `T ×_S X`.
- No group structure, universal bundle, comparison isomorphism for universal
  global functions, or representability hypothesis is added.
- The values remain in `Type (u+1)`, and the statement has the single universe
  parameter `u`.

## Provenance

This is an internal geometric prerequisite. It is extracted from Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter VI §1.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (6.1), printed p.87 (PDF p.91), defines the relative Picard functor as
the fppf sheaf associated to the presheaf `T ↦ Pic(X ×_S T)`. The Library's
`RelativePicard.classSheaf` formalizes this sheaf; its parameter-first fibre
product agrees with the source's through the published `relativeSpaceSymmetry`.
Paragraph (6.3)(iii), printed p.89 (PDF p.93), states that for `S = Spec(k)` and
`f` proper this sheaf is representable by a scheme that is separated and locally
of finite type over `k`. The source attributes this to Murre, who uses a theorem
of Oort to reduce to reduced `X`. Worker 766 read PDF pp.91–93 and verified the
fingerprint.

The present proposition keeps only the algebraic-space content of (6.3)(iii): the
sheaf is an algebraic space, separated and locally of finite type over `k`. It
does not assert scheme representability. The full scheme statement is the
Library's `FieldPicardSheafRepresentabilityStatement`. Mathematically that scheme
theorem implies the present proposition. This implication is not proved here, and
it is not an available proof. The proposition is intended as an independent input
to a proof of the scheme theorem, so a proof of it must not assume that theorem.

The geometric predicates follow the registered Stacks Project snapshot
`stacks-group-algebraic-spaces-fields-2026-11-01`, directory SHA-256
`8d652c67cd0a05469ce5a92e9dd8eb8428b4911b43e6d6d6c8e2541f3361734f`:

- `02X3.html`, Definition 65.13.2: an algebraic space `F` over `S` is separated
  over `S` if its diagonal `F → F × F` is a closed immersion. Conjunct 2 states
  this. A closed immersion of algebraic spaces is a representable transformation
  whose represented scheme projections are closed immersions. This is the
  convention of the Library's `AlgebraicSpace.IsClosedImmersion`.
- `03XE.html`, Lemma 67.23.4, condition (6): a morphism `f : X → Y` of algebraic
  spaces is locally of finite type if and only if there are a scheme `U` and a
  surjective etale `φ : U → X` with `f ∘ φ` locally of finite type. With `Y = S`,
  the composite is the structure morphism `U.hom`. Conjunct 3 states this
  condition with the actual atlas `a`.

The definition of algebraic space in conjunct 1 is the Library's Stacks
fppf convention, documented in `AlgebraicSpace/Basic.md`. The retained Stacks
pages 02X3 and 03XE have no comments. The Library has no errata note for the
EVM draft or for this Stacks snapshot.

This file defines a proposition only and supplies no proof. A proof must
establish algebraicity, separatedness and the locally finite type atlas for the
actual sheaf in the full scope above. Any route through Artin's representability
criteria must also discharge its cohomological-flatness hypotheses and the
comparison with the actual fppf sheaf, without assuming `H⁰(X, O_X) = k`.
