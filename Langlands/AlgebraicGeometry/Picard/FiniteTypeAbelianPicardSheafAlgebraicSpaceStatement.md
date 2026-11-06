# The fppf Picard sheaf of an abelian scheme over a finite-type integer algebra as an algebraic space

Authors: Worker 59 and Worker 139.

Worker 139 specified the exact scope in the contract of task
`068c6e74-5b8e-47c6-ac61-4f979fa50e3d`. Worker 59 formalized it and wrote this
description.

## Statement

`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u}`
is a proposition. It quantifies over every commutative ring `R : Type u` with
`Algebra.FiniteType ℤ R` and over every
`A : Langlands.AbelianScheme (Spec (CommRingCat.of R))`. For each of these it
asserts the two conjuncts below and nothing else. Write `S` for
`Spec (CommRingCat.of R)`, `F` for the Library sheaf
`RelativePicard.classSheaf A.X.hom`, and
`F.obj = RelativePicard.classSheafPresheaf A.X.hom` for its underlying presheaf
`(Over S)ᵒᵖ ⥤ Type (u+1)`. Here `A.X : Over S` is the underlying scheme of the
abelian scheme, and `A.X.hom` is its structure morphism to `S`.

1. `AlgebraicSpace.IsAlgebraicSpace S F`. By the Library definition in
   `Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`, this says that the
   diagonal of `F.obj` is representable by actual schemes over `S`. It also says
   that there are an actual `U : Over S` and a natural transformation
   `a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ F.obj` with
   `AlgebraicSpace.IsEtale a` and `AlgebraicSpace.IsSurjective a`.
2. There exist an actual `U : Over S` and
   `a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ F.obj` with
   `AlgebraicSpace.IsEtale a`, `AlgebraicSpace.IsSurjective a` and
   `LocallyOfFinitePresentation U.hom`. The last condition is Mathlib's
   scheme-morphism property for the structure morphism `U.left ⟶ S`. This
   conjunct expresses that `F` is locally of finite presentation over `S` by an
   actual atlas. The atlas need not coincide with the one supplied by
   conjunct 1.

Both `AlgebraicSpace.IsEtale a` and `AlgebraicSpace.IsSurjective a` include
representability of `a` by actual schemes. For every actual `T : Over S` and
every map from the functor of points of `T` to `F.obj`, they require the
projection of every represented pullback square to be an etale, respectively
surjective, morphism of schemes. Surjectivity is therefore geometric
surjectivity of the represented projections. It does not mean surjectivity of
the presheaf map `a` at each test scheme.

Here `AlgebraicSpace.schemeYoneda S` is the Library's lifted Yoneda functor.
Its value on `U` at `T` is `ULift (T ⟶ U)`, valued in `Type (u+1)`.

## The actual sheaf and the scope

The definitions are imported unchanged from the Library.
`RelativePicard.classSheaf A.X.hom` is Mathlib's sheafification in
`Type (u+1)`, for `Scheme.fppfTopology.over S`, of the ordinary class presheaf
`RelativePicard.classPresheaf A.X.hom`. That presheaf sends a test scheme `T`
over `S` to the isomorphism classes of actual line bundles on the fibre product
`T ×_S A`, formed by the Library's `relativeSpace`. The sheaf's type
`Sheaf (Scheme.fppfTopology.over S) (Type (u+1))` is by definition the
Library's `AlgebraicSpace.FppfSheaf S`. Thus conjunct 1 is applied to the
published sheaf itself, with no replacement or conversion. The sheaf is not
assumed to be a scheme, and no rigidified or other substitute functor occurs.

- `R` is an arbitrary commutative ring of finite type over `ℤ`. It need not be
  reduced, a domain, regular or flat over `ℤ`.
- `A` is an arbitrary Library abelian scheme over `S`. This is an actual
  commutative group scheme whose structure morphism is smooth and proper with
  geometrically connected fibres. No polarization, projectivity, level
  structure or other extra datum is assumed.
- Test schemes range over all objects of `Over S` with `S : Scheme.{u}`. These
  include nonreduced and non-quasi-compact schemes. They are not restricted to
  affine, quasi-separated, reduced or geometric-point tests.
- Sections are all sections of the sheafification. No premise supplies a global
  line-bundle representative on `T ×_S A` for a section, and surjectivity of the
  sheafification unit `RelativePicard.toClassSheaf A.X.hom` is not assumed. For
  abelian schemes the unit section gives every section such a representative by
  Faltings–Chai (see Provenance). The statement neither uses nor asserts this,
  and its comparison with the exact Library sheaf is left to a proof.
- No geometric, cohomological-flatness, comparison, representer, projectivity
  or polarization hypothesis is added.
- The values remain in `Type (u+1)`, and the statement has the single universe
  parameter `u`.

## Provenance

This is an internal geometric prerequisite. It specializes Artin's
representability theorem for the relative Picard functor to actual abelian
schemes over affine bases of finite type over `ℤ`. None of the sources below
states this exact Lean proposition.

- M. Artin, *Algebraization of formal moduli I*, in Spencer and Iyanaga (eds.),
  *Global Analysis, Papers in Honor of K. Kodaira* (1969). Registered source
  `provided-4857ef34e92b785c08a5299e3cf7d7b54297d1fb2861e92e0925757aeeab6809`,
  SHA-256 `9fc1ce396aa1f62ebf41e67c1f644e0d4f54d885da5a049c9f22d2eefa36cb32`.
  Section 7, printed pp.66–67 (PDF pp.76–77), takes `f : X → S` flat and proper.
  Display (7.1) defines `Pic X/S` on `S' → S` as the global sections of
  `R¹f'_* G_m`, the derived direct image for the fppf topology. Display (7.2)
  defines cohomological flatness in dimension zero. Theorem 7.3, printed p.67
  (PDF p.77), states: if `f : X → S` is a proper, flat map of algebraic spaces
  which is finitely presented and cohomologically flat in dimension zero, then
  `Pic X/S` is represented by an algebraic space locally of finite
  presentation over `S`. Its proof first descends the data, etale locally on
  `S`, to an affine base of finite type over `Spec ℤ`. This is the base class of
  the present statement.
- M. Artin, *Versal deformations and algebraic stacks*, Inventiones
  mathematicae 27 (1974). Registered source
  `artin-1974-versal-deformations-algebraic-stacks`, SHA-256
  `9bf1a078bdfa3b3d3dbad8152e408238b2ce367692a0bc1957ed8c255f47ff35`.
  Appendix item 2, printed pp.186–187 (PDF pp.22–23), is the author's
  correction. The preliminary reduction on p.68 of the 1969 proof, to the base
  `Spec f_*O_X`, is incorrect because `X` need not be flat over that base; the
  1969 proof is complete only with this flatness as an extra hypothesis. The
  correction gives an alternative route. The Picard stack of invertible sheaves
  on `X ×_S S'` is algebraic by (5.3) of the 1974 paper, presented by a groupoid
  `P1 ⇉ P0`. `Pic X/S` is the etale sheaf associated to its isomorphism classes.
  Cohomological flatness makes the automorphism groups smooth, so
  `P1 ×_{P0×P0} P1` is a smooth equivalence relation on `P1`. Its quotient `P̄1`
  is an algebraic space, and `P̄1 ⇉ P0` is an equivalence relation defining
  `Pic X/S`. The uncorrected reduction must not be used.
- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990).
  Registered source
  `provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
  SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`.
  Chapter I, Definition 1.4 and Remark 1.5(a), printed p.2 (PDF p.14), treat
  the Picard functor of an abelian scheme. Remark 1.5(a) identifies
  `R¹f_{*fppf} G_m` with the fppf sheaf associated to `T ↦ Pic(X ×_S T)`, the
  sheaf formalized by `RelativePicard.classSheaf`. Since `X` has the unit
  section, the remark also identifies it with the functor of Definition 1.4(b),
  whose values on `T` are classes of line bundles on `X ×_S T` rigidified along
  the unit section. Printed p.3 (PDF p.15)
  recalls Artin's theorem: for `X` and the base locally of finite type over a
  field or an excellent Dedekind domain, `Pic(X/B)` is an algebraic space
  locally of finite presentation over the base. Here algebraic spaces are big
  etale sheaves with an etale scheme atlas. With `ℤ` as the excellent Dedekind
  domain, this is the abelian-scheme application that motivates the present
  specialization.

Worker 139 read these passages, including the correction, when designing the
scope. Worker 59 read the cited pages and verified the three fingerprints. No
source-specific errata were found in the checked project, Library or workspace
errata directories. The 1974 Appendix is the author's correction. The public
note `notes/abelian-schemes/relative-picard-source-map.md` records broader
source boundaries.

The locally finite presentation predicate follows the registered Stacks Project
snapshot `stacks-structural-atlas-geometry-2026-11-03`, directory SHA-256
`8c3f10b49df7e2195ce78f4f98c54e89277749fb3149aabdf3117023515f65da`.
`03XP.html`, Definition 67.28.1, defines local finite presentation of
morphisms of algebraic spaces. `03XO.html`, Lemma 67.28.4, condition (6),
states that `f : X → Y` is locally of finite presentation if and only if there
are a scheme `U` and a surjective etale `φ : U → X` with `f ∘ φ` locally of
finite presentation. With `Y = S` the composite is the structure morphism
`U.hom`, so conjunct 2 states this condition with an actual atlas `a`. The
two comments on 03XP fix a missing label; 03XO has no comments. The Library's
`AlgebraicSpace.StructuralAtlasGeometry` uses the same atlas expression for
bundled algebraic spaces; this statement writes it directly for the presheaf.

The definition of algebraic space in conjunct 1 is the Library's Stacks fppf
convention, documented in `AlgebraicSpace/Basic.md`.

## Future proof obligations

This file defines a proposition only and supplies no proof. A proof must
construct the algebraic-space structure and an etale surjective atlas locally of
finite presentation over `S` for the actual sheaf in the full scope above. In
particular it must:

- discharge Artin's hypotheses from the actual abelian-scheme and finite-type
  assumptions: properness, flatness and finite presentation of `A.X.hom`, and
  cohomological flatness in dimension zero;
- use the 1974 corrected route, or another correct argument, rather than the
  uncorrected reduction to `Spec f_*O_X`;
- prove the comparison of the source's object with the exact
  `RelativePicard.classSheaf A.X.hom`. The derived-functor description, the
  etale sheaf of classes, the ordinary relative Picard functor and the
  Library's fppf sheafification cannot be equated by citation. An etale/fppf
  comparison must supply the actual natural transformations and cover all
  sheaf sections;
- relate the sources' notion of algebraic space, an etale sheaf with an etale
  scheme atlas, to the Library's fppf convention in conjunct 1.

None of these is a premise of the present proposition.

## Non-scope and preserved workflows

This proposition does not state separatedness of the diagonal, a Picard-zero
group space, properness or smoothness of a zero part, scheme representability,
a Poincaré family, or classification by the Library's smooth-family predicate.
These remain separate obligations of the finite-type consumer, Worker 139's
proof task `90a7704e-771a-4107-a91a-c67873dd035e`, whose final target is
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`.
The general-base final assembly remains with task
`e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`.

This file changes no ownership. The field Picard, Picard-stack atlas,
topology-comparison, ordinary/rigidified comparison, global-functions,
smooth-relation quotient and smooth-family workflows named in the task context
keep their current owners and scopes.
