# Local finite presentation of a universal smooth-family parameter

`Langlands.AbelianScheme.SmoothFamilyFinitePresentationStatement.{u}` is a
proposition definition. It is not a proof, and no axiom is introduced.
For every `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, every
`A : AbelianScheme S`, every actual `P : Over S` and every actual
`L : RigidifiedFamily A P`, it asserts

```text
IsUniversalSmoothFamilyOnQuasiSeparatedTests A L →
  LocallyOfFinitePresentation P.hom
```

that is, if the specified rigidified family `L` on the specified parameter
`P` is universal for smooth-family algebraically trivial rigidified classes on
quasi-separated tests, then the structure morphism `P.hom : P.left ⟶ S` is
locally of finite presentation. `LocallyOfFinitePresentation` is Mathlib's
morphism property. The declaration is universe-polymorphic in `u`.

The hypothesis is imported by its Lean name from
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement`
and is neither redefined nor replaced. It is the conjunction of
`IsAlgebraicallyTrivialFamilyViaSmoothFamily A L` and the requirement that,
for every `T : Over S` with `[QuasiSeparatedSpace T.left]` and every
`q : AlgebraicallyTrivialClassesViaSmoothFamily A T`, there is exactly one
`h : T ⟶ P` with
`RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
(unitSection_comp A) L T h = q.val`. Every quasi-separated test in universe
`u` is included, including nonreduced tests. The fibre predicate tests every
algebraically closed field-valued point `Spec K ⟶ P.left` with `K : Type u`
and uses actual smooth separated finite-type geometrically integral
parameter schemes, line bundles and endpoint isomorphisms; it is defined in
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality`.

The statement makes no assumption on `P.left`: it is not assumed
quasi-separated, separated, quasi-compact or of finite type, since the
geometry of an abstractly given universal parameter is not yet known.
There is no existence, projectivity, polarization, noetherian, reducedness,
ordinary-Picard-representability, existing-dual, global-functions,
normalization, coherence, pullback-stability or other geometric hypothesis.
The statement does not assert that such a pair `(P, L)` exists; existence
is the separate proposition
`SmoothFamilyQuasiSeparatedRepresentabilityStatement` in the imported
module, which is not assumed here.

## Original sources and conventions

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
The following passages were read:

- The conventions, printed p.xxvi/PDF p.26, take schemes to be
  quasi-separated preschemes; this is why the base hypothesis is kept and
  the tests of the imported predicate are quasi-separated.
- Definition 1.3.1.1, printed p.67/PDF p.95, defines an abelian scheme as a
  proper smooth group scheme with geometrically connected fibres.
  Remark 1.3.1.2(1) on the same page notes that smoothness implies local
  finite presentation.
- Definition 1.3.2.1, printed p.73/PDF p.101, defines `Pic(A/S)` as the
  quotient of invertible sheaves on `A ×_S T` by those pulled back from `T`,
  and `Pic⁰(A/S)` by algebraic equivalence to zero of the fibre `L_t` over
  `A_t` for every `t ∈ T`.
- Lemma 1.3.2.2, printed pp.73–74/PDF pp.101–102, identifies these
  functors with the rigidified functors `Pic_e(A/S)` and `Pic⁰_e(A/S)` of
  isomorphism classes of invertible sheaves on `A_T` rigidified along `e_T`.
- Theorem 1.3.2.3, printed p.74/PDF p.102, states that for every abelian
  scheme `A → S`, `Pic⁰_e(A/S)` is representable by an abelian scheme `A∨`
  over `S`, referring to Faltings–Chai, Ch. I, §1 for the proof.
  Remark 1.3.2.4 on the same page notes that the locally projective case
  follows from Hilbert schemes; the present statement uses the unrestricted
  scope of the theorem, not that restricted route. Definition 1.3.2.5 names
  the universal rigidified Poincaré sheaf on `A ×_S A∨`.

The author's errata of March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
retained as
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`,
were read at PDF pp.1 and 8–9. Page 1 replaces the separated-scheme
convention by quasi-separatedness and directs readers to the revision.
Page 8 corrects Definition 1.3.2.1 so that the quotient bundles come from
`T`; the revision cited above incorporates this. No source-specific errata
note was present in the checked project, Library or workspace notes.

The imported smooth-family fibre predicate is motivated by Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Remark (6.9), printed p.91/PDF p.95, defines algebraic equivalence of
divisors over an algebraically closed field through a smooth parameter
variety, and Section (7.24), printed p.107/PDF p.111, defines algebraic
equivalence of line bundles through the Néron–Severi group and states that
it can be tested over an algebraic closure, where it agrees with
Remark (6.9). These passages are used here only to explain why a
comparison with Lan's fibre condition is needed.

## Derived status

This is a derived proposition, not a verbatim statement from Lan and not a
proved theorem. Lan's theorem concerns the functor `Pic⁰_e(A/S)` with
algebraic equivalence on ordinary residue-field fibres and source product
order `A ×_S T`. The hypothesis here instead concerns an arbitrary actual
pair `(P, L)` that is universal for the Library's geometric-fibre
smooth-family predicate, with the Library order `T ×_S A`, only on
quasi-separated tests. Neither the existing representability proposition
nor any comparison of these functors is proved or assumed by this module.

## Intended proof route and remaining obligations

A future exact proof is expected to proceed as follows; none of these
steps is implemented here, and none is added as a hypothesis.

1. Construct, or reuse after its own acceptance and publication, an actual
   abelian scheme `B` over `S` with an actual rigidified family on `B`
   that represents Lan's rigidified Picard-zero functor on quasi-separated
   tests, as in Theorem 1.3.2.3.
2. Prove that, on actual rigidified families over quasi-separated tests,
   Lan's condition agrees with the imported smooth-family condition, so
   that the family on `B` is universal in the sense of
   `IsUniversalSmoothFamilyOnQuasiSeparatedTests`. This requires comparing
   ordinary residue-field algebraic equivalence with the condition after
   every algebraically closed field-valued point, the explicit
   smooth-family witnesses with divisor or Néron–Severi algebraic
   equivalence, the ordinary quotient by bundles from `T` with actual
   rigidified representatives (normalization of rigidifications), and the
   source product order with the Library order, all compatibly with actual
   pullbacks. Stability of the smooth-family class subtype under the
   pullbacks used below is also required.
3. Recover an isomorphism `P ≅ B` over `S` compatible with the given `L`.
   Since `P.left` need not be quasi-separated, `P` itself is not a
   permitted test, so the Yoneda argument cannot be applied directly.
   Instead, restrict `L` to affine opens of `P.left`, which are
   quasi-separated tests, classify them into `B`, and glue the resulting
   maps using uniqueness on overlaps. Since `B ⟶ S` is separated and `S`
   is quasi-separated, `B` is a permitted test, and classifying the family
   on `B` gives a map `B ⟶ P`. Uniqueness
   of classifying maps, together with the existing
   `RigidifiedLineBundle.classifyingMap_comp` and
   `RigidifiedLineBundle.classifyingMap_id`, should show that the two maps
   are mutually inverse, the composite on `P` being checked on an affine
   open cover. The comparison must retain the given actual family `L`
   throughout.
4. Since `B ⟶ S` is smooth, it is locally of finite presentation, and this
   transports along the isomorphism to `P.hom`.

The existing proposition `SmoothFamilyQuasiSeparatedRepresentabilityStatement`
only asserts existence of some universal pair and supplies no geometry of
the parameter, so it does not prove this statement. An equality or
bijection of geometric-point sets between `P` and `B` also does not
suffice: it does not identify the functors on nonreduced tests and does
not give an isomorphism of schemes. The proof must not use the chosen-dual
target `RelativeDualSchemeFinitePresentationStatement`, whose proof is
intended to consume this result, or the relative dual geometry target
`RelativeDualSchemeGeometryStatement`, which consumes that chosen-dual
result; the translation-invariance comparison
`SmoothFamilyPicardZeroComparisonStatement` and the all-test extension
`PicardZeroQuasiSeparatedExtensionStatement` are separately stated
propositions that are not imported here.
