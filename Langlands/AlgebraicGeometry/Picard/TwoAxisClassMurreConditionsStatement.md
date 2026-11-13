# Murre's conditions for the two-axis class presheaf over noetherian affine bases

Module `Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement`
defines eleven `Prop`-valued statements, all in the namespace
`Langlands.AlgebraicGeometry.Picard`. It proves nothing.

## Exact statements

Each of the first ten statements has the form

```
∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
  (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
  UnramifiedFunctor.<Condition> (TwoAxisRigidifiedLineBundle.classPresheaf A)
```

where `<Condition>` is one of the conditions defined in the module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`, for
`S = Spec R` and `F = classPresheaf A : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)`.

| Statement | Condition | Murre |
| --- | --- | --- |
| `NoetherianTwoAxisClassSmallValuesStatement` | `SmallValues` | values are sets of the test universe |
| `NoetherianTwoAxisClassZariskiSheafStatement` | `ZariskiSheaf` | (F1a) |
| `NoetherianTwoAxisClassFaithfullyFlatSheafStatement` | `FaithfullyFlatSheaf` | (F1b) |
| `NoetherianTwoAxisClassFilteredColimitsStatement` | `FilteredColimits` | (F2) |
| `NoetherianTwoAxisClassAdicLimitsStatement` | `AdicLimits` | (F3) |
| `NoetherianTwoAxisClassArtinianLiftingStatement` | `ArtinianLifting` | (F4′) |
| `NoetherianTwoAxisClassNilpotentInjectiveStatement` | `NilpotentInjective` | strong (F5), local artinian rings |
| `NoetherianTwoAxisClassValuativeSeparationStatement` | `ValuativeSeparation` | (F6) |
| `NoetherianTwoAxisClassOneDimensionalLiftingStatement` | `OneDimensionalLifting` | (F7) |
| `NoetherianTwoAxisClassGenericNonLiftingStatement` | `GenericNonLifting` | (F8) |

The closing statement `NoetherianTwoAxisClassMurreConditionsStatement` is the
conjunction of these ten statements, in the order of the table.

In words, for every abelian scheme over the spectrum of a noetherian ring:

- every value of the class presheaf is `u`-small;
- it is a sheaf for Zariski open covers and for single flat, surjective,
  quasi-compact morphisms of test objects;
- on algebras over an affine open of `Spec R` it turns filtered colimits of
  algebras into colimits of sets;
- over a complete local noetherian ring `B`, classes over `Spec B` correspond
  bijectively to compatible families of classes over the `Spec (B/mⁿ)`;
- over local artinian rings it satisfies Murre's lifting condition (F4′), and
  restriction to a nilpotent thickening is injective;
- over a discrete valuation ring, restriction to the generic point is
  injective;
- it satisfies Murre's lifting conditions (F7) and (F8).

The precise meaning of each condition is in `MurreCriterionStatement.md`.

`classPresheaf A` is the published presheaf of the module
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf`. Its value
at a test object `T` is the set of isomorphism classes of actual line bundles on
the self-product of the base change `abelian A T`, with module-sheaf
trivializations along the two unit axes `(id, e)` and `(e, id)` that are
compatible at the unit. Isomorphisms must respect both trivializations.
Restriction is the published compatible pullback `classesPullback`. The test
objects are all of `Over (Spec R)`, including nonreduced and non-noetherian
schemes.

## Source

The statements are derived. They specialize the conditions of Murre's
criterion to the functor of divisorial correspondences of an abelian scheme
with itself, as in the proof of Raynaud's Theorem III 4.4.

- M. Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
  homogènes*, LNM 119 (1970), registered as
  `provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`
  (SHA-256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`).
  Printed page `p` is PDF page `p + 4`.
  - Theorem III 4.4, printed p.53: for proper, flat, finitely presented `X, Y`
    over `S` with `u*(O_X) = O_S` and `v*(O_Y) = O_S` universally, `Corr_S(X, Y)`
    is representable by an `S`-group scheme locally of finite presentation,
    separated and unramified. Its proof reduces to a noetherian affine `S` and
    concludes from III 4.3 and from Murre's Theorem 4 ([16 bis] théorème 4).
  - Proposition III 4.1, printed p.49: `Corr_S(X, Y)` is formally unramified
    (EGA IV 17.1.1). This includes injectivity of restriction to nilpotent
    thickenings of affine test schemes, hence `NilpotentInjective`.
  - Proposition III 4.3, printed p.51: `Corr_S(X, Y)` satisfies the valuative
    criterion of separation: for every trait `(T, s, t)` over `S`, the map
    `Corr_S(X, Y)(T) → Corr_S(X, Y)(t)` is injective. This is
    `ValuativeSeparation`.
- J. P. Murre, *Representation of unramified functors. Applications*,
  Séminaire Bourbaki exp. 294, registered as
  `murre-1965-bourbaki-294-unramified-functors`
  (SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`.
  - Definition of `Corr_S(X, Y)` by line bundles on `X' ×_{S'} Y'` with
    trivializations on `e_{X'} ×_{S'} Y'` and `X' ×_{S'} e_{Y'}` agreeing on
    `e_{X'} ×_{S'} e_{Y'}`: printed pp.255–256 (PDF pp.14–15).
  - Theorem 4 and its Corollary 1, printed p.256 (PDF p.15): for `S` locally
    noetherian and `X, Y` proper and flat with `k(s) ≅ H⁰` on the fibres,
    a separated `Corr_S(X, Y)` is representable by an unramified `S`-scheme
    locally of finite type; `Corr_S(A, B)` is representable for abelian
    schemes `A, B`.
  - Indications of proof, printed pp.256–258 (PDF pp.15–17): (F1)–(F4)
    follow from the same properties of `Pic_{X ×_S Y / S}`; non-ramification
    from the lemma on `R¹`; (F7) and (F8) by the obstruction argument in
    `H²(X ×_S Y, O ⊗ I)`; separation when `X` has geometrically integral
    fibres.

Theorem III 4.4 and Murre's Theorem 4 concern `Corr_S(X, Y)`, a functor of
classes of rigidifiable line bundles. The Library presheaf is the rigidified
class presheaf with `X = Y = A` and `e = f` the unit section. Identifying the
two is part of the proof obligation of these statements and is not assumed.
An abelian scheme is smooth and proper, hence flat and of finite presentation,
and has geometrically integral fibres. "Noetherian ring" matches the noetherian
affine reduction in the proof of III 4.4.

`SmallValues` has no counterpart in the sources: Murre's functors take values
in sets of the same universe as the schemes, while `classPresheaf A` takes
values in `Type (u + 1)`. The criterion statement requires it; see
`MurreCriterionStatement.md`.

## Use

`TwoAxisClassMurreReduction` proves that Murre's criterion
`UnramifiedFunctor.MurreCriterionStatement.{u, u + 1}` together with these ten
statements implies the published
`NoetherianTwoAxisClassRepresentabilityStatement`. None of the statements is
proved here.
