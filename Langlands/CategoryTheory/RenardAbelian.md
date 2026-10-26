# Renard's seven abelian-category axioms

This construction unit represents Renard 2026 A.VI.1, printed page 261 / PDF
page 267, and obtains the additive Hom structure in A.VI.2(6), printed page
262 / PDF page 268, by reusing Mathlib's nonpreadditive construction.
The short equivalences and compatibility laws are intrinsic consequences of
the interface, rather than separately assumed source results.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both PDF267 and PDF268 were read; the seven-axiom list on PDF267 was also
visually inspected. The neighboring 2020 edition is not used.

The author's [books page](https://perso.pages.math.cnrs.fr/users/david.renard/)
was checked on 26 October 2026. Its book section links the corrected French
2026 edition and separately labels the errata for the 2010 edition; it has no
separate 2026 errata link in that section. The already registered snapshot
`renard-author-page-2026-10-26` retains this navigation evidence. The appendix
portion PDF18–19 of registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read and gives no correction to these seven axioms or the additive Hom
assertion. This is a limited check of that portion, not an exhaustive errata
claim.

## Source interface

All declarations are in `Langlands.Renard`, over `C : Type u` and
`Category.{v} C`, with independent object and Hom universes. No smallness,
finite-dimensionality, generator, completeness or cocompleteness hypothesis
is imposed.

`AbelianAxiomsWithZero C z : Prop` exposes the following seven conjuncts in
source order, with the fixed data `z : HasZeroMorphisms C` used for every
zero-dependent conjunct:

| Renard axiom | Lean conjunct | Meaning |
| --- | --- | --- |
| AB0 | `HasZeroObject C` | An object is both initial and terminal. |
| AB1 | `HasFiniteProducts C` | All finite discrete diagrams have limits, including the empty product. |
| AB1* | `HasFiniteCoproducts C` | All finite discrete diagrams have colimits, including the empty coproduct. |
| AB2 | `HasKernels C` | Every morphism has an actual categorical kernel, expressed by existence of its limiting kernel fork. |
| AB2* | `HasCokernels C` | Every morphism has an actual categorical cokernel, expressed by existence of its colimiting cokernel cofork. |
| AB3 | `IsNormalMonoCategory C` | For every mono `f`, there exists `NormalMono f`: a target object, a map `g`, the equation `f ≫ g = 0`, and an `IsLimit` witness for the kernel fork with leg `f`. |
| AB3* | `IsNormalEpiCategory C` | For every epi `f`, there exists `NormalEpi f`: a source object, a map `g`, the equation `g ≫ f = 0`, and an `IsColimit` witness for the cokernel cofork with leg `f`. |

These seven classes are propositions. In contrast, `HasZeroMorphisms`,
`NonPreadditiveAbelian`, `Abelian`, `Preadditive`, `NormalMono`, `NormalEpi`,
`IsLimit` and `IsColimit` carry data. `AbelianAxioms C : Prop` therefore uses
an existential over zero-morphism data. The existence comparisons with
`NonPreadditiveAbelian C` and `Abelian C` use `Nonempty`.
Neither source predicate takes a preadditive or abelian structure as input.
The fixed-data `normalMono` and `normalEpi` accessors select actual universal
property witnesses from the final two conjuncts, using Mathlib's choice
accessors. They retain the supplied category, morphism and zero data.

## Zero morphisms and compatibility

The extra existential packages necessary Lean data without adding an eighth
mathematical axiom. AB0 constructs the zero `X → Y` as the composite through a
zero object. Mathlib's `HasZeroObject.zeroMorphismsOfZeroObject` implements this;
`nonempty_zeroMorphisms_of_zeroObject` records its existence. Initiality and
terminality give the two annihilation laws.

No global zero-morphism instance is introduced here. Mathlib explicitly warns
that the zero-object construction can differ definitionally from an ambient
choice, so users should retain their ambient zeros. Its
`HasZeroMorphisms.ext` proves that all compatible zero structures are equal,
and supplies `Subsingleton (HasZeroMorphisms C)`.
`zeroMorphismsOfZeroObject_eq` applies this uniqueness to the construction.
`abelianAxiomsWithZero_iff` transports the full seven-component proposition
between zero choices by equality, and `abelianAxioms_iff_withZero` unpacks the
existential using any ambient zero structure. Thus kernel and normality
universal properties can be used with the original zeros.

The fixed-data constructor retains its zero structure definitionally, as
`AbelianAxiomsWithZero.nonPreadditiveAbelian_zero` shows.
`AbelianAxioms.homGroup_zero` also proves that the neutral element of the
constructed additive group agrees with any ambient categorical zero.
These are proved equalities, not claims of definitional equality between
arbitrary existing instances.

## Construction and intrinsic laws

`AbelianAxiomsWithZero.nonPreadditiveAbelian` fills all fields of the actual
Mathlib structure using the seven conjuncts and the supplied zero data.
`AbelianAxiomsWithZero.ofNonPreadditiveAbelian` reads those fields back.
Their wrapping law is proof irrelevance for the seven-property proposition;
it does not claim equality of arbitrary selected normal-morphism witnesses.
`AbelianAxioms.nonPreadditiveAbelian` selects the existential witness and
applies the fixed-data constructor. Its reverse packaging operation and
wrapping law give `abelianAxioms_iff_nonempty_nonPreadditiveAbelian`.

`AbelianAxioms.preadditive` calls
`CategoryTheory.NonPreadditiveAbelian.preadditive`.
`AbelianAxioms.abelian` calls
`CategoryTheory.NonPreadditiveAbelian.abelian`, whose preadditive field is
precisely that construction, as `abelian_toPreadditive` records.
`AbelianAxioms.ofAbelian` calls
`CategoryTheory.Abelian.nonPreadditiveAbelian` and packages its fields.
Together these give `abelianAxioms_iff_nonempty_abelian`. An ordinary ambient
`[Abelian C]` can enter directly through `ofAbelian`; no replacement category,
object wrapper or altered morphism type is involved.

The compatibility law `AbelianAxioms.preadditive_eq` uses Mathlib's
`subsingleton_preadditive_of_hasBinaryBiproducts`: the newly constructed
abelian category has binary biproducts, so its preadditive structure agrees
with every ambient preadditive structure on the same category. This is an
intrinsic uniqueness consequence, not an additional source hypothesis.

## A.VI.2(6) and attribution

Mathlib at commit `5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`, implements the substantive
proof, by Markus Himmel (Apache 2.0). Its full source was read for this unit.
After developing images/coimages and normality consequences, it constructs a
subtraction morphism using the cokernel of the diagonal `A → A × A`. It defines
subtraction on morphisms from this map, negation from subtraction from zero,
and addition from subtraction of a negative. The proved identities supply
additive commutative groups and bilinearity of composition.
This unit reuses that implementation; it does not supply a new proof of the
substantial construction or assume an additive structure to obtain it.

`AbelianAxioms.homGroup h X Y` exposes the resulting actual
`AddCommGroup (X ⟶ Y)`, with addition, zero, negatives and their laws.
The `add_comp` and `comp_add` accessors specialize the corresponding two fields
of the constructed `Preadditive C` structure. Their conclusion explicitly uses
that structure. Along with `homGroup_zero`, these implement exactly the Hom
group and distributivity assertion A.VI.2(6).

Other reused source definitions, whose full types were inspected, are in
`Abelian/Basic.lean`, `Preadditive/Basic.lean`,
`Preadditive/Biproducts.lean`, and
`Limits/Shapes/{FiniteProducts,Kernels,ZeroObjects,ZeroMorphisms}.lean`
and `Limits/Shapes/NormalMono/Basic.lean`. The short proofs here assemble and
project fields, use proof irrelevance, transport equal zero data, and apply
Mathlib's conversion and uniqueness constructions.

## Scope

This unit covers the seven-axiom bridge and A.VI.2(6) only. It does not
formalize the false subquotient-closure claim preceding AB0; that claim has a
separate correction and task. Module and sheaf examples, the other A.VI.2
properties, and the later AB4/AB4*, AB5/Grothendieck and AB6 conventions remain
outside this construction.
