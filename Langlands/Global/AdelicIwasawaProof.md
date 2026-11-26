# Actual adelic parabolic Iwasawa existence: proof

Lean module: `Langlands.Global.AdelicIwasawaProof`.

## Statement

```
theorem Langlands.Global.AdelicGroupPoints.parabolicIwasawaStatement :
    Langlands.Global.AdelicGroupPoints.ParabolicIwasawaStatement.{u}
```

The type is exactly the published proposition of the module
`Langlands.Global.AdelicIwasawaStatement`, at an arbitrary universe `u`, with
no further hypothesis. It applies to every number field `F : Type u`, every
group scheme `G` over `Spec F` with `IsConnectedReductive G`, and every
morphism `p : P ⟶ G` with `IsParabolicSubgroup p`. For each of these it
gives a subgroup `K` of `AdelicGroupPoints F G` with
`IsParabolicIwasawaCompact F G P p K`. Here `AdelicGroupPoints F G` is the
group of actual points of `G` over the full adele ring `AdeleRing (𝓞 F) F`.
The subgroup has three properties:

1. `K` is compact in the existing topology of `AdelicGroupPoints F G`. This
   topology (`affinePointsTopologicalSpace`) is induced by evaluating all
   global regular functions of `G` in the adele ring.
2. Every compact subgroup of `AdelicGroupPoints F G` containing `K` equals
   `K`. This is maximality among all compact subgroups, with no restriction
   to open or model-defined subgroups.
3. `Set.range (AdelicGroupPoints.map F P G p) * (K : Set _) = Set.univ`.
   Here `AdelicGroupPoints.map F P G p` is the existing continuous
   homomorphism induced by `p` on adelic points. The parabolic factor is on
   the left and `K` on the right, as in Getz–Hahn's equation (2.24).

All parabolics are covered, including the improper parabolic `p = 𝟙 G`.
No splitness or isotropy is assumed, so non-split and anisotropic groups are
included. The subgroup `K` is constructed after `F`, `G` and `p`; it is not
supplied.

## Proof

The proof is a single application of the published conditional reduction
`AdelicGroupPoints.parabolicIwasawaStatement_of_archimedean_finite_integral`
(module `Langlands.Global.AdelicIwasawaReduction`). Each of its three
hypotheses is replaced by the published theorem proving it:

- `InfinitePlaceGroupPoints.parabolicIwasawaStatement`
  (module `Langlands.Global.InfinitePlaceIwasawaProof`) gives local
  existence at every infinite place;
- `FinitePlaceGroupPoints.parabolicIwasawaStatement`
  (module `Langlands.Global.FinitePlaceIwasawaProof`) gives local existence
  at every finite place;
- `IntegralIwasawaFamily.existenceStatement`
  (module `Langlands.Global.IntegralIwasawaFamilyProof`) gives the
  almost-everywhere integral family.

No new hypothesis is introduced and no proof step is added. The structure
behind the composition is as follows.

### Assembly on actual adelic points

The reduction fixes `F`, `G` and `p`. Connected reductivity makes the
structure morphism of `G` affine, so `G.X.left` is affine by
`isAffine_of_isAffineHom`. Parabolicity makes `p` a closed immersion, so
`P.X.left` is affine as well. The integral-family theorem gives a family
`K v` of subgroups of the finite-place point groups, satisfying
`IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p K`. A case split on
`Place F` gives local existence at every place: the archimedean theorem at
infinite places, the finite-place theorem at finite places. Both are in the
form `CoordinateCompactPatching.IsLocalIwasawaCompact`, that is, local
compactness, maximality among all compact subgroups and literal
parabolic-left covering. The reduction then applies
`AdelicGroupPoints.exists_parabolicIwasawaCompact_of_local_integral` (module
`Langlands.Global.AdelicIwasawaAssembly`).

That assembly theorem extends the finite family to all places by the full
group at the infinite places (`extendFinite`). The integral family is good at
all but finitely many finite places, and there are finitely many infinite
places. So the extended family is good at all but finitely many places.
`CoordinateCompactPatching.exists_compact_maximal_cover_of_ae_local` replaces
the finitely many bad members by local Iwasawa subgroups from the local
existence theorems. It then forms the coordinate subgroup of adelic points
whose coordinate at each place lies in the patched local subgroup. The
topological inputs are the following actual adelic facts, all from
`Langlands.Global.AdelicGroupLocalPoints`:

- the place projections `atPlace` are continuous homomorphisms;
- they separate points (`ext_atPlace`);
- they are natural for the parabolic map;
- every adelic point lies in the family at almost every place;
- finitely supported families of local parabolic points lift to adelic
  parabolic points.

Uniform integrality of regular functions survives finite changes of the
family. Through `IsUniformlyIntegral.compactProductLift` it gives a
continuous map from the full product of the local subgroups onto the
coordinate subgroup. The local subgroups are compact, so the product is
compact by Tychonoff. Its continuous image, the coordinate subgroup, is
therefore compact.

Maximality follows by projection. A compact overgroup projects at each
place to a compact overgroup of the local subgroup, which local maximality
makes equal to the local subgroup. Covering holds because each adelic point
needs a parabolic correction at only finitely many places. The correction
lifts to an actual adelic parabolic point, and the remaining factor lies in
the coordinate subgroup.

### The local and integral inputs

At an infinite place `v`, the archimedean theorem passes to the pullback of
`G` to the completion `v.Completion`. There it uses a self-adjoint closed
matrix realization of the connected reductive group. The parabolic becomes a
dynamic parabolic of a cocharacter defined over the completion. The polar
Iwasawa decomposition `MatrixRepresentation.affineDynamicIwasawa` then gives
a compact subgroup, maximal among compact subgroups, whose product with the
parabolic points is the whole group.

At a finite place `v`, the finite-place theorem passes to the pullback of `G`
to the nonarchimedean local field `FiniteCompletion F v`. There it takes the
norm-one stabilizer of a special point of the Bruhat–Tits building, from the
published building construction. Maximality among compact subgroups comes
from the bounded-orbit fixed point in the complete nonpositively curved
metric of the building. Covering comes from the chamber Iwasawa decomposition
of the relative Tits system, Weyl representatives in the special parahoric,
and rational conjugacy of minimal parabolics.

The integral family comes from simultaneous good reductive and parabolic
integral models over a ring of `S`-integers. At almost every finite place its
member is the image of the model's integral points. The integral-model
maximality theorem `IntegralModel.maximalCompactStatement` gives maximality.
Covering comes from the proper relative parabolic quotient and integral
torsor lifting. Finite coordinate and denominator arguments give absorption
of adelic points and uniform integrality of regular functions.

The companions of the four cited modules describe these proofs in full. This
module uses each of them only through the exact published proposition it
proves.

## Route and sources

The target is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §2.7, Theorem 2.7.1 and equation (2.24), printed p.71, in the
number-field case. The source refers to its Appendix B for a proof sketch.
The implemented route follows that sketch's division into local results at
every place and an integral family at almost every place: Theorem B.2.5,
Proposition B.3.1 and §B.4, printed pp.543–548. The local proofs differ from
the source in the ways their own companions record. Registered source:
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
five-page October 2026 author errata, `getz-hahn-2024-errata-2026-10`,
SHA-256 `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
contains no correction to Theorem 2.7.1, equation (2.24) or these Appendix B
passages.

The theorem proves only the existence statement above. It does not identify
`K` with a standard compact subgroup or with the compact data of
`AdelicSiegelFactors`. It does not prove Siegel-set coverage, finite volume
or the Levi-intersection properties of the source's Appendix B.

## Verification

A Lake build of the module reports no errors or warnings. The declaration
check of `Langlands.Global.AdelicGroupPoints.parabolicIwasawaStatement`
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.
