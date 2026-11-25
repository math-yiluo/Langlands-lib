module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Properties of unramified morphisms

An unramified morphism of schemes is equivalently a locally finite type, formally unramified
morphism, and a G-unramified morphism is equivalently a locally finitely presented, formally
unramified one. Both classes are stable under composition and under arbitrary base change, and
both descend from a composite to its first factor, G-unramifiedness under the additional
assumption that the second factor is locally of finite type. A morphism unramified at a point is
quasi-finite there; an unramified morphism is locally of finite type and locally quasi-finite, and
its residue field extensions are finite separable.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` and
  `AlgebraicGeometry.gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified`
  characterize the two classes by a finiteness condition together with formal unramifiedness.
* `AlgebraicGeometry.unramified_isStableUnderComposition` and
  `AlgebraicGeometry.gUnramified_isStableUnderComposition` give stability under composition.
* `AlgebraicGeometry.unramified_isStableUnderBaseChange` and
  `AlgebraicGeometry.gUnramified_isStableUnderBaseChange` give stability under base change.
* `AlgebraicGeometry.unramified_of_comp` descends unramifiedness to the first factor, and
  `AlgebraicGeometry.gUnramified_of_comp` does the same for G-unramifiedness when the second
  factor is locally of finite type.
* `AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt` is the pointwise finiteness consequence, and
  `AlgebraicGeometry.locallyOfFiniteType_of_unramified` and
  `AlgebraicGeometry.locallyQuasiFinite_of_unramified` are the two global ones.
* `AlgebraicGeometry.finite_residueField_of_unramified` and
  `AlgebraicGeometry.isSeparable_residueField_of_unramified` describe the residue field
  extensions.

## Implementation notes

Stability under composition and under base change are transported from the corresponding
properties of ring homomorphisms along the `AlgebraicGeometry.HasRingHomProperty` instances
established with the locality of the two classes, so the conjunctive form of each class is set up
once rather than at each use. The two descent statements along a composite are proved through
that conjunctive form as well: the formal half is Mathlib's
`AlgebraicGeometry.FormallyUnramified.of_comp` in both cases, while the finiteness half is
`AlgebraicGeometry.locallyOfFiniteType_of_comp` for the unramified case and
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp` for the G-unramified one, the latter
being exactly where the finite-type hypothesis on the second factor is consumed.

Local quasi-finiteness of an unramified morphism uses that an unramified algebra is quasi-finite:
`Algebra.Unramified.finiteType` gives essential finite type and
`Algebra.Unramified.formallyUnramified` the formal condition, and Mathlib's quasi-finiteness
instance concludes.

The pointwise statement concludes `AlgebraicGeometry.quasiFiniteAt`, which is finite type at the
point together with quasi-finiteness of the stalk map, Mathlib's
`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` omitting the finite-type condition. Both halves come
from the single affine chart that witnesses unramifiedness at the point, so that no global
finiteness hypothesis is required: the chart's map of sections is of finite type, which is the
first half directly, and `AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso` identifies the stalk
map with the local homomorphism that map of sections induces, along which
`RingHom.HoldsForLocalization.localRingHom` transports essential finite type and formal
unramifiedness.

The residue field statements record the finite and the separable half of "finite separable"
separately, with the algebra structure on `κ(x)` induced by the canonical residue field map
`κ(f(x)) → κ(x)`.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02G9](https://stacks.math.columbia.edu/tag/02G9)
* [Stacks Project, Tag 02GA](https://stacks.math.columbia.edu/tag/02GA)
* [Stacks Project, Tag 02GG](https://stacks.math.columbia.edu/tag/02GG)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 02V5](https://stacks.math.columbia.edu/tag/02V5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

private lemma algebraUnramified_iff_ringHom {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) :
    letI : Algebra R T := g.toAlgebra
    Algebra.Unramified R T ↔ (g.FiniteType ∧ g.FormallyUnramified) := by
  let : Algebra R T := g.toAlgebra
  change Algebra.Unramified R T ↔
    (RingHom.FiniteType (algebraMap R T) ∧ RingHom.FormallyUnramified (algebraMap R T))
  rw [RingHom.finiteType_algebraMap, RingHom.formallyUnramified_algebraMap]
  exact ⟨fun h => ⟨h.finiteType, h.formallyUnramified⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A property of ring homomorphisms that splits as a conjunction with formal unramifiedness holds
on all `appLE` maps of a morphism if and only if each conjunct does, as in `locallyOfFiniteType_iff`
and `formallyUnramified_iff`. -/
private lemma forall_appLE_iff_and
    {A B : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    (h : ∀ {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T),
      A g ↔ (B g ∧ g.FormallyUnramified))
    (f : X ⟶ S) :
    (∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V → ∀ (e : U ≤ f ⁻¹ᵁ V),
      A (f.appLE V U e).hom) ↔
    ((∀ {V : S.Opens}, IsAffineOpen V → ∀ {U : X.Opens}, IsAffineOpen U → ∀ (e : U ≤ f ⁻¹ᵁ V),
      B (f.appLE V U e).hom) ∧
    (∀ {V : S.Opens}, IsAffineOpen V → ∀ {U : X.Opens}, IsAffineOpen U → ∀ (e : U ≤ f ⁻¹ᵁ V),
      (f.appLE V U e).hom.FormallyUnramified)) := by
  refine ⟨fun H => ⟨fun {V} hV {U} hU e => ((h _).mp (H U hU V hV e)).1,
    fun {V} hV {U} hU e => ((h _).mp (H U hU V hV e)).2⟩, ?_⟩
  rintro ⟨hB, hform⟩ U hU V hV e
  exact (h _).mpr ⟨hB hV hU e, hform hV hU e⟩

/-- A morphism of schemes is unramified if and only if it is locally of finite type and formally
unramified. -/
@[stacks 02HE "unramified case"]
public theorem unramified_iff_locallyOfFiniteType_and_formallyUnramified (f : X ⟶ S) :
    Unramified f ↔ (LocallyOfFiniteType f ∧ FormallyUnramified f) := by
  refine ((unramified_tfae f).out 1 2).trans ?_
  rw [locallyOfFiniteType_iff, formallyUnramified_iff]
  exact forall_appLE_iff_and algebraUnramified_iff_ringHom f

end AlgebraicGeometry
