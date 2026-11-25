/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Limits.ConstructLimitMap

/-!
# Cofiltered limits of schemes with affine transition morphisms

## Noetherian approximation of quasi-compact quasi-separated schemes

A *Noetherian approximation* of a scheme `S` is a cofiltered system of schemes of finite type
over `ℤ` with affine transition morphisms, together with a limit cone over the system with
point `S` (`AlgebraicGeometry.Scheme.NoetherianApproximation`). The stages of such a system
are Noetherian schemes (`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`).

Absolute Noetherian approximation (Stacks Project Tag 01ZA), proved in this file as
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, asserts that every quasi-compact
quasi-separated scheme admits a Noetherian approximation. It is proved by induction over a
finite affine cover, starting from the affine case: for an affine scheme `S`, the spectra of the
finitely generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a Noetherian approximation
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The key algebraic input
is that `Γ(S, ⊤)` is the filtered colimit of its finitely generated `ℤ`-subalgebras
(`CommRingCat.isColimitFgSubalgebraCocone`), and the geometric translation is that `Spec`,
being a right adjoint, preserves limits.

Throughout, "of finite type over `ℤ`" is spelled out as `LocallyOfFiniteType` of the
structure morphism `specULiftZIsTerminal.from X : X ⟶ Spec ℤ` together with
`CompactSpace X`.

(Blueprint: `def:nagata-noetherian-inverse-system`, `prop:nagata-noetherian-inverse-system`.)

## Checking the limit property locally on a stage

Mathlib's `AlgebraicGeometry.isLimitOpensCone` says that a limit cone over a cofiltered diagram
`{Dᵢ}` of schemes restricts, over any open `V ⊆ Dᵢ`, to a limit cone over the diagram of the
preimages of `V`. Here we prove the converse: a cone `c` over `{Dᵢ}` is a limit cone as soon as
its restrictions to the members of an open cover of one stage, and to their pairwise
intersections, are limit cones (`AlgebraicGeometry.isLimitOfIsLimitOpensCone`). No assumption on
the transition morphisms is needed. This is how the limit property of the system constructed for
Tag 01ZA is verified, chart by chart.

## The stages of the induction step of absolute Noetherian approximation

The general case of Tag 01ZA is proved by induction over a finite affine cover, extending an
approximation of a quasi-compact open `U` of `X` across one more affine open `V`
(Stacks Project Tag 07RN). The data of one induction step is bundled into
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData`, and the index category of
the extended system is the category
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.Stage` of *stages*: a stage
consists of an index `j` of the approximation of `U`, lifts to the stage `j` of finitely many
sections of `V` whose basic opens cover `W = U ⊓ V`, and a finitely generated `ℤ`-subalgebra
`A` of the fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)` big enough that `Wⱼ` becomes a
quasi-affine open of `Spec A` (`Stage.isOpenImmersion_toSpec`, Tags 01Z7 and 01Z9).

The two structural facts that drive the induction are that the stages form a cofiltered
category, and that the functor `ExtensionData.stageIndex` remembering the underlying index is
initial; so limits over the system of the `Wⱼ` may be computed over the category of stages.

## Descending schemes of finite presentation along an inverse limit of affine schemes

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps. If `X`
is an affine scheme that is locally of finite presentation over `lim Dᵢ`, then `X` is the base
change of an affine scheme that is locally of finite presentation over one of the `Dᵢ`
(`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`).

The same holds for an arbitrary scheme `X` of finite presentation over `lim Dᵢ`, and more
generally over a limit of quasi-compact quasi-separated schemes
(`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, Stacks Project Tag 01ZM):
one covers `X` by finitely many affine opens, each lying over an affine open of a fixed stage,
and glues the finite-stage models of the charts over a common stage. The two auxiliary steps
are that a quasi-compact open of `X` descends to a stage
(`AlgebraicGeometry.exists_descendsAtWithOpen`) and that two finite-stage models of the
same scheme become isomorphic at a later stage
(`AlgebraicGeometry.exists_iso_of_isPullback`).

## Separatedness descends to a finite stage

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps. If the limit `lim Dᵢ` is a separated scheme, then `Dᵢ` is separated for every
`i` past some stage (`AlgebraicGeometry.Scheme.exists_isSeparated_of_isLimit`, Stacks Project
Tag 086Q); and if all the `Dᵢ` lie over a fixed base `S` and `lim Dᵢ ⟶ S` is separated, then
`Dᵢ ⟶ S` is separated for every `i` past some stage
(`AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit`, Stacks Project Tag 01ZH).

Both are proved through the affine criterion `AlgebraicGeometry.IsSeparatingPair`: a scheme is
separated as soon as the affine opens of a finite affine cover pairwise have affine intersections
and the sections over such an intersection are generated by the sections of the two members. The
affineness of the intersections descends to a stage by Mathlib's
`AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` (Stacks Project Tag 01Z6). The generation
statement descends because, on one hand, the sections over the intersection at a stage are
finitely generated over the sections of one of the two members, and on the other hand the
elements of the limit which do come from a stage inside the subring generated by the two members
form a subring, which by hypothesis is everything
(`AlgebraicGeometry.exists_isSeparatingPair_of_isLimit`).

## The finite presentation model system of a morphism of finite type

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ S` be a morphism locally of
finite type with `X` quasi-compact and quasi-separated. Then `X` is a cofiltered limit of
schemes of finite presentation over `S` whose transition morphisms and whose morphisms from `X`
are closed immersions. Such a system is bundled into
`AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation`, and its existence is
`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation` (Stacks Project
Tag 09ZQ).

It is obtained by shrinking the immersion of Tag 01ZE to a closed immersion `X ⟶ Y` into a
quasi-compact open of the model
(`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation`) and then
writing `X` as the limit of the closed subschemes of `Y` cut out by the subideal sheaves of
finite type of the kernel of `X ⟶ Y` (Tag 09ZP).

## Minimal counterexamples over a quasi-compact quasi-separated base

A property `P` of quasi-compact quasi-separated schemes over a fixed quasi-compact
quasi-separated base `T` — a predicate on morphisms `T' ⟶ T` — is *qcqs-local*
(`AlgebraicGeometry.Scheme.IsQcqsLocalProperty`) if it is invariant under thickenings,
compatible with cofiltered limits along affine transition morphisms, propagates from a
scheme to a quasi-compact open subscheme or to its closed complement, and fails for the empty
scheme. Such a property holds
for the spectrum of a field over `T` as soon as it holds for `T` itself
(`AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`). Applied to the failure locus
of a base-change map, this says that a minimal counterexample can be found over a point.

Since Mathlib has no notion of a thickening of schemes, a thickening is spelled out as a
closed immersion which is surjective on points.

## References

- [Stacks: Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
- [Stacks: Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
- [Stacks: Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
- [Stacks: Tag 01ZH](https://stacks.math.columbia.edu/tag/01ZH)
- [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
- [Stacks: Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
- [Stacks: Tag 086Q](https://stacks.math.columbia.edu/tag/086Q)
- [Stacks: Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
- [Stacks: Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section FiniteTypeOverInt

/-- `Spec ℤ` is a locally Noetherian scheme. -/
instance isLocallyNoetherian_spec_uliftInt :
    IsLocallyNoetherian (Spec <| .of <| ULift.{u} ℤ) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  inferInstance

/-- The spectrum of a `ℤ`-algebra of finite type is locally of finite type over `Spec ℤ`. -/
instance locallyOfFiniteType_specULiftZIsTerminal_from (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec <| .of R)) := by
  have hφ : RingHom.FiniteType ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom) :=
    (RingHom.finiteType_algebraMap.mpr ‹_›).comp
      (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom))) :=
    HasRingHomProperty.Spec_iff.mpr hφ
  rwa [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from _) (Spec.map _)]

end FiniteTypeOverInt

/-- A **Noetherian approximation** of a scheme `S`: a cofiltered system of schemes of finite
type over `ℤ` with affine transition morphisms, exhibiting `S` as the limit of the system.
The stages are automatically Noetherian, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`.

```
              S
    π.app i  ↙         ↘  π.app j
  D.obj i  ─────────⟶  D.obj j
                D.map f
```

By absolute Noetherian approximation (Stacks Project Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), every quasi-compact
quasi-separated scheme admits one.
(Blueprint: `def:nagata-noetherian-inverse-system`.) -/
structure Scheme.NoetherianApproximation (S : Scheme.{u}) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of stages. -/
  D : I ⥤ Scheme.{u}
  /-- Every stage is locally of finite type over `ℤ`. -/
  locallyOfFiniteType_obj (i : I) : LocallyOfFiniteType (specULiftZIsTerminal.from (D.obj i))
  /-- Every stage is quasi-compact; together with `locallyOfFiniteType_obj` this says that
  every stage is of finite type over `ℤ`. -/
  compactSpace_obj (i : I) : CompactSpace (D.obj i)
  /-- The transition morphisms of the system are affine. -/
  isAffineHom_map {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f)
  /-- The projections from `S` to the stages. -/
  π : (Functor.const I).obj S ⟶ D
  /-- `S` is the limit of its stages. -/
  isLimit : IsLimit (Cone.mk S π)

namespace Scheme.NoetherianApproximation

attribute [instance] smallCategory isCofiltered locallyOfFiniteType_obj compactSpace_obj
  isAffineHom_map

variable {S : Scheme.{u}}

/-- The stages of a Noetherian approximation are Noetherian schemes: they are of finite type
over the Noetherian ring `ℤ`. -/
instance isNoetherian_obj (N : S.NoetherianApproximation) (i : N.I) : IsNoetherian (N.D.obj i) :=
  have := LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from (N.D.obj i))
  ⟨⟩

/-- Transport a Noetherian approximation along an isomorphism of schemes. -/
noncomputable def ofIso {S' : Scheme.{u}} (e : S ≅ S') (N : S.NoetherianApproximation) :
    S'.NoetherianApproximation where
  I := N.I
  D := N.D
  locallyOfFiniteType_obj := N.locallyOfFiniteType_obj
  compactSpace_obj := N.compactSpace_obj
  isAffineHom_map := N.isAffineHom_map
  π := (Functor.const N.I).map e.inv ≫ N.π
  isLimit := N.isLimit.ofIsoLimit <| Cone.ext e fun i ↦ by simp

/-- Restrict a Noetherian approximation to the over category of one of its indices. -/
noncomputable def over (N : S.NoetherianApproximation) (i : N.I) :
    S.NoetherianApproximation where
  I := Over i
  D := Over.forget i ⋙ N.D
  locallyOfFiniteType_obj _ := N.locallyOfFiniteType_obj _
  compactSpace_obj _ := N.compactSpace_obj _
  isAffineHom_map _ := N.isAffineHom_map _
  π := Functor.whiskerLeft (Over.forget i) N.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Cone.mk S N.π)).symm N.isLimit

@[simp] lemma over_I (N : S.NoetherianApproximation) (i : N.I) : (N.over i).I = Over i := rfl

@[simp] lemma over_D (N : S.NoetherianApproximation) (i : N.I) :
    (N.over i).D = Over.forget i ⋙ N.D := rfl

@[simp] lemma over_π_app (N : S.NoetherianApproximation) (i : N.I) (j : Over i) :
    (N.over i).π.app j = N.π.app j.left := rfl

variable (S : Scheme.{u}) [IsAffine S]

/-- **Noetherian approximation of an affine scheme**: the spectra of the finitely
generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a cofiltered system of schemes of finite type
over `ℤ` with affine transition maps whose limit is `S`. This is the affine case of Stacks
Project Tag 01ZA.

For `A ≤ B` the transition morphism `Spec ↥B ⟶ Spec ↥A` is `Spec.map` of the inclusion:

```
              S
    π.app B  ↙         ↘  π.app A
  Spec ↥B  ─────────⟶  Spec ↥A
```
-/
noncomputable def ofIsAffine : S.NoetherianApproximation where
  I := {A : Subalgebra ℤ Γ(S, ⊤) // A.FG}ᵒᵖ
  D := (CommRingCat.fgSubalgebraDiagram Γ(S, ⊤)).op ⋙ Scheme.Spec
  locallyOfFiniteType_obj i :=
    have : Algebra.FiniteType ℤ i.unop.1 := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
    inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of i.unop.1))))
  compactSpace_obj i := inferInstanceAs (CompactSpace (Spec (CommRingCat.of i.unop.1)))
  isAffineHom_map f := inferInstanceAs (IsAffineHom (Spec.map _))
  π := (Functor.const _).map S.isoSpec.hom ≫
    (Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCocone Γ(S, ⊤)).op).π
  isLimit :=
    (isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFgSubalgebraCocone Γ(S, ⊤)).op).ofIsoLimit
      (Cone.ext S.isoSpec.symm fun A ↦ by simp)

end Scheme.NoetherianApproximation

section IsLimitOfOpensCone

/-!
### Checking the limit property locally on a stage

Let `D` be a cofiltered diagram of schemes and `c` a cone over `D`. If the restrictions of
`c` to the members of an open cover of some stage `D.obj i₀` (and to their pairwise
intersections) are limit cones, then `c` is a limit cone. This is a converse to
`AlgebraicGeometry.isLimitOpensCone`.
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- (Implementation) The open cover of the point of a cone `s` over `D` by the preimages of a
covering family of opens of the stage `D.obj i₀`. -/
@[reducible] noncomputable def preimageCover (i₀ : I) {σ : Type*} (U : σ → (D.obj i₀).Opens)
    (hU : ⨆ a, U a = ⊤) (s : Cone D) : s.pt.OpenCover :=
  Scheme.Cover.mkOfCovers σ (fun a ↦ (s.π.app i₀ ⁻¹ᵁ U a).toScheme)
    (fun a ↦ Scheme.Opens.ι _)
    (fun x ↦ by
      have : s.π.app i₀ x ∈ ⨆ a, U a := by rw [hU]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨a, ⟨x, ha⟩, rfl⟩)

variable {c} in
/-- (Implementation) The universal morphism to the restriction of `c` to an open `V` of the
stage `D.obj i₀`, composed back into the tower of the cone `c`, agrees with the cone `s`. -/
lemma lift_opensCone_ι_comp {i₀ : I} {V : (D.obj i₀).Opens}
    (hV : IsLimit (opensCone D c i₀ V)) (s : Cone D) (j : Over i₀) :
    hV.lift (opensCone D s i₀ V) ≫ (c.π.app i₀ ⁻¹ᵁ V).ι ≫ c.π.app j.left =
      (s.π.app i₀ ⁻¹ᵁ V).ι ≫ s.π.app j.left := by
  have h1 := congrArg (· ≫ (D.map j.hom ⁻¹ᵁ V).ι) (hV.fac (opensCone D s i₀ V) j)
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι] at h1
  simpa using h1

variable {c} in
/-- (Implementation) Compatibility of the local universal morphisms on overlaps. -/
lemma glueMorphisms_compat {i₀ : I} {σ : Type*} {U : σ → (D.obj i₀).Opens}
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, IsLimit (opensCone D c i₀ (U a ⊓ U b))) (s : Cone D) (a b : σ) :
    pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) =
      pullback.snd _ _ ≫ ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι) := by
  have hq' : pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      (s.π.app i₀ ⁻¹ᵁ U a).ι = pullback.snd _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U b).ι :=
    pullback.condition
  have hqmem (t : ↑(pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι))) :
      s.π.app i₀ ((pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        (s.π.app i₀ ⁻¹ᵁ U a).ι) t) ∈ U a ⊓ U b := by
    constructor
    · rw [Scheme.Hom.comp_apply]
      exact (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
    · rw [hq', Scheme.Hom.comp_apply]
      exact (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
  have h0 : ∀ (x : σ), (h x).lift (opensCone D s i₀ (U x)) ≫
      (c.π.app i₀ ⁻¹ᵁ U x).ι ≫ c.π.app i₀ = (s.π.app i₀ ⁻¹ᵁ U x).ι ≫ s.π.app i₀ :=
    fun x ↦ lift_opensCone_ι_comp D (h x) s (Over.mk (𝟙 i₀))
  have key : ∀ (e : pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ⟶ c.pt),
      e ≫ c.π.app i₀ = (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ →
      Set.range e ⊆ Set.range ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) := by
    rintro e he - ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (e ≫ c.π.app i₀) t ∈ U a ⊓ U b
    rw [he]
    exact hqmem t
  have he_a : (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 a]
  have he_b : (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 b, reassoc_of% hq']
  rw [show pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) =
      IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_a) ≫
        (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι from (IsOpenImmersion.lift_fac _ _ _).symm,
    show pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι) =
      IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_b) ≫
        (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι from (IsOpenImmersion.lift_fac _ _ _).symm]
  congr 1
  apply (h₂ a b).hom_ext
  intro j
  rw [← cancel_mono (D.map j.hom ⁻¹ᵁ (U a ⊓ U b)).ι]
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc]
  simp only [Category.assoc]
  rw [lift_opensCone_ι_comp D (h a) s j, lift_opensCone_ι_comp D (h b) s j,
    reassoc_of% hq']

/-- **Being a limit cone is local on a stage.** Let `{Dᵢ}` be a cofiltered diagram of schemes and
let `c` be a cone over it. Suppose some stage `D.obj i₀` has an open cover `{U a}` such that the
restriction of `c` to every `U a`, and to every intersection `U a ⊓ U b`, is a limit cone. Then
`c` is a limit cone.

This is a converse to `AlgebraicGeometry.isLimitOpensCone`. -/
noncomputable def isLimitOfIsLimitOpensCone [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, IsLimit (opensCone D c i₀ (U a ⊓ U b))) : IsLimit c where
  lift s := (preimageCover D i₀ U hU s).glueMorphisms
    (fun a ↦ (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)
    (glueMorphisms_compat D h h₂ s)
  fac s j := by
    obtain ⟨k, fkj, fki₀, -⟩ := IsCofilteredOrEmpty.cone_objs j i₀
    rw [← c.w fkj, ← s.w fkj, ← Category.assoc]
    congr 1
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
    change ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) ≫ c.π.app k =
      (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ s.π.app k
    rw [Category.assoc]
    exact lift_opensCone_ι_comp D (h a) s (Over.mk fki₀)
  uniq s m hm := by
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [Scheme.Cover.ι_glueMorphisms]
    change (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m =
      (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι
    have hrange : Set.range ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ⊆
        Set.range ((c.π.app i₀ ⁻¹ᵁ U a).ι) := by
      rintro - ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ≫ c.π.app i₀) t ∈ U a
      rw [Category.assoc, hm i₀]
      exact t.2
    have hma : IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ U a).ι)
        ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) hrange = (h a).lift (opensCone D s i₀ (U a)) := by
      apply (h a).hom_ext
      intro j
      rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U a).ι]
      simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hm j.left]
      exact (lift_opensCone_ι_comp D (h a) s j).symm
    rw [← hma, IsOpenImmersion.lift_fac]

@[reassoc]
lemma opensDiagram_map_ι (i : I) (U : (D.obj i).Opens) {j j' : Over i} (k : j ⟶ j') :
    (opensDiagram D i U).map k ≫ Scheme.Opens.ι (D.map j'.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) ≫ D.map k.left :=
  (opensDiagramι D i U).naturality k

@[reassoc]
lemma opensCone_π_ι (c : Cone D) (i : I) (U : (D.obj i).Opens) (j : Over i) :
    (opensCone D c i U).π.app j ≫ Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (c.π.app i ⁻¹ᵁ U) ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

end IsLimitOfOpensCone

namespace Scheme.NoetherianApproximation

/-!
### The induction step of absolute Noetherian approximation

Following the proof of Stacks Project Tag 07RN, we extend a Noetherian approximation of a
quasi-compact open `U` of a quasi-separated scheme `X` to a Noetherian approximation of
`U ∪ V` for an affine open `V`. The extension is built from *stages*: a stage consists of an
index `j` of (the restriction to a coslice of) the approximation of `U`, a lift `r` of the
generators of `W = U ⊓ V` to sections at the stage `j`, and a finitely generated
`ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` — an algebraic incarnation of the fiber product
`Γ(V) ×_{Γ(W)} Γ(Wⱼ)` of Stacks 07RN. The scheme attached to a stage is the pushout of
`Dⱼ ⟵ Wⱼ ⟶ Spec A` along open immersions.
-/

/-- (Implementation) The setup for the induction step of absolute Noetherian approximation
(Stacks Project Tag 07RN): a quasi-separated scheme `X` covered by a quasi-compact open `U`
carrying a Noetherian approximation `N` and an affine open `V`; the intersection `U ⊓ V`
is descended to a quasi-compact open `W₀` at a stage `i₀` of `N`, and is exhibited as a
finite union of basic opens of sections `b l` of `V`. -/
structure ExtensionData where
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- The ambient scheme is quasi-separated. -/
  [qs : QuasiSeparatedSpace X]
  /-- The already approximated quasi-compact open. -/
  U : X.Opens
  /-- The new affine open. -/
  V : X.Opens
  /-- The two opens cover the ambient scheme. -/
  hUV : U ⊔ V = ⊤
  /-- The new open is affine. -/
  hV : IsAffineOpen V
  /-- A Noetherian approximation of `U`. -/
  N : U.toScheme.NoetherianApproximation
  /-- The stage of `N` at which `U ⊓ V` is descended. -/
  i₀ : N.I
  /-- The descended intersection. -/
  W₀ : (N.D.obj i₀).Opens
  /-- The descended intersection is quasi-compact. -/
  hW₀c : IsCompact (W₀ : Set (N.D.obj i₀))
  /-- The descended intersection pulls back to `U ⊓ V`. -/
  hW₀ : N.π.app i₀ ⁻¹ᵁ W₀ = U.ι ⁻¹ᵁ V
  /-- The number of chosen generators of the intersection. -/
  n : ℕ
  /-- The chosen generators of the intersection: sections of `V` whose basic opens
  cover `U ⊓ V`. -/
  b : Fin n → Γ(X, V)
  /-- Each chosen generator has its basic open inside the intersection. -/
  hb (l : Fin n) : X.basicOpen (b l) ≤ U ⊓ V
  /-- The basic opens of the chosen generators cover the intersection. -/
  hb' : U ⊓ V = ⨆ l, X.basicOpen (b l)

namespace ExtensionData

attribute [instance] qs

variable (E : ExtensionData.{u})

/-- (Implementation) The limit cone of the approximation of `U`. -/
abbrev cone : Cone E.N.D := Cone.mk _ E.N.π

/-- (Implementation) `W = U ⊓ V` as an open of `U`. -/
abbrev WU : E.U.toScheme.Opens := E.N.π.app E.i₀ ⁻¹ᵁ E.W₀

/-- (Implementation) The system of the descended intersections `Wⱼ`. -/
noncomputable abbrev WD : Over E.i₀ ⥤ Scheme.{u} := opensDiagram E.N.D E.i₀ E.W₀

/-- (Implementation) The cone exhibiting `W` as the limit of the `Wⱼ`. -/
noncomputable abbrev Wc : Cone E.WD := opensCone E.N.D E.cone E.i₀ E.W₀

/-- (Implementation) `W` is the limit of the `Wⱼ`. -/
noncomputable def isLimitWc : IsLimit E.Wc :=
  isLimitOpensCone E.N.D E.cone E.N.isLimit E.i₀ E.W₀

instance (j : Over E.i₀) : CompactSpace (E.WD.obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.D.map j.hom) _ E.W₀.2 E.hW₀c)

instance (j : Over E.i₀) : IsLocallyNoetherian (E.WD.obj j) := by
  have : IsLocallyNoetherian (E.N.D.obj j.left) := (E.N.isNoetherian_obj j.left).1
  exact isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι _)

/-- (Implementation) The restriction of a section of `V` to `W`, viewed inside the limit of
the `Wⱼ`. -/
noncomputable def sV : Γ(E.X, E.V) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ (by
    rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self])

/-- (Implementation) The restriction of a section at the stage `j` to the limit `W`. -/
noncomputable abbrev t (j : Over E.i₀) : Γ(E.WD.obj j, ⊤) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.Wc.π.app j).appTop

/-- (Implementation) The transition map on sections of the system `Wⱼ`. -/
noncomputable abbrev res {j j' : Over E.i₀} (f : j' ⟶ j) :
    Γ(E.WD.obj j, ⊤) ⟶ Γ(E.WD.obj j', ⊤) :=
  (E.WD.map f).appTop

lemma t_res {j j' : Over E.i₀} (f : j' ⟶ j) (x : Γ(E.WD.obj j, ⊤)) :
    E.t j' (E.res f x) = E.t j x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.Wc.w f]

lemma res_res {j j' j'' : Over E.i₀} (f : j' ⟶ j) (g : j'' ⟶ j') (x : Γ(E.WD.obj j, ⊤)) :
    E.res g (E.res f x) = E.res (g ≫ f) x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]

/-- (Implementation) A stage of the extended system: an index `j`, a lift `r` of the
generators of `W` to `Wⱼ` such that the basic opens of the `r l` form an affine cover of
`Wⱼ`, and a finitely generated `ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` contained in the
fiber product over `Γ(W, ⊤)`, containing the tautological elements `(b l, r l)` and
generating all the local rings of the cover (condition `hgen`, ensuring that `Wⱼ ⟶ Spec A`
is an open immersion). -/
structure Stage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))
  /-- The finite-stage coefficient algebra. -/
  A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))
  hA : ∀ p ∈ A, E.sV p.1 = E.t j p.2
  hAfg : A.FG
  hmem (l : Fin E.n) : (E.b l, r l) ∈ A
  hgen (l : Fin E.n) (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen (r l))) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ A ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom (r l) ^ m

/-- (Implementation) A morphism of stages over a morphism of underlying indices: the lifts
`r` are compatible, and the coefficient algebra of the target maps into that of the
source. -/
@[ext] structure Stage.Hom (T T' : E.Stage) where
  /-- The underlying index morphism. -/
  base : T.j ⟶ T'.j
  res_r (l : Fin E.n) : E.res base (T'.r l) = T.r l
  map_mem (p : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)) (hp : p ∈ T'.A) :
    (p.1, E.res base p.2) ∈ T.A

lemma res_id (j : Over E.i₀) (x : Γ(E.WD.obj j, ⊤)) : E.res (𝟙 j) x = x := by
  change ((E.WD.map (𝟙 j)).appTop).hom x = x
  rw [CategoryTheory.Functor.map_id]
  simp

instance : Category E.Stage where
  Hom := Stage.Hom E
  id T := ⟨𝟙 T.j, fun l ↦ E.res_id _ _, fun p hp ↦ by simpa [E.res_id] using hp⟩
  comp {T T' T''} f g := ⟨f.base ≫ g.base,
    fun l ↦ by rw [← E.res_res g.base f.base, g.res_r, f.res_r],
    fun p hp ↦ by
      have := f.map_mem _ (g.map_mem p hp)
      rwa [E.res_res] at this⟩
  id_comp f := Stage.Hom.ext (Category.id_comp f.base)
  comp_id f := Stage.Hom.ext (Category.comp_id f.base)
  assoc f g h := Stage.Hom.ext (Category.assoc f.base g.base h.base)

@[simp] lemma id_base (T : E.Stage) : (𝟙 T : T ⟶ T).base = 𝟙 T.j := rfl

@[simp] lemma comp_base {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[ext] lemma stageHom_ext {T T' : E.Stage} {f g : T ⟶ T'} (h : f.base = g.base) : f = g :=
  Stage.Hom.ext h

variable {E}

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of `Wⱼ`. -/
noncomputable def Stage.ρ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, ⊤) :=
  CommRingCat.ofHom ((RingHom.snd _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.ρ_apply (T : E.Stage) (a : ↥T.A) :
    T.ρ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := rfl

/-- (Implementation) The tautological element `(b l, r l)` of the coefficient algebra of a
stage. -/
def Stage.h (T : E.Stage) (l : Fin E.n) : ↥T.A := ⟨(E.b l, T.r l), T.hmem l⟩

@[simp] lemma Stage.coe_h (T : E.Stage) (l : Fin E.n) :
    (T.h l : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) = (E.b l, T.r l) := rfl

/-- (Implementation) The morphism from `Wⱼ` to the spectrum of the coefficient algebra of a
stage. By `Stage.isOpenImmersion_toSpec` this is an open immersion. -/
noncomputable def Stage.toSpec (T : E.Stage) :
    E.WD.obj T.j ⟶ Spec (CommRingCat.of ↥T.A) :=
  (E.WD.obj T.j).toSpecΓ ≫ Spec.map T.ρ

lemma Stage.toSpec_preimage_basicOpen (T : E.Stage) (l : Fin E.n) :
    T.toSpec ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) = (E.WD.obj T.j).basicOpen (T.r l) := by
  rw [Stage.toSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen, Stage.ρ_apply, Stage.coe_h]

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of the basic open `Wⱼ(r l) ⊆ Wⱼ`. This realizes the sections over `Wⱼ(r l)` as the
localization of the coefficient algebra away from the tautological element `(b l, r l)`,
see `Stage.isLocalization_away`. -/
noncomputable def Stage.ρRes (T : E.Stage) (l : Fin E.n) :
    CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) :=
  T.ρ ≫ (E.WD.obj T.j).presheaf.map (homOfLE le_top).op

@[simp] lemma Stage.ρRes_apply (T : E.Stage) (l : Fin E.n) (a : ↥T.A) :
    (T.ρRes l).hom a = ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom a.1.2 := rfl

/-- (Implementation) The image of `W = U ⊓ V` in `X`. -/
lemma opensRange_WUι_comp_Uι (E : ExtensionData.{u}) :
    (E.WU.ι ≫ E.U.ι).opensRange = E.U ⊓ E.V := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma basicOpen_le_opensRange (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.basicOpen (E.b l) ≤ (E.WU.ι ≫ E.U.ι).opensRange :=
  (E.hb l).trans E.opensRange_WUι_comp_Uι.ge

/-- (Implementation) Restricting a section of `V` to `X.basicOpen (b l)` and pulling back
to `W` agrees with restricting the pullback to `W`. -/
lemma res_app_eq_sV_res (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op ≫
      (E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) =
      E.sV ≫ E.WU.toScheme.presheaf.map (homOfLE le_top).op := by
  simp only [ExtensionData.sV, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- (Implementation) A section of `V` restricting to zero on `W` is annihilated by a power
of each of the chosen generators `b l`: the restriction `Γ(X, V) ⟶ Γ(W, 𝒪)` factors through
the localization `Γ(X, V) ⟶ Γ(X, X.basicOpen (b l))` because `X.basicOpen (b l) ≤ U ⊓ V`.
This is the key cancellation step in the proof of Stacks 01Z9. -/
lemma exists_pow_mul_eq_zero_of_sV_eq_zero (l : Fin E.n) {y : Γ(E.X, E.V)}
    (hy : E.sV y = 0) : ∃ K, E.b l ^ K * y = 0 := by
  have := E.hV.isLocalization_basicOpen (E.b l)
  suffices h0 : (E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op) y = 0 by
    obtain ⟨⟨_, K, rfl⟩, hK⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (E.b l)) Γ(E.X, E.X.basicOpen (E.b l)) y).mp h0
    exact ⟨K, hK⟩
  have := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  apply (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).1
  rw [map_zero, ← CommRingCat.comp_apply, E.res_app_eq_sV_res l, CommRingCat.comp_apply, hy,
    map_zero]

/-- (Implementation, Stacks 01Z9) The sections over the basic open `Wⱼ(r l)` are the
localization of the coefficient algebra of the stage away from the tautological element
`(b l, r l)`. Surjectivity is the condition `hgen` of the stage; injectivity combines the
qcqs lemma on `Wⱼ` with `exists_pow_mul_eq_zero_of_sV_eq_zero` on the `V`-component. -/
lemma Stage.isLocalization_away (T : E.Stage) (l : Fin E.n) :
    letI := (T.ρRes l).hom.toAlgebra
    IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := by
  let := (T.ρRes l).hom.toAlgebra
  refine IsLocalization.Away.mk (T.h l) ?_ (fun z ↦ ?_) (fun a a' hd ↦ ?_)
  · change IsUnit (((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom (T.r l))
    exact RingedSpace.isUnit_res_basicOpen (E.WD.obj T.j).toRingedSpace (T.r l)
  · obtain ⟨m, p, hp, hres⟩ := T.hgen l z
    refine ⟨m, ⟨p, hp⟩, ?_⟩
    change z * ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom (T.r l) ^ m =
      ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom p.2
    exact hres.symm
  · -- The second components agree after multiplication by a power of `r l`.
    have hres : a.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) =
        a'.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) := hd
    obtain ⟨k, hk⟩ := exists_of_res_eq_of_qcqs_of_top (X := E.WD.obj T.j)
      (f := a.1.2) (g := a'.1.2) (s := T.r l) hres
    have hk' : T.r l ^ k * (a.1.2 - a'.1.2) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact hk
    -- Push down to the intersection `W` and cancel the first components there.
    have hV0 : E.sV (E.b l ^ k * (a.1.1 - a'.1.1)) = 0 := by
      have ht := congrArg (E.t T.j) hk'
      rw [map_mul, map_pow, map_zero, T.hr] at ht
      rw [map_mul, map_pow, map_sub, T.hA _ a.2, T.hA _ a'.2, ← map_sub]
      exact ht
    obtain ⟨K, hK⟩ := E.exists_pow_mul_eq_zero_of_sV_eq_zero l hV0
    refine ⟨K + k, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.fst_mul,
        Prod.pow_fst]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc]
      exact hK
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.snd_mul,
        Prod.pow_snd]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc, hk', mul_zero]

/-- (Implementation) The heart of Stacks 07RN (via Tags 01Z7 and 01Z9): the morphism from
`Wⱼ` to the spectrum of the coefficient algebra of a stage is an open immersion. -/
instance Stage.isOpenImmersion_toSpec (T : E.Stage) : IsOpenImmersion T.toSpec := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨PrimeSpectrum.basicOpen (T.h l), (T.toSpec_preimage_basicOpen l).ge hl, ?_⟩
  suffices h : IsOpenImmersion (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) by
    convert! h <;> rw [toSpec_preimage_basicOpen]
  have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
      ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
    rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, ← Spec.map_comp, Stage.ρRes]
  rw [e]
  let := (T.ρRes l).hom.toAlgebra
  have : IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
  exact MorphismProperty.comp_mem _ (T.haff l).isoSpec.hom _ inferInstance
    (IsOpenImmersion.of_isLocalization (T.h l))

/-- (Implementation) The image of `Wⱼ ⟶ Spec A` is the union of the basic opens of the
tautological elements `(b l, r l)`. -/
lemma Stage.opensRange_toSpec (T : E.Stage) :
    T.toSpec.opensRange = ⨆ l, PrimeSpectrum.basicOpen (T.h l) := by
  refine le_antisymm ?_ (iSup_le fun l ↦ ?_)
  · rintro - ⟨x, rfl⟩
    have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, (T.toSpec_preimage_basicOpen l).ge hl⟩
  · have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
        ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
      rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
        Category.assoc, ← Spec.map_comp, Stage.ρRes]
    let := (T.ρRes l).hom.toAlgebra
    have : IsLocalization.Away (T.h l)
        Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
    have : IsIso (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) := by
      rw [← IsAffineOpen.isoSpec_hom (T.haff l)]
      infer_instance
    rintro p hp
    obtain ⟨q, hq⟩ : ∃ q, (Spec.map (T.ρRes l)).base q = p := by
      have h := PrimeSpectrum.localization_away_comap_range
        (S := Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l))) (T.h l)
      have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥T.A
          Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)))) := by
        rw [h]
        exact hp
      exact hmem
    obtain ⟨w, hw⟩ := (Scheme.Hom.homeomorph
      (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ)).surjective q
    have hw' : (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) w = q := hw
    refine ⟨((E.WD.obj T.j).basicOpen (T.r l)).ι w, ?_⟩
    have h1 : (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) w = p := by
      rw [e, Scheme.Hom.comp_apply, hw']
      exact hq
    rw [Scheme.Hom.comp_apply] at h1
    exact h1

/-!
#### Existence of stages

Following Stacks 01Z7, we produce stages: the sections of `Wⱼ` over a basic open `Wⱼ(r l)`
form a finitely generated `ℤ`-algebra, and each generator is, up to a power of `r l`, the
second component of an element of the fiber product `Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. Adjoining
these elements to any finitely generated subalgebra of the fiber product yields a stage.
-/

/-- (Implementation) The fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)`, i.e. the pairs of
sections agreeing on `W`, as a subalgebra of the product ring. The coefficient algebra of a
stage at `j` is a finitely generated subalgebra of it. -/
noncomputable def fiberProduct (E : ExtensionData.{u}) (j : Over E.i₀) :
    Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :=
  AlgHom.equalizer (E.sV.hom.comp (RingHom.fst _ _)).toIntAlgHom
    ((E.t j).hom.comp (RingHom.snd _ _)).toIntAlgHom

lemma mem_fiberProduct_iff (E : ExtensionData.{u}) {j : Over E.i₀}
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    p ∈ E.fiberProduct j ↔ E.sV p.1 = E.t j p.2 := Iff.rfl

/-- (Implementation) The basic open of `W` attached to a generator `b l` is the pullback of
the basic open of `X` attached to it. -/
lemma basicOpen_sV (E : ExtensionData.{u}) (l : Fin E.n) :
    E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) := by
  simp only [ExtensionData.sV, Scheme.basicOpen_appLE, top_inf_eq]

/-- (Implementation) The basic opens of the chosen generators cover `W`. -/
lemma iSup_basicOpen_sV (E : ExtensionData.{u}) :
    ⨆ l, E.Wc.pt.basicOpen (E.sV (E.b l)) = ⊤ := by
  simp_rw [E.basicOpen_sV]
  rw [← Scheme.Hom.preimage_iSup, ← E.hb']
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at this
  exact this

/-- (Implementation) `Wⱼ` is of finite type over `ℤ`, being open in a stage of the
approximation of `U`. -/
instance (j : Over E.i₀) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.WD.obj j)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.WD.obj j))
    ((E.N.D.map j.hom ⁻¹ᵁ E.W₀).ι ≫ specULiftZIsTerminal.from (E.N.D.obj j.left))]
  infer_instance

instance : CompactSpace E.Wc.pt := by
  have := isAffineHom_π_app E.N.D E.cone E.N.isLimit E.i₀
  exact isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.π.app E.i₀) _ E.W₀.2 E.hW₀c)

instance : QuasiSeparatedSpace E.Wc.pt := by
  have : QuasiSeparatedSpace E.U.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ E.U.2).mp (.of_quasiSeparatedSpace _)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ E.WU.2).mp (.of_quasiSeparatedSpace _)

variable (E) in
/-- (Implementation) Restricting a global section of `W` to the basic open of `sV (b l)`
factors through the restriction to the pullback of `X.basicOpen (b l)`; the two opens are
equal by `basicOpen_sV`. -/
lemma restrict_basicOpen_sV_eq (l : Fin E.n) (x : Γ(E.Wc.pt, ⊤)) :
    x |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.Wc.pt.presheaf.map (eqToHom (E.basicOpen_sV l)).op)
        ((E.Wc.pt.presheaf.map (homOfLE le_top).op) x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun f : E.Wc.pt.basicOpen (E.sV (E.b l)) ⟶ (⊤ : E.Wc.pt.Opens) ↦
      (E.Wc.pt.presheaf.map f.op).hom x)
    (Subsingleton.elim _ _)

/-- (Implementation, Stacks 01Z7) Every section over a basic open `Wⱼ(r l)` is, up to a
power of `r l`, the restriction of the second component of an element of the fiber product
`Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. -/
lemma exists_mem_fiberProduct_res_eq_mul_pow (E : ExtensionData.{u}) {j : Over E.i₀}
    {l : Fin E.n} {rl : Γ(E.WD.obj j, ⊤)} (hrl : E.t j rl = E.sV (E.b l))
    (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen rl)) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ E.fiberProduct j ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op) p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m := by
  classical
  -- Lift `z` to a global section `y` of `Wⱼ`, up to a power of `rl`.
  obtain ⟨m₀, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (E.WD.obj j) ⊤ isCompact_univ isQuasiSeparated_univ rl z
  -- The restriction of `t y` to the basic open of `W` comes from a section `zV` of
  -- `X.basicOpen (b l)`.
  have hiso := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  obtain ⟨zV, hzV⟩ := (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).2
    ((E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.t j y))
  -- Write `zV` as `v₀ / (b l) ^ K` using that `V` is affine.
  have := E.hV.isLocalization_basicOpen (E.b l)
  obtain ⟨⟨v₀, ⟨_, K, rfl⟩⟩, hv⟩ := IsLocalization.surj (M := Submonoid.powers (E.b l)) zV
  rw [map_pow] at hv
  -- Restricting sections of `V` to `X.basicOpen (b l)` and pulling back to `W` agrees with
  -- pulling back to `W` and restricting.
  have happ : ∀ x : Γ(E.X, E.V),
      ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))
        ((algebraMap Γ(E.X, E.V) Γ(E.X, E.X.basicOpen (E.b l))) x) =
      (E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.sV x) := fun x ↦ by
    have h := congrArg
      (fun f : Γ(E.X, E.V) ⟶
          Γ(E.WU.toScheme, (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l)) ↦ f x)
      (E.res_app_eq_sV_res l)
    dsimp only at h
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h
  -- Transport the localization relation along the pullback to `W`.
  have e₁ := congrArg ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) ·) hv
  dsimp only at e₁
  rw [map_mul, map_pow, happ, happ, hzV] at e₁
  have e₁' : (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.t j y) *
        (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.sV (E.b l)) ^ K =
      (E.Wc.pt.presheaf.map (homOfLE (le_top :
        (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) ≤ ⊤)).op) (E.sV v₀) := e₁
  -- `sV v₀` and `t (rl ^ K * y)` agree on the basic open of `sV (b l)`.
  have h6 : E.sV v₀ |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      E.t j (rl ^ K * y) |_ E.Wc.pt.basicOpen (E.sV (E.b l)) := by
    rw [E.restrict_basicOpen_sV_eq, E.restrict_basicOpen_sV_eq]
    congr 1
    rw [map_mul, map_pow, hrl, map_mul, map_pow]
    linear_combination -e₁'
  -- Hence they agree after multiplication by a power of `sV (b l)`.
  obtain ⟨M, hM⟩ := exists_of_res_eq_of_qcqs_of_top (X := E.Wc.pt) h6
  -- Assemble the element of the fiber product.
  refine ⟨M + K + m₀, (E.b l ^ M * v₀, rl ^ (M + K) * y), ?_, ?_⟩
  · rw [E.mem_fiberProduct_iff]
    dsimp only
    rw [map_mul, map_pow, hM, ← hrl, ← map_pow, ← map_mul, ← mul_assoc, ← pow_add]
  · dsimp only
    rw [map_mul, map_pow]
    have hy' : ((E.WD.obj j).presheaf.map (homOfLE le_top).op) y =
        ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m₀ * z := hy
    rw [hy', pow_add, pow_add]
    ring

/-!
#### The category of stages

Following `lemma:nagata-valid-refinements-directed`, the stages form a nonempty cofiltered
category: any finitely generated subalgebra of the fiber product can be enlarged to satisfy
the generation condition (Stacks 01Z7), lifts of the generators exist at a common index by
the section-descent lemmas for the limit `W = lim Wⱼ`, and the covering and affineness
conditions descend from the limit by Stacks 01Z4.
-/

instance (j : Over E.i₀) : IsNoetherian (E.WD.obj j) := ⟨⟩

/-- (Implementation) The identity on the `V`-component times restriction on the section
component, as a morphism of `ℤ`-algebras. It maps the fiber product at `j` into the fiber
product at `j'`. -/
noncomputable def resAlgHom {j j' : Over E.i₀} (k : j' ⟶ j) :
    (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) →ₐ[ℤ] Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤) :=
  ((RingHom.id Γ(E.X, E.V)).prodMap (E.res k).hom).toIntAlgHom

@[simp] lemma resAlgHom_apply {j j' : Over E.i₀} (k : j' ⟶ j)
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    resAlgHom k p = (p.1, E.res k p.2) := rfl

lemma resAlgHom_mem_fiberProduct {j j' : Over E.i₀} (k : j' ⟶ j)
    {p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)} (hp : p ∈ E.fiberProduct j) :
    resAlgHom k p ∈ E.fiberProduct j' := by
  rw [E.mem_fiberProduct_iff] at hp ⊢
  rw [resAlgHom_apply, E.t_res]
  exact hp

lemma Stage.A_le_fiberProduct (T : E.Stage) : T.A ≤ E.fiberProduct T.j :=
  fun p hp ↦ (E.mem_fiberProduct_iff p).mpr (T.hA p hp)

variable (E)

/-- (Implementation) The data of a stage without its coefficient algebra: an index `j` and
lifts `r` of the generators of the intersection such that the basic opens of the `r l` form
an affine cover of `Wⱼ`. -/
structure PreStage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))

variable {E}

/-- (Implementation) The pre-stage underlying a stage. -/
def Stage.toPreStage (T : E.Stage) : E.PreStage :=
  ⟨T.j, T.r, T.hr, T.hcov, T.haff⟩

/-- (Implementation) Pre-stages restrict along morphisms of indices. -/
noncomputable def PreStage.restrict (P : E.PreStage) {j' : Over E.i₀} (k : j' ⟶ P.j) :
    E.PreStage where
  j := j'
  r l := E.res k (P.r l)
  hr l := by rw [E.t_res, P.hr]
  hcov := by
    have h : ∀ l, (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm
    simp_rw [h, ← Scheme.Hom.preimage_iSup, P.hcov, Scheme.Hom.preimage_top]
  haff l := by
    rw [show (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) from
      (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm]
    exact (P.haff l).preimage _

/-- (Implementation, Stacks 01Z7) For every pre-stage and every generator index `l`, there
is a finite subset of the fiber product such that every subalgebra containing it and the
tautological pair `(b l, r l)` satisfies the generation condition of a stage at `l`: the
sections over the affine basic open `Wⱼ(r l)` form a finitely generated `ℤ`-algebra, and
every generator is, up to a power of `r l`, the section component of an element of the
fiber product. -/
lemma PreStage.exists_finset_hgen (P : E.PreStage) (l : Fin E.n) :
    ∃ s : Finset (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
      (∀ q ∈ s, q ∈ E.fiberProduct P.j) ∧
      ∀ A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
        (E.b l, P.r l) ∈ A → (∀ q ∈ s, q ∈ A) →
        ∀ z : Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)),
          ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
            ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom p.2 =
              z * ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom (P.r l) ^ m := by
  classical
  have hft : Algebra.FiniteType ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
    IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType
      (f := specULiftZIsTerminal.from (E.WD.obj P.j)) (P.haff l)
  obtain ⟨s₀, hs₀⟩ := hft.1
  choose m p hp₁ hp₂ using fun z : s₀ ↦
    E.exists_mem_fiberProduct_res_eq_mul_pow (P.hr l) (z : _)
  refine ⟨s₀.attach.image p, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact hp₁ z
  · intro A hbr hsub z
    set ρ := ((E.WD.obj P.j).presheaf.map
      (homOfLE (le_top : (E.WD.obj P.j).basicOpen (P.r l) ≤ ⊤)).op).hom with hρ
    let S : Subalgebra ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
      { carrier := {z | ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
          ρ p.2 = z * ρ (P.r l) ^ m}
        one_mem' := ⟨0, 1, one_mem A, by simp⟩
        zero_mem' := ⟨0, 0, zero_mem A, by simp⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * p₂, mul_mem h₁ h₂, ?_⟩
          change ρ (p₁.2 * p₂.2) = _
          rw [map_mul, e₁, e₂]
          ring
        add_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * (E.b l, P.r l) ^ m₂ + p₂ * (E.b l, P.r l) ^ m₁,
            add_mem (mul_mem h₁ (pow_mem hbr m₂)) (mul_mem h₂ (pow_mem hbr m₁)), ?_⟩
          change ρ (p₁.2 * P.r l ^ m₂ + p₂.2 * P.r l ^ m₁) = _
          rw [map_add, map_mul, map_mul, map_pow, map_pow, e₁, e₂]
          ring
        algebraMap_mem' := fun c ↦ ⟨0, algebraMap ℤ _ c, A.algebraMap_mem c, by
          change ρ (algebraMap ℤ _ c) = _
          rw [pow_zero, mul_one]
          exact map_intCast ρ c⟩ }
    have hS : Algebra.adjoin ℤ (↑s₀ : Set _) ≤ S := by
      refine Algebra.adjoin_le fun z hz ↦ ?_
      exact ⟨m ⟨z, hz⟩, p ⟨z, hz⟩,
        hsub _ (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩), hp₂ ⟨z, hz⟩⟩
    have := hS (hs₀ ▸ Algebra.mem_top (R := ℤ) (x := z))
    exact this

/-- (Implementation, Stacks 01Z7) Enlarge a finitely generated subalgebra of the fiber
product containing the tautological pairs to the coefficient algebra of a stage over a
given pre-stage. -/
noncomputable def PreStage.mkStage (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)))
    (hA₀ : A₀ ≤ E.fiberProduct P.j) (hfg : A₀.FG)
    (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) : E.Stage where
  j := P.j
  r := P.r
  hr := P.hr
  hcov := P.hcov
  haff := P.haff
  A := A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose)
  hA p hp := by
    have h : A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose) ≤
        E.fiberProduct P.j := by
      refine sup_le hA₀ (Algebra.adjoin_le fun q hq ↦ ?_)
      obtain ⟨l, hql⟩ := Set.mem_iUnion.mp hq
      exact (P.exists_finset_hgen l).choose_spec.1 q hql
    exact (E.mem_fiberProduct_iff p).mp (h hp)
  hAfg := hfg.sup (Subalgebra.fg_def.mpr
    ⟨_, Set.finite_iUnion fun l ↦ (P.exists_finset_hgen l).choose.finite_toSet, rfl⟩)
  hmem l := Algebra.mem_sup_left (hmem l)
  hgen l z :=
    (P.exists_finset_hgen l).choose_spec.2 _
      (Algebra.mem_sup_left (hmem l))
      (fun q hq ↦ Algebra.mem_sup_right
        (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨l, hq⟩))) z

@[simp] lemma PreStage.mkStage_j (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).j = P.j := rfl

@[simp] lemma PreStage.mkStage_r (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).r = P.r := rfl

lemma PreStage.le_mkStage_A (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    A₀ ≤ (P.mkStage A₀ hA₀ hfg hmem).A := le_sup_left

/-- (Implementation) The minimal stage over a pre-stage: adjoin the tautological pairs and
close up under the generation condition. -/
noncomputable def PreStage.stage (P : E.PreStage) : E.Stage :=
  P.mkStage (Algebra.adjoin ℤ (Set.range fun l ↦ (E.b l, P.r l)))
    (Algebra.adjoin_le (by rintro p ⟨l, rfl⟩; exact (E.mem_fiberProduct_iff _).mpr (P.hr l).symm))
    (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)
    (fun l ↦ Algebra.subset_adjoin ⟨l, rfl⟩)

@[simp] lemma PreStage.stage_j (P : E.PreStage) : P.stage.j = P.j := rfl

/-- (Implementation) Restrict a stage along a morphism of indices, adjoining an extra
finitely generated subalgebra of the fiber product. -/
noncomputable def Stage.restrict (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤)))
    (hA' : A' ≤ E.fiberProduct j') (hfg : A'.FG) : E.Stage :=
  (T.toPreStage.restrict k).mkStage (T.A.map (resAlgHom k) ⊔ A')
    (sup_le (by rintro p ⟨q, hq, rfl⟩; exact resAlgHom_mem_fiberProduct k (T.A_le_fiberProduct hq))
      hA')
    ((T.hAfg.map _).sup hfg)
    (fun l ↦ Algebra.mem_sup_left ⟨(E.b l, T.r l), T.hmem l, rfl⟩)

@[simp] lemma Stage.restrict_j (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrict k A' hA' hfg).j = j' := rfl

@[simp] lemma Stage.restrict_r (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) (l : Fin E.n) :
    (T.restrict k A' hA' hfg).r l = E.res k (T.r l) := rfl

lemma Stage.le_restrict_A (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : A' ≤ (T.restrict k A' hA' hfg).A :=
  le_trans le_sup_right ((T.toPreStage.restrict k).le_mkStage_A _ _ _ _)

/-- (Implementation) The canonical morphism from a restricted stage. -/
noncomputable def Stage.restrictHom (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : T.restrict k A' hA' hfg ⟶ T where
  base := k
  res_r _ := rfl
  map_mem p hp := (T.toPreStage.restrict k).le_mkStage_A _ _ _ _
    (Algebra.mem_sup_left ⟨p, hp, rfl⟩)

@[simp] lemma Stage.restrictHom_base (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrictHom k A' hA' hfg).base = k := rfl

variable (E)

/-- (Implementation) A finite-conjunction helper: a family of index-stable properties, each
attainable below any index, is attained jointly below any index. -/
private lemma exists_hom_forall {j₂ : Over E.i₀}
    (P : ∀ (j' : Over E.i₀), (j' ⟶ j₂) → Fin E.n → Prop)
    (hstab : ∀ {j j' : Over E.i₀} (k' : j' ⟶ j) (k : j ⟶ j₂) (l : Fin E.n),
      P j k l → P j' (k' ≫ k) l)
    (hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (k' : j' ⟶ j), P j' (k' ≫ k) l) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, P j k l := by
  classical
  suffices h : ∀ s : Finset (Fin E.n), ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l ∈ s, P j k l by
    obtain ⟨j, k, hj⟩ := h Finset.univ
    exact ⟨j, k, fun l ↦ hj l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨j₂, 𝟙 j₂, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, k, hj⟩ := ih
    obtain ⟨j', k', hj'⟩ := hex j k a
    refine ⟨j', k' ≫ k, fun l hl ↦ ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj'
    · exact hstab k' k l (hj l hl)

/-- (Implementation) The lifts of the generators of the intersection exist at a common
index below any given index. -/
lemma exists_r (j₀ : Over E.i₀) :
    ∃ (j : Over E.i₀) (_ : j ⟶ j₀) (r : Fin E.n → Γ(E.WD.obj j, ⊤)),
      ∀ l, E.t j (r l) = E.sV (E.b l) := by
  have hex : ∀ (j : Over E.i₀) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (_ : j' ⟶ j) (r : Γ(E.WD.obj j', ⊤)), E.t j' r = E.sV (E.b l) := by
    intro j l
    obtain ⟨i, r₀, hr₀⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV (E.b l))
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    exact ⟨j', kj, E.res ki r₀, by rw [E.t_res]; exact hr₀.symm⟩
  obtain ⟨j, k, h⟩ := E.exists_hom_forall (j₂ := j₀)
    (fun j' _ l ↦ ∃ r, E.t j' r = E.sV (E.b l))
    (fun {j j'} k' k l hl ↦ by
      obtain ⟨r, hr⟩ := hl
      exact ⟨E.res k' r, by rw [E.t_res]; exact hr⟩)
    (fun j k l ↦ by
      obtain ⟨j', k', r, hr⟩ := hex j l
      exact ⟨j', k', r, hr⟩)
  choose r hr using h
  exact ⟨j, k, r, hr⟩

/-- (Implementation) The basic opens of the limit lifts of the generators are affine: they
are the basic opens of the affine `V`, transported into the limit `W`. -/
lemma isAffineOpen_basicOpen_sV (l : Fin E.n) :
    IsAffineOpen (E.Wc.pt.basicOpen (E.sV (E.b l))) := by
  rw [E.basicOpen_sV]
  exact (E.hV.basicOpen (E.b l)).preimage_of_isOpenImmersion _
    (by rw [E.opensRange_WUι_comp_Uι]; exact E.hb l)

/-- (Implementation) Below any index, there is a pre-stage: lifts of the generators whose
basic opens are affine and cover. The covering condition descends from the limit by
`exists_map_eq_top`, and affineness by descending the affine limit basic open
(Stacks 01Z4). -/
lemma exists_preStage_hom (j₀ : Over E.i₀) :
    ∃ (P : E.PreStage), Nonempty (P.j ⟶ j₀) := by
  -- Step 1: lifts with the covering condition.
  obtain ⟨j₁, k₁, r, hr⟩ := E.exists_r j₀
  have hU : E.Wc.π.app j₁ ⁻¹ᵁ (⨆ l, (E.WD.obj j₁).basicOpen (r l)) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [Scheme.preimage_basicOpen_top]
    have h : ∀ l, (E.Wc.π.app j₁).appTop (r l) = E.sV (E.b l) := hr
    simp_rw [h]
    exact E.iSup_basicOpen_sV
  obtain ⟨j₂, k₂, hk₂⟩ := exists_map_eq_top E.WD E.Wc E.isLimitWc _ hU
  set r₂ : Fin E.n → Γ(E.WD.obj j₂, ⊤) := fun l ↦ E.res k₂ (r l) with hr₂def
  have hr₂ : ∀ l, E.t j₂ (r₂ l) = E.sV (E.b l) := fun l ↦ by rw [hr₂def, E.t_res, hr]
  have hcov₂ : ⨆ l, (E.WD.obj j₂).basicOpen (r₂ l) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₂).basicOpen (r₂ l) =
        E.WD.map k₂ ⁻¹ᵁ ((E.WD.obj j₁).basicOpen (r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₂) (r l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hk₂]
  -- Step 2: affineness of the basic opens, by descending the affine limit basic open
  -- and equalizing (Stacks 01Z4).
  have hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (ja : Over E.i₀) (ka : ja ⟶ j),
        IsAffineOpen ((E.WD.obj ja).basicOpen (E.res (ka ≫ k) (r₂ l))) := by
    intro j k l
    obtain ⟨i, O, hO, hOeq⟩ := exists_isAffineOpen_preimage_eq E.WD E.Wc E.isLimitWc _
      (E.isAffineOpen_basicOpen_sV l)
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    have hpre : E.Wc.π.app j' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) =
        E.Wc.π.app j' ⁻¹ᵁ (E.WD.map ki ⁻¹ᵁ O) := by
      rw [Scheme.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage, E.Wc.w ki, hOeq]
      congr 1
      exact (E.t_res (kj ≫ k) (r₂ l)).trans (hr₂ l)
    obtain ⟨j'', k'', heq⟩ := exists_map_preimage_eq_map_preimage E.WD E.Wc E.isLimitWc
      (TopologicalSpace.NoetherianSpace.isCompact _)
      (TopologicalSpace.NoetherianSpace.isCompact _) hpre
    refine ⟨j'', k'' ≫ kj, ?_⟩
    have e : (E.WD.obj j'').basicOpen (E.res ((k'' ≫ kj) ≫ k) (r₂ l)) =
        E.WD.map k'' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) := by
      rw [Scheme.preimage_basicOpen_top]
      congr 1
      rw [Category.assoc]
      exact (E.res_res (kj ≫ k) k'' _).symm
    rw [e, heq]
    exact (hO.preimage (E.WD.map ki)).preimage (E.WD.map k'')
  obtain ⟨j₃, k₃, h₃⟩ := E.exists_hom_forall (j₂ := j₂)
    (fun j' k l ↦ IsAffineOpen ((E.WD.obj j').basicOpen (E.res k (r₂ l))))
    (fun {j j'} k' k l hl ↦ by
      have e : (E.WD.obj j').basicOpen (E.res (k' ≫ k) (r₂ l)) =
          E.WD.map k' ⁻¹ᵁ ((E.WD.obj j).basicOpen (E.res k (r₂ l))) := by
        rw [Scheme.preimage_basicOpen_top]
        congr 1
        exact (E.res_res k k' _).symm
      rw [e]
      exact hl.preimage _)
    hex
  have hcov₃ : ⨆ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) =
        E.WD.map k₃ ⁻¹ᵁ ((E.WD.obj j₂).basicOpen (r₂ l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₃) (r₂ l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hcov₂, Scheme.Hom.preimage_top]
  exact ⟨⟨j₃, fun l ↦ E.res k₃ (r₂ l), fun l ↦ by rw [E.t_res, hr₂], hcov₃, h₃⟩,
    ⟨(k₃ ≫ k₂) ≫ k₁⟩⟩

/-- (Implementation) Equalize two families of sections with equal limit restrictions at a
common finer index. -/
lemma exists_hom_res_eq {j₂ : Over E.i₀} (x y : Fin E.n → Γ(E.WD.obj j₂, ⊤))
    (h : ∀ l, E.t j₂ (x l) = E.t j₂ (y l)) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, E.res k (x l) = E.res k (y l) := by
  apply E.exists_hom_forall (fun j k l ↦ E.res k (x l) = E.res k (y l))
  · intro j j' k' k l hl
    exact (E.res_res k k' _).symm.trans
      ((congrArg (fun z ↦ E.res k' z) hl).trans (E.res_res k k' _))
  · intro j k l
    have hcpt : IsCompact ((⊤ : (E.WD.obj j).Opens) : Set (E.WD.obj j)) := isCompact_univ
    obtain ⟨j', k', hk'⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt
      (E.res k (x l)) (E.res k (y l))
      (show E.t j (E.res k (x l)) = E.t j (E.res k (y l)) by rw [E.t_res, E.t_res, h])
    refine ⟨j', k', ?_⟩
    exact (E.res_res k k' _).symm.trans (hk'.trans (E.res_res k k' _))

instance : Nonempty E.Stage := by
  obtain ⟨P, -⟩ := E.exists_preStage_hom (Over.mk (𝟙 E.i₀))
  exact ⟨P.stage⟩

instance : IsCofilteredOrEmpty E.Stage where
  cone_objs T₁ T₂ := by
    obtain ⟨j', k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j T₂.j
    obtain ⟨j, k, hk⟩ := E.exists_hom_res_eq (fun l ↦ E.res k₁ (T₁.r l))
      (fun l ↦ E.res k₂ (T₂.r l)) (fun l ↦ by rw [E.t_res, E.t_res, T₁.hr, T₂.hr])
    have hmap : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ E.fiberProduct j := by
      rintro p ⟨q, hq, rfl⟩
      exact resAlgHom_mem_fiberProduct _ (T₂.A_le_fiberProduct hq)
    -- Stated for a general subalgebra `A'`: for the concrete one, elaborating the components
    -- of the morphism to `T₂` is very slow.
    have H (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))) (hA' : A' ≤ E.fiberProduct j)
        (hfg : A'.FG) (hle : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ A') :
        ∃ (W : E.Stage) (_ : W ⟶ T₁) (_ : W ⟶ T₂), True :=
      ⟨T₁.restrict (k ≫ k₁) A' hA' hfg, T₁.restrictHom _ _ _ _,
        ⟨k ≫ k₂, fun l ↦ (E.res_res k₂ k _).symm.trans ((hk l).symm.trans (E.res_res k₁ k _)),
          fun p hp ↦ T₁.le_restrict_A _ _ _ _ (hle ⟨p, hp, rfl⟩)⟩, trivial⟩
    exact H _ hmap (T₂.hAfg.map _) le_rfl
  cone_maps T₁ T₂ f g := by
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps f.base g.base
    refine ⟨T₁.restrict k ⊥ bot_le Subalgebra.fg_bot, T₁.restrictHom _ _ _ _, ?_⟩
    exact E.stageHom_ext (by simpa using hk)

instance : IsCofiltered E.Stage where

/-- (Implementation) The index functor from stages to the base indices. By
`exists_preStage_hom` and the restriction construction it is initial: limits over the
system of the `Wⱼ` may be computed over the category of stages. -/
@[simps] def stageIndex : E.Stage ⥤ Over E.i₀ where
  obj T := T.j
  map f := f.base

instance : E.stageIndex.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro j
    obtain ⟨P, ⟨k⟩⟩ := E.exists_preStage_hom j
    exact ⟨P.stage, ⟨k⟩⟩
  · intro j T s s'
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps s s'
    exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot, T.restrictHom _ _ _ _, by simpa using hk⟩

variable {E}

/-- (Implementation) The open immersion of `Wⱼ` into the stage `Dⱼ`. -/
noncomputable abbrev Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.WD.obj j ⟶ E.N.D.obj j.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).app j

instance (E : ExtensionData.{u}) (j : Over E.i₀) : IsOpenImmersion (E.Wι j) :=
  inferInstanceAs (IsOpenImmersion ((opensDiagramι E.N.D E.i₀ E.W₀).app j))

@[reassoc]
lemma WD_map_Wι {j j' : Over E.i₀} (k : j ⟶ j') :
    E.WD.map k ≫ E.Wι j' = E.Wι j ≫ E.N.D.map k.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).naturality k

/-- (Implementation) The first projection from the coefficient algebra of a stage to the
sections of `V`. -/
noncomputable def Stage.φ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.X, E.V) :=
  CommRingCat.ofHom ((RingHom.fst _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.φ_apply (T : E.Stage) (a : ↥T.A) :
    T.φ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 := rfl

/-- (Implementation) The map of coefficient algebras attached to a morphism of stages. -/
noncomputable def Stage.Hom.algHom {T T' : E.Stage} (f : T ⟶ T') :
    CommRingCat.of ↥T'.A ⟶ CommRingCat.of ↥T.A :=
  CommRingCat.ofHom
    ((AlgHom.codRestrict ((resAlgHom f.base).comp T'.A.val) T.A
      (fun a ↦ f.map_mem _ a.2)).toRingHom)

@[simp] lemma Stage.Hom.algHom_coe {T T' : E.Stage} (f : T ⟶ T') (a : ↥T'.A) :
    ((f.algHom a : ↥T.A) : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) =
      ((a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).1,
        E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).2) := rfl

lemma Stage.Hom.algHom_ρ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.ρ = T'.ρ ≫ E.res f.base := rfl

lemma Stage.Hom.algHom_φ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.φ = T'.φ := rfl

@[simp] lemma Stage.Hom.algHom_id (T : E.Stage) : (𝟙 T : T ⟶ T).algHom = 𝟙 _ := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact E.res_id _ _

@[simp] lemma Stage.Hom.algHom_comp {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).algHom = g.algHom ≫ f.algHom := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact (E.res_res g.base f.base _).symm

@[reassoc (attr := simp)]
lemma Stage.Hom.SpecMap_φ {T T' : E.Stage} (f : T ⟶ T') :
    Spec.map T.φ ≫ Spec.map f.algHom = Spec.map T'.φ := by
  rw [← Spec.map_comp, Stage.Hom.algHom_φ]

lemma Stage.toSpec_comp_SpecMap_algHom {T T' : E.Stage} (f : T ⟶ T') :
    T.toSpec ≫ Spec.map f.algHom = E.WD.map f.base ≫ T'.toSpec := by
  rw [Stage.toSpec, Stage.toSpec, Category.assoc, ← Spec.map_comp, Stage.Hom.algHom_ρ,
    Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]

-- Elaborating the pushout functor forces repeated defeq checks between the two
-- `Algebra` structures on the coefficient algebra of a stage.
/-- (Implementation) The system of stage schemes: the scheme attached to a stage is the
gluing of the Noetherian stage `Dⱼ` and the affine scheme `Spec A` along `Wⱼ`. -/
noncomputable def stageDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} where
  obj T := pushout (E.Wι T.j) T.toSpec
  map {T T'} f := pushout.map _ _ _ _ (E.N.D.map f.base.left) (Spec.map f.algHom)
    (E.WD.map f.base) (WD_map_Wι f.base).symm (Stage.toSpec_comp_SpecMap_algHom f)
  map_id T := by
    have hb : (𝟙 T : T ⟶ T).base.left = 𝟙 T.j.left := rfl
    have h2 := Stage.Hom.algHom_id T
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc, hb, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [pushout.inr_desc, h2, Spec.map_id, Category.id_comp, Category.comp_id]
  map_comp {T T' T''} f g := by
    have hb : (f ≫ g).base.left = f.base.left ≫ g.base.left := rfl
    have h2 := Stage.Hom.algHom_comp f g
    refine pushout.hom_ext ?_ ?_
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc, hb, CategoryTheory.Functor.map_comp,
        Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, h2, Spec.map_comp, Category.assoc]

@[simp] lemma stageDiagram_obj (T : E.Stage) :
    E.stageDiagram.obj T = pushout (E.Wι T.j) T.toSpec := rfl

@[reassoc (attr := simp)]
lemma inl_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inl (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      E.N.D.map f.base.left ≫ pushout.inl (E.Wι T'.j) T'.toSpec :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inr (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      Spec.map f.algHom ≫ pushout.inr (E.Wι T'.j) T'.toSpec :=
  pushout.inr_desc _ _ _


@[simp] lemma opensRange_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    (E.Wι j).opensRange = E.N.D.map j.hom ⁻¹ᵁ E.W₀ :=
  Scheme.Opens.opensRange_ι _

/-- (Implementation) The `Wⱼ`-squares of the system of stages are cartesian. -/
lemma isPullback_Wι {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) (E.Wι T.j) (E.Wι T'.j) (E.N.D.map f.base.left) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (WD_map_Wι f.base).symm ?_
  rw [opensRange_Wι, opensRange_Wι, ← Scheme.Hom.comp_preimage, ← E.N.D.map_comp, Over.w f.base]

-- The basic opens of the tautological elements have to be compared through
-- `Spec.map` of the coefficient algebra map, which unfolds the stage structure.
/-- (Implementation) The `Spec A`-squares of the system of stages are cartesian. -/
lemma isPullback_toSpec {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) T.toSpec T'.toSpec (Spec.map f.algHom) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Stage.toSpec_comp_SpecMap_algHom f) ?_
  rw [T.opensRange_toSpec, T'.opensRange_toSpec, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun l ↦ ?_
  rw [SpecMap_preimage_basicOpen]
  congr 1
  refine Subtype.ext ?_
  rw [Stage.Hom.algHom_coe, Stage.coe_h, Stage.coe_h, f.res_r]

lemma isPullback_pushout_inl {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.N.D.map f.base.left) (pushout.inl (E.Wι T.j) T.toSpec)
      (pushout.inl (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inl_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma isPullback_pushout_inr {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (Spec.map f.algHom) (pushout.inr (E.Wι T.j) T.toSpec)
      (pushout.inr (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inr_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

instance (T : E.Stage) : CompactSpace (E.stageDiagram.obj T) :=
  have : CompactSpace (E.N.D.obj T.j.left) := inferInstance
  have : CompactSpace (Spec (CommRingCat.of ↥T.A)) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum ↥T.A))
  inferInstanceAs (CompactSpace ↑(pushout (E.Wι T.j) T.toSpec))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A))) :=
  have : Algebra.FiniteType ℤ ↥T.A := (Subalgebra.fg_iff_finiteType _).mp T.hAfg
  inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of ↥T.A))))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.stageDiagram.obj T)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.stageDiagram.obj T))
    (pushout.desc (specULiftZIsTerminal.from (E.N.D.obj T.j.left))
      (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A)))
      (specULiftZIsTerminal.hom_ext _ _))]
  exact IsZariskiLocalAtSource.pushout_desc (E.Wι T.j) T.toSpec _ inferInstance inferInstance

instance isAffineHom_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    IsAffineHom (E.stageDiagram.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (IsOpenImmersion.pushoutCover (E.Wι T'.j) T'.toSpec)
  rintro (_ | _)
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inl (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inl f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inl f).flip.isoPullback_hom_snd]
    infer_instance
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inr (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inr f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inr f).flip.isoPullback_hom_snd]
    infer_instance


/-! ### The cone -/

lemma sVle (E : ExtensionData.{u}) : (⊤ : E.Wc.pt.Opens) ≤ (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.V := by
  rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self]

lemma sV_eq (E : ExtensionData.{u}) :
    E.sV = (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ E.sVle := rfl

lemma range_WUι_comp_Uι_subset (E : ExtensionData.{u}) :
    Set.range (E.WU.ι ≫ E.U.ι) ⊆ Set.range E.V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨x, rfl⟩
  have hx : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at hx
  exact hx.2

/-- (Implementation) The canonical morphism from the intersection `W = U ⊓ V` to `V`. -/
noncomputable def ζ (E : ExtensionData.{u}) : E.Wc.pt ⟶ E.V.toScheme :=
  IsOpenImmersion.lift E.V.ι (E.WU.ι ≫ E.U.ι) E.range_WUι_comp_Uι_subset

@[reassoc (attr := simp)]
lemma ζ_ι (E : ExtensionData.{u}) : E.ζ ≫ E.V.ι = E.WU.ι ≫ E.U.ι :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma Wc_π_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.Wc.π.app j ≫ E.Wι j = E.WU.ι ≫ E.N.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

lemma toSpecΓ_ζ (E : ExtensionData.{u}) :
    E.ζ ≫ E.V.toSpecΓ = E.Wc.pt.toSpecΓ ≫ Spec.map E.sV := by
  have : IsIso ((⊤ : E.Wc.pt.Opens).ι) := by
    rw [← Scheme.topIso_hom]; infer_instance
  have hres : (E.WU.ι ≫ E.U.ι).resLE E.V ⊤ E.sVle = (⊤ : E.Wc.pt.Opens).ι ≫ E.ζ := by
    rw [← cancel_mono E.V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, E.ζ_ι]
  have h := Scheme.Opens.toSpecΓ_SpecMap_appLE (E.WU.ι ≫ E.U.ι) E.V (⊤ : E.Wc.pt.Opens) E.sVle
  rw [← E.sV_eq, hres, Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc] at h
  exact ((cancel_epi ((⊤ : E.Wc.pt.Opens).ι)).mp h).symm

/-- (Implementation) Comparing `W` with `Spec A` via `V` and via `Wⱼ` gives the same
morphism: this is where the fiber product condition on the coefficient algebra enters. -/
@[reassoc]
lemma Stage.ζ_toSpecΓ_SpecMap_φ (T : E.Stage) :
    E.ζ ≫ E.V.toSpecΓ ≫ Spec.map T.φ = E.Wc.π.app T.j ≫ T.toSpec := by
  rw [Stage.toSpec, ← Category.assoc E.ζ, E.toSpecΓ_ζ, Category.assoc, ← Spec.map_comp,
    ← Category.assoc (E.Wc.π.app T.j), Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact T.hA _ a.2

/-- (Implementation) The open cover of `X` by `U` and `V`. -/
noncomputable def cover (E : ExtensionData.{u}) : E.X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b ↦ (bif b then E.U else E.V).toScheme)
    (fun b ↦ (bif b then E.U else E.V).ι)
    (fun x ↦ by
      have hx : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
      · exact ⟨true, ⟨x, h⟩, rfl⟩
      · exact ⟨false, ⟨x, h⟩, rfl⟩)
    (fun b ↦ by cases b <;> exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))

@[simp] lemma cover_f_true (E : ExtensionData.{u}) : E.cover.f true = E.U.ι := rfl

@[simp] lemma cover_f_false (E : ExtensionData.{u}) : E.cover.f false = E.V.ι := rfl

/-- (Implementation) The morphism `U ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromU (T : E.Stage) : E.U.toScheme ⟶ E.stageDiagram.obj T :=
  E.N.π.app T.j.left ≫ pushout.inl (E.Wι T.j) T.toSpec

/-- (Implementation) The morphism `V ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromV (T : E.Stage) : E.V.toScheme ⟶ E.stageDiagram.obj T :=
  E.V.toSpecΓ ≫ Spec.map T.φ ≫ pushout.inr (E.Wι T.j) T.toSpec

lemma Stage.WUι_fromU (T : E.Stage) : E.WU.ι ≫ T.fromU = E.ζ ≫ T.fromV := by
  rw [Stage.fromU, Stage.fromV, ← E.Wc_π_Wι_assoc T.j, pushout.condition,
    T.ζ_toSpecΓ_SpecMap_φ_assoc]

/-- (Implementation) The isomorphism between `U ⊓ V` and the intersection `W`. -/
noncomputable def θ (E : ExtensionData.{u}) : (E.U ⊓ E.V).toScheme ≅ E.Wc.pt :=
  IsOpenImmersion.isoOfRangeEq (E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U)) E.WU.ι (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
      Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀]
    congr 1
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq])

@[reassoc (attr := simp)]
lemma θ_hom_WUι (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.WU.ι = E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma θ_hom_ζ (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.ζ = E.X.homOfLE (inf_le_right : E.U ⊓ E.V ≤ E.V) := by
  rw [← cancel_mono E.V.ι, Category.assoc, E.ζ_ι, ← Category.assoc, E.θ_hom_WUι,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι]

@[reassoc (attr := simp)]
lemma θ_inv_homOfLE (E : ExtensionData.{u}) :
    E.θ.inv ≫ E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) = E.WU.ι := by
  rw [← E.θ_hom_WUι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma θ_inv_infι (E : ExtensionData.{u}) : E.θ.inv ≫ (E.U ⊓ E.V).ι = E.WU.ι ≫ E.U.ι := by
  rw [← Scheme.homOfLE_ι E.X (inf_le_left : E.U ⊓ E.V ≤ E.U), ← Category.assoc,
    θ_inv_homOfLE]

lemma Stage.homOfLE_fromU (T : E.Stage) {W : E.X.Opens} (h₁ : W ≤ E.U) (h₂ : W ≤ E.V) :
    E.X.homOfLE h₁ ≫ T.fromU = E.X.homOfLE h₂ ≫ T.fromV := by
  rw [← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_left : E.U ⊓ E.V ≤ E.U),
    ← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_right : E.U ⊓ E.V ≤ E.V), Category.assoc,
    Category.assoc, ← E.θ_hom_WUι, ← E.θ_hom_ζ, Category.assoc, Category.assoc, T.WUι_fromU]

/-- (Implementation) The morphism from `X` to the stage scheme of a stage: it restricts to
the projection of the approximation of `U` on `U`, and to the map induced by the first
projection of the coefficient algebra on `V`. -/
noncomputable def Stage.fromX (T : E.Stage) : E.X ⟶ E.stageDiagram.obj T :=
  E.cover.glueMorphisms (fun b ↦ match b with | true => T.fromU | false => T.fromV) (by
    rintro (_ | _) (_ | _)
    · change pullback.fst E.V.ι E.V.ι ≫ T.fromV = pullback.snd E.V.ι E.V.ι ≫ T.fromV
      rw [(cancel_mono E.V.ι).mp
        (pullback.condition : pullback.fst E.V.ι E.V.ι ≫ _ = pullback.snd _ _ ≫ _)]
    · change pullback.fst E.V.ι E.U.ι ≫ T.fromV = pullback.snd E.V.ι E.U.ι ≫ T.fromU
      rw [← cancel_epi (isPullback_opens_inf E.V E.U).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact (T.homOfLE_fromU inf_le_right inf_le_left).symm
    · change pullback.fst E.U.ι E.V.ι ≫ T.fromU = pullback.snd E.U.ι E.V.ι ≫ T.fromV
      rw [← cancel_epi (isPullback_opens_inf E.U E.V).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact T.homOfLE_fromU inf_le_left inf_le_right
    · change pullback.fst E.U.ι E.U.ι ≫ T.fromU = pullback.snd E.U.ι E.U.ι ≫ T.fromU
      rw [(cancel_mono E.U.ι).mp
        (pullback.condition : pullback.fst E.U.ι E.U.ι ≫ _ = pullback.snd _ _ ≫ _)])


@[reassoc (attr := simp)]
lemma Stage.Uι_fromX (T : E.Stage) : E.U.ι ≫ T.fromX = T.fromU :=
  E.cover.ι_glueMorphisms _ _ true

@[reassoc (attr := simp)]
lemma Stage.Vι_fromX (T : E.Stage) : E.V.ι ≫ T.fromX = T.fromV :=
  E.cover.ι_glueMorphisms _ _ false

@[reassoc]
lemma N_π_naturality (E : ExtensionData.{u}) {i i' : E.N.I} (g : i ⟶ i') :
    E.N.π.app i ≫ E.N.D.map g = E.N.π.app i' :=
  E.cone.w g

/-- (Implementation) The cone with point `X` over the system of stage schemes. -/
noncomputable def stageCone (E : ExtensionData.{u}) : Cone E.stageDiagram where
  pt := E.X
  π :=
    { app := fun T ↦ T.fromX
      naturality := fun T T' f ↦ by
        change 𝟙 E.X ≫ T'.fromX = T.fromX ≫ E.stageDiagram.map f
        rw [Category.id_comp]
        refine E.cover.hom_ext _ _ fun b ↦ ?_
        cases b
        · simp only [cover_f_false, Stage.Vι_fromX, Stage.Vι_fromX_assoc, Stage.fromV,
            Category.assoc, inr_stageDiagram_map, Stage.Hom.SpecMap_φ_assoc]
        · simp only [cover_f_true, Stage.Uι_fromX, Stage.Uι_fromX_assoc, Stage.fromU,
            Category.assoc, inl_stageDiagram_map, E.N_π_naturality_assoc] }

@[simp] lemma stageCone_pt (E : ExtensionData.{u}) : E.stageCone.pt = E.X := rfl

@[simp] lemma stageCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.stageCone.π.app T = T.fromX := rfl


/-! ### The two charts of a stage scheme -/

/-- (Implementation) The chart of a stage scheme coming from the Noetherian stage `Dⱼ`. -/
noncomputable abbrev Stage.chartU (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inl (E.Wι T.j) T.toSpec).opensRange

/-- (Implementation) The chart of a stage scheme coming from `Spec A`. -/
noncomputable abbrev Stage.chartV (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inr (E.Wι T.j) T.toSpec).opensRange

lemma Stage.chartU_sup_chartV (T : E.Stage) : T.chartU ⊔ T.chartV = ⊤ :=
  opensRange_pushout_inl_sup_opensRange_pushout_inr _ _

lemma Stage.preimage_chartU {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartU = T.chartU :=
  preimage_opensRange_pushout_inl_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma Stage.preimage_chartV {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartV = T.chartV :=
  preimage_opensRange_pushout_inr_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

lemma Stage.chartU_inf_chartV (T : E.Stage) :
    T.chartU ⊓ T.chartV = (E.Wι T.j ≫ pushout.inl (E.Wι T.j) T.toSpec).opensRange := by
  rw [Scheme.Hom.opensRange_comp (E.Wι T.j) (pushout.inl (E.Wι T.j) T.toSpec),
    ← preimage_opensRange_pushout_inr (E.Wι T.j) T.toSpec,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

lemma Stage.fromX_preimage_chartU (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartU = E.U := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · exact h
    · -- `x` lies in `V`; its image in `Spec A` lies in the image of `Wⱼ`, hence in one of
      -- the basic opens of the generators, which are contained in `U`.
      obtain ⟨y, hy⟩ : ∃ y, pushout.inl (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.V.toScheme := ⟨x, h⟩ with hx'
      have hfV : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
          (Spec.map T.φ (E.V.toSpecΓ x')) :=
        calc T.fromX x = (E.V.ι ≫ T.fromX) x' := rfl
          _ = T.fromV x' := by rw [Stage.Vι_fromX]
          _ = _ := rfl
      rw [hfV] at hy
      obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy
      have hq : Spec.map T.φ (E.V.toSpecΓ x') ∈ T.toSpec.opensRange := ⟨w, hw⟩
      rw [T.opensRange_toSpec] at hq
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
      have hl' : E.V.toSpecΓ x' ∈ Spec.map T.φ ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) := hl
      rw [SpecMap_preimage_basicOpen] at hl'
      have hb : (T.φ (T.h l) : Γ(E.X, E.V)) = E.b l := rfl
      rw [hb] at hl'
      have : x' ∈ E.V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (E.b l) := hl'
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at this
      exact ((E.hb l) this).1
  · change T.fromX x ∈ T.chartU
    have h1 : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec
        (E.N.π.app T.j.left (⟨x, hx⟩ : E.U.toScheme)) :=
      calc T.fromX x = (E.U.ι ≫ T.fromX) (⟨x, hx⟩ : E.U.toScheme) := rfl
        _ = T.fromU (⟨x, hx⟩ : E.U.toScheme) := by rw [Stage.Uι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartV (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartV = E.V := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · obtain ⟨y, hy⟩ : ∃ y, pushout.inr (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.U.toScheme := ⟨x, h⟩ with hx'
      have hfU : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec (E.N.π.app T.j.left x') :=
        calc T.fromX x = (E.U.ι ≫ T.fromX) x' := rfl
          _ = T.fromU x' := by rw [Stage.Uι_fromX]
          _ = _ := rfl
      rw [hfU] at hy
      obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy.symm
      have hp : E.N.π.app T.j.left x' ∈ (E.Wι T.j).opensRange := ⟨w, hw⟩
      rw [opensRange_Wι] at hp
      have hp' : E.N.π.app E.i₀ x' ∈ E.W₀ := by
        rw [← E.N_π_naturality T.j.hom, Scheme.Hom.comp_apply]
        exact hp
      have : x' ∈ E.N.π.app E.i₀ ⁻¹ᵁ E.W₀ := hp'
      rw [E.hW₀] at this
      exact this
    · exact h
  · change T.fromX x ∈ T.chartV
    have h1 : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
        (Spec.map T.φ (E.V.toSpecΓ (⟨x, hx⟩ : E.V.toScheme))) :=
      calc T.fromX x = (E.V.ι ≫ T.fromX) (⟨x, hx⟩ : E.V.toScheme) := rfl
        _ = T.fromV (⟨x, hx⟩ : E.V.toScheme) := by rw [Stage.Vι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartU_inf_chartV (T : E.Stage) :
    T.fromX ⁻¹ᵁ (T.chartU ⊓ T.chartV) = E.U ⊓ E.V := by
  rw [Scheme.Hom.preimage_inf, T.fromX_preimage_chartU, T.fromX_preimage_chartV]


/-! ### The limit property, chart by chart -/

/-- (Implementation) The system of Noetherian stages `Dⱼ`, indexed by the stages below a
fixed stage. -/
noncomputable abbrev baseDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀ ⋙ E.N.D

/-- (Implementation) `U` is the limit of the Noetherian stages `Dⱼ` indexed by the stages
below a fixed stage: the index functor is initial. -/
noncomputable def isLimitBaseCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.cone).symm E.N.isLimit

/-- (Implementation) The `U`-chart of a stage scheme is `Dⱼ`, compatibly with the
transition morphisms. -/
noncomputable def chartUIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.baseDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ T₀.chartU :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))
      (Scheme.Hom.range_eq_range_ι_of_opensRange_eq _ (Stage.preimage_chartU S.hom).symm))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map]
      rfl)

-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `U`-chart is a limit cone. -/
noncomputable def isLimitOpensConeChartU (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU) :=
  IsLimit.equivOfNatIsoOfIso (E.chartUIso T₀)
    (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU)
    (Cone.ext (E.X.isoOfEq T₀.fromX_preimage_chartU.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Category.assoc, chartUIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Scheme.isoOfEq_hom_ι_assoc]
      exact (Stage.Uι_fromX S.left).symm))
    (E.isLimitBaseCone T₀)


/-- (Implementation) The system of intersections `Wⱼ`, indexed by the stages below a fixed
stage. -/
noncomputable abbrev interDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ E.WD

/-- (Implementation) `W = U ⊓ V` is the limit of the `Wⱼ` indexed by the stages below a
fixed stage. -/
noncomputable def isLimitInterCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.Wc).symm E.isLimitWc

/-- (Implementation) The overlap of the two charts of a stage scheme is `Wⱼ`, compatibly
with the transition morphisms. -/
noncomputable def interIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.interDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ (T₀.chartU ⊓ T₀.chartV) :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq
      (E.Wι S.left.j ≫ pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ (T₀.chartU ⊓ T₀.chartV)))
      (Scheme.Hom.range_eq_range_ι_of_opensRange_eq _ ((congrArg₂ (· ⊓ ·)
        (Stage.preimage_chartU S.hom) (Stage.preimage_chartV S.hom)).trans
          (Stage.chartU_inf_chartV _)).symm))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      have h : (E.interDiagram T₀).map k = E.WD.map k.left.base := rfl
      simp only [h, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map,
        WD_map_Wι_assoc])

-- Transporting the limit along the overlap isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the overlap of the two charts is a
limit cone. -/
noncomputable def isLimitOpensConeInter (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV)) :=
  IsLimit.equivOfNatIsoOfIso (E.interIso T₀)
    (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex))
    (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV))
    (Cone.ext (E.θ.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartU_inf_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, interIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, θ_inv_infι_assoc, stageCone_π_app]
      exact (E.Wc_π_Wι_assoc S.left.j _).trans (by rw [Stage.Uι_fromX, Stage.fromU])))
    (E.isLimitInterCone T₀)
/-! ### The `Spec A`-chart: the sections of `V` are the colimit of the coefficient algebras -/

/-- (Implementation) Every section of `V` occurs in the coefficient algebra of some stage. -/
lemma exists_stage_mem_A (E : ExtensionData.{u}) (β : Γ(E.X, E.V)) :
    ∃ (T : E.Stage) (a : ↥T.A), (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 = β := by
  obtain ⟨T₁⟩ := (inferInstance : Nonempty E.Stage)
  obtain ⟨j₁, x₁, hx₁⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV β)
  obtain ⟨j₂, k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j j₁
  have hxt : E.t j₂ (E.res k₂ x₁) = E.sV β := by rw [E.t_res]; exact hx₁.symm
  have hle : Algebra.adjoin ℤ {(β, E.res k₂ x₁)} ≤ E.fiberProduct j₂ :=
    Algebra.adjoin_le (by rintro p rfl; exact (E.mem_fiberProduct_iff _).mpr hxt.symm)
  have hfg : (Algebra.adjoin ℤ {(β, E.res k₂ x₁)}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.finite_singleton _, rfl⟩
  exact ⟨T₁.restrict k₁ _ hle hfg,
    ⟨(β, E.res k₂ x₁), T₁.le_restrict_A k₁ _ hle hfg (Algebra.subset_adjoin rfl)⟩, rfl⟩

/-- (Implementation) Two elements of a coefficient algebra whose components agree are
equal. -/
lemma Stage.Hom.algHom_eq_of {T T' : E.Stage} (f : T' ⟶ T) (a b : ↥T.A)
    (h1 : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1)
    (h2 : E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.res f.base (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2) :
    f.algHom a = f.algHom b :=
  Subtype.ext (by rw [Stage.Hom.algHom_coe, Stage.Hom.algHom_coe, h1, h2])

/-- (Implementation) Two elements of a coefficient algebra with the same `V`-component become
equal at a later stage: their `Wⱼ`-components agree on the intersection `W`, hence already at
a finite stage. -/
lemma exists_hom_algHom_eq (E : ExtensionData.{u}) (T : E.Stage) (a b : ↥T.A)
    (h : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1) :
    ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b := by
  have ht : E.t T.j (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.t T.j (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := by
    rw [← T.hA _ a.2, ← T.hA _ b.2, h]
  have hcpt : IsCompact ((⊤ : (E.WD.obj T.j).Opens) : Set (E.WD.obj T.j)) := isCompact_univ
  obtain ⟨j', k, hk⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt _ _ ht
  -- Stated for a general subalgebra `A'`: at `A' = ⊥`, unifying `hk` with the goal is very
  -- slow.
  have H (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤))) (hA' : A' ≤ E.fiberProduct j')
      (hfg : A'.FG) : ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b :=
    ⟨T.restrict k A' hA' hfg, T.restrictHom k A' hA' hfg, Stage.Hom.algHom_eq_of _ a b h hk⟩
  exact H ⊥ bot_le Subalgebra.fg_bot

/-- (Implementation) The system of coefficient algebras of the stages, as a diagram in the
opposite category of commutative rings. -/
noncomputable def algOp (E : ExtensionData.{u}) : E.Stage ⥤ CommRingCatᵒᵖ where
  obj T := Opposite.op (CommRingCat.of ↥T.A)
  map f := (f.algHom).op
  map_id T := Quiver.Hom.unop_inj (Stage.Hom.algHom_id T)
  map_comp f g := Quiver.Hom.unop_inj (Stage.Hom.algHom_comp f g)

/-- (Implementation) `Γ(X, V)` as a cocone on the system of coefficient algebras. -/
noncomputable def algCocone (E : ExtensionData.{u}) : Cocone E.algOp.leftOp where
  pt := Γ(E.X, E.V)
  ι :=
    { app := fun T ↦ T.unop.φ
      naturality := fun _ _ f ↦
        (Stage.Hom.algHom_φ f.unop).trans (Category.comp_id _).symm }

-- Reflecting the colimit through the forgetful functor unfolds the subalgebra
-- coercions of every stage.
/-- (Implementation) `Γ(X, V)` is the filtered colimit of the coefficient algebras of the
stages: every section of `V` occurs at some stage, and two elements with the same
`V`-component become equal at a later stage. -/
noncomputable def isColimitAlgCocone (E : ExtensionData.{u}) : IsColimit E.algCocone := by
  have : ReflectsColimit E.algOp.leftOp (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun β ↦ ?_) (fun T a b hab ↦ ?_)
  · obtain ⟨T, a, ha⟩ := E.exists_stage_mem_A β
    exact ⟨Opposite.op T, a, ha.symm⟩
  · obtain ⟨T', f, hf⟩ := E.exists_hom_algHom_eq T.unop a b hab
    exact ⟨Opposite.op T', f.op, hf⟩

/-- (Implementation) The system of the spectra of the coefficient algebras. -/
noncomputable abbrev specDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} :=
  E.algOp ⋙ Scheme.Spec

/-- (Implementation) `V ≅ Spec Γ(X, V)` as a cone on the spectra of the coefficient
algebras. -/
noncomputable def specCone (E : ExtensionData.{u}) : Cone E.specDiagram :=
  Scheme.Spec.mapCone (Limits.coneOfCoconeLeftOp E.algCocone)

lemma specCone_pt (E : ExtensionData.{u}) : E.specCone.pt = Spec Γ(E.X, E.V) := rfl

lemma specCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.specCone.π.app T = Spec.map T.φ := rfl

/-- (Implementation) `Spec Γ(X, V)` is the limit of the spectra of the coefficient
algebras. -/
noncomputable def isLimitSpecCone (E : ExtensionData.{u}) : IsLimit E.specCone :=
  isLimitOfPreserves Scheme.Spec
    (Limits.isLimitConeOfCoconeLeftOp E.algOp E.isColimitAlgCocone)

@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ (E : ExtensionData.{u}) :
    E.hV.isoSpec.inv ≫ E.V.toSpecΓ = 𝟙 _ := by
  rw [← IsAffineOpen.isoSpec_hom E.hV, Iso.inv_hom_id]

/-- (Implementation) The `Spec A`-chart of a stage scheme is `Spec A`, compatibly with the
transition morphisms. -/
noncomputable def chartVIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over.forget T₀ ⋙ E.specDiagram ≅ opensDiagram E.stageDiagram T₀ T₀.chartV :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inr (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))
      (Scheme.Hom.range_eq_range_ι_of_opensRange_eq _ (Stage.preimage_chartV S.hom).symm))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inr_stageDiagram_map]
      rfl)

-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `Spec A`-chart is a limit
cone. -/
noncomputable def isLimitOpensConeChartV (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV) :=
  IsLimit.equivOfNatIsoOfIso (E.chartVIso T₀)
    (E.specCone.whisker (Over.forget T₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV)
    (Cone.ext (E.hV.isoSpec.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, chartVIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, stageCone_π_app]
      rw [Stage.Vι_fromX, Stage.fromV, isoSpec_inv_toSpecΓ_assoc]
      exact congrArg (fun g ↦ g ≫ pushout.inr (E.Wι S.left.j) S.left.toSpec)
        (specCone_π_app E S.left)))
    ((Functor.Initial.isLimitWhiskerEquiv _ E.specCone).symm E.isLimitSpecCone)

/-- (Implementation) The two charts of a stage scheme, as a family indexed by `Bool`. -/
noncomputable def charts (E : ExtensionData.{u}) (T₀ : E.Stage) (b : Bool) :
    (E.stageDiagram.obj T₀).Opens :=
  bif b then T₀.chartU else T₀.chartV

-- Each of the four cases unfolds the pushout defining the stage scheme.
/-- (Implementation) The stage cone is a limit cone: its restrictions to the two charts of a
stage scheme and to their overlap are limit cones. -/
noncomputable def isLimitStageConeOfStage (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit E.stageCone := by
  refine isLimitOfIsLimitOpensCone E.stageDiagram E.stageCone T₀ (E.charts T₀) ?_
    (fun b ↦ ?_) (fun b b' ↦ ?_)
  · rw [iSup_bool_eq]
    exact T₀.chartU_sup_chartV
  · cases b
    exacts [E.isLimitOpensConeChartV T₀, E.isLimitOpensConeChartU T₀]
  · cases b <;> cases b'
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartV))
      rw [inf_idem]
      exact E.isLimitOpensConeChartV T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartU))
      rw [inf_comm]
      exact E.isLimitOpensConeInter T₀
    · exact E.isLimitOpensConeInter T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartU))
      rw [inf_idem]
      exact E.isLimitOpensConeChartU T₀

/-- (Implementation) The stage cone is a limit cone. -/
noncomputable def isLimitStageCone (E : ExtensionData.{u}) : IsLimit E.stageCone :=
  E.isLimitStageConeOfStage (Classical.arbitrary E.Stage)

/-- (Implementation) The Noetherian approximation of `X = U ∪ V` extending a given
approximation of `U` across the affine open `V`. This is the induction step of
Stacks Project Tag 07RN. -/
noncomputable def approximation (E : ExtensionData.{u}) : E.X.NoetherianApproximation where
  I := E.Stage
  D := E.stageDiagram
  locallyOfFiniteType_obj _ := inferInstance
  compactSpace_obj _ := inferInstance
  isAffineHom_map _ := inferInstance
  π := E.stageCone.π
  isLimit := E.isLimitStageCone

end ExtensionData

end Scheme.NoetherianApproximation

/-- (Implementation) A finite supremum of quasi-compact opens is quasi-compact. -/
private lemma isCompact_finset_sup {X : Scheme.{u}} (s : Finset X.Opens)
    (hs : ∀ V ∈ s, IsCompact (V : Set X)) : IsCompact ((s.sup id : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert]
      refine IsCompact.union (hs a (Finset.mem_insert_self a s)) ?_
      exact ih fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)

open Scheme.NoetherianApproximation in
/-- (Implementation) **Absolute Noetherian approximation** for a finite union of affine
opens of a quasi-separated scheme, by induction on the number of members of the union
(Stacks Project Tag 07RN). -/
private lemma nonempty_noetherianApproximation_finsetSup {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (s : Finset X.Opens) (hs : ∀ V ∈ s, IsAffineOpen V) :
    Nonempty ((s.sup id : X.Opens).toScheme.NoetherianApproximation) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      have h : IsAffine ((⊥ : X.Opens).toScheme) := isAffineOpen_bot X
      exact ⟨Scheme.NoetherianApproximation.ofIsAffine _⟩
  | insert a s ha ih =>
      obtain ⟨N₀⟩ := ih fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      have haff : IsAffineOpen a := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ V ∈ s, IsAffineOpen V := fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      rw [Finset.sup_insert, id]
      set Y : X.Opens := a ⊔ s.sup id with hYdef
      have : QuasiSeparatedSpace Y.toScheme :=
        (isQuasiSeparated_iff_quasiSeparatedSpace _ Y.2).mp (.of_quasiSeparatedSpace _)
      set U : Y.toScheme.Opens := Y.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Y.toScheme.Opens := Y.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hYdef,
          Scheme.Opens.ι_preimage_self]
      have hVaff : IsAffineOpen V := by
        refine haff.preimage_of_isOpenImmersion Y.ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact le_sup_left
      -- the approximation of `U`, transported from the induction hypothesis
      have hrange : Set.range (X.homOfLE (le_sup_right : s.sup id ≤ Y)) =
          Set.range (Scheme.Opens.ι U) := by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
          Scheme.opensRange_homOfLE, Scheme.Opens.opensRange_ι]
      have N : U.toScheme.NoetherianApproximation :=
        N₀.ofIso (IsOpenImmersion.isoOfRangeEq _ _ hrange)
      -- the intersection `U ⊓ V` is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun V hV ↦ (hsaff V hV).isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Y.toScheme.Opens) : Set Y.toScheme) := by
        have he : (U ⊓ V : Y.toScheme.Opens) = Y.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Y.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      have hUVc' : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
        have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
          rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
        rw [he]
        refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hUVc ?_
        rw [Scheme.Opens.range_ι]
        exact inf_le_left
      obtain ⟨i₀, W₀, hW₀c, hW₀⟩ :=
        exists_preimage_eq N.D (Cone.mk _ N.π) N.isLimit _ hUVc'
      -- the generators of the intersection
      obtain ⟨t, ht⟩ := hVaff.exists_finset_basicOpen_eq hUVc inf_le_right
      obtain ⟨m, eq⟩ : ∃ m, Nonempty ({x // x ∈ t} ≃ Fin m) := ⟨t.card, ⟨t.equivFin⟩⟩
      obtain ⟨eq⟩ := eq
      have hcov : (U ⊓ V : Y.toScheme.Opens) =
          ⨆ l : Fin m, Y.toScheme.basicOpen ((eq.symm l : {x // x ∈ t}) :
            Γ(Y.toScheme, V)) := by
        have h1 : (⨆ f ∈ t, Y.toScheme.basicOpen f) =
            ⨆ x : {x // x ∈ t}, Y.toScheme.basicOpen (x : Γ(Y.toScheme, V)) :=
          iSup_subtype' (p := fun x : Γ(Y.toScheme, V) ↦ x ∈ t)
            (f := fun x _ ↦ Y.toScheme.basicOpen x)
        rw [ht, h1, ← Equiv.iSup_comp (g := fun x : {x // x ∈ t} ↦
          Y.toScheme.basicOpen (x : Γ(Y.toScheme, V))) eq.symm]
      exact ⟨Scheme.NoetherianApproximation.ExtensionData.approximation
        { X := Y.toScheme, U := U, V := V, hUV := hUV, hV := hVaff, N := N, i₀ := i₀,
          W₀ := W₀, hW₀c := hW₀c, hW₀ := hW₀, n := m,
          b := fun l ↦ ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V)),
          hb := fun l ↦ hcov ▸ le_iSup (fun l : Fin m ↦ Y.toScheme.basicOpen
            ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V))) l,
          hb' := hcov }⟩

/-- **Absolute Noetherian approximation** (Stacks Project Tag 01ZA): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case follows by induction over a finite affine cover: each step extends an
approximation of a quasi-compact open across one more affine open, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.approximation`.
(Blueprint: `prop:nagata-noetherian-inverse-system`.) -/
@[stacks 01ZA]
theorem Scheme.nonempty_noetherianApproximation (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty S.NoetherianApproximation := by
  classical
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    S.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) (by simpa using isCompact_univ)
  obtain ⟨N⟩ := nonempty_noetherianApproximation_finsetSup hUsfin.toFinset
    (fun V hV ↦ hUsB (hUsfin.mem_toFinset.mp hV))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at N
  exact ⟨N.ofIso S.topIso⟩

section BaseChangeLimit

/-!
### Base change of a cofiltered limit

A cofiltered limit `lim Dⱼ` of schemes stays a limit after base change along a morphism
`p : Y ⟶ Dᵢ` to one of the stages: `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system
`{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. This is `AlgebraicGeometry.isLimitBaseChangeCone`; it is what
makes the results on cofiltered limits of schemes available for the descent of a scheme
over `lim Dⱼ` to a finite stage.
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)

set_option backward.defeqAttrib.useBackward true in
/-- Blueprint `theorem-nagata-s-compactification-theorem--1`: Base-changed system over a chosen
stage.

The base change `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}` of the diagram `{ Dⱼ }` along a morphism
`p : Y ⟶ Dᵢ`, indexed by the cofinal subsystem `Over i`; its transition maps are the base
changes of the transitions of `D`. The limit `Y ×_{Dᵢ} lim Dⱼ` is `baseChangeCone`. -/
@[simps] noncomputable def baseChangeDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback p (D.map j.hom)
  map {j k} f := pullback.map _ _ _ _ (𝟙 Y) (D.map f.left) (𝟙 _)
    (by simp) (by simp [← D.map_comp, Over.w f])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The projection from the base changed diagram to the original diagram. -/
@[simps] noncomputable def baseChangeDiagramπ :
    baseChangeDiagram D p ⟶ Over.forget i ⋙ D where
  app j := pullback.snd _ _

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The cone with point `Y ×_{Dᵢ} lim Dⱼ` over the base changed diagram. -/
@[simps] noncomputable def baseChangeCone : Cone (baseChangeDiagram D p) where
  pt := pullback p (c.π.app i)
  π.app j := pullback.map _ _ _ _ (𝟙 Y) (c.π.app j.left) (𝟙 _) (by simp) (by simp)
  π.naturality {j k} f := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.fst p (D.map k.hom) =
      pullback.fst p (D.map j.hom) := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.snd p (D.map k.hom) =
      pullback.snd p (D.map j.hom) ≫ D.map f.left := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_fst (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.fst p (D.map j.hom) =
      pullback.fst p (c.π.app i) := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_snd (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.snd p (D.map j.hom) =
      pullback.snd p (c.π.app i) ≫ c.π.app j.left := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeDiagram_map {j k : Over i} (f : j ⟶ k) :
    IsPullback ((baseChangeDiagram D p).map f) (pullback.snd p (D.map j.hom))
      (pullback.snd p (D.map k.hom)) (D.map f.left) :=
  isPullback_pullback_map _ _ _ _ (by rw [← D.map_comp, Over.w f])

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeCone_π (j : Over i) :
    IsPullback ((baseChangeCone D c p).π.app j) (pullback.snd p (c.π.app i))
      ((baseChangeDiagramπ D p).app j) (c.π.app j.left) :=
  isPullback_pullback_map _ _ _ _ (c.w j.hom)

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

include c in
/-- **Base change of a cofiltered limit of schemes.** If `lim Dⱼ` is a cofiltered limit and
`p : Y ⟶ Dᵢ`, then `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. -/
noncomputable def isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (baseChangeCone D c p) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramπ D p) _ (c.whisker (Over.forget i))
    { hom := pullback.snd p (c.π.app i)
      w := fun j ↦ by simp }
    (isPullback_baseChangeCone_π D c p)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChangeDiagram_map D p f).flip
    inferInstance

end BaseChangeLimit

section FinitePresentation

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Objects of finite presentation descend to a finite stage, affine case.**

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps and
let `X` be an affine scheme that is locally of finite presentation over `lim Dᵢ`. Then `X` is
the base change of an affine scheme `Y` that is locally of finite presentation over some
`Dᵢ`. -/
@[stacks 01ZM]
lemma Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [LocallyOfFinitePresentation g] :
    ∃ (i : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation p) (h : X ⟶ Y), IsPullback h g p (c.π.app i) := by
  have hcpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- Reduce to the case where `X` is the spectrum of a ring.
  wlog hX : ∃ A, X = Spec A generalizing X
  · obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (X := Spec Γ(X, ⊤)) (X.isoSpec.inv ≫ g) ⟨_, rfl⟩
    refine ⟨i, Y, hYaff, p, hp, X.isoSpec.hom ≫ h, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := X.isoSpec.hom) (snd := g)
      (f := X.isoSpec.inv ≫ g) (g := 𝟙 c.pt) ⟨by simp⟩).paste_horiz hsq
  obtain ⟨A, rfl⟩ := hX
  -- Reduce to the case where the diagram is the spectrum of a diagram of rings.
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := IsAffine.affine
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    have inst : ∀ {i j : I} (f : i ⟶ j),
        IsAffineHom ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map f) := fun f ↦ inferInstance
    have hg : @LocallyOfFinitePresentation (Spec A)
        ((Cone.postcompose (asIso e).hom).obj c).pt g := ‹_›
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      hcpt g ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    have : LocallyOfFinitePresentation (p ≫ inv (e.app i)) := by
      have := hp; infer_instance
    refine ⟨i, Y, hYaff, p ≫ inv (e.app i), this, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (e.app i)).symm
      (by simp) (Category.comp_id g) (by simp) ?_
    change (c.π.app i ≫ e.app i) ≫ inv (e.app i) = 𝟙 _ ≫ c.π.app i
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (c.π.app i)).symm
  obtain ⟨D, rfl⟩ := hD
  -- Reduce to the case where the limit cone is the spectrum of a colimit cocone of rings.
  wlog hc' : ∃ c' : Cocone D.leftOp, c = Scheme.Spec.mapCone (coneOfCoconeLeftOp c')
    generalizing c
  · let β : c.pt ≅ Spec Γ(c.pt, ⊤) := c.pt.isoSpec
    let φ : ∀ i : Iᵒᵖ, D.leftOp.obj i ⟶ Γ(c.pt, ⊤) :=
      fun i ↦ (Scheme.Spec.preimage (β.inv ≫ c.π.app i.unop)).unop
    have hφ : ∀ i : Iᵒᵖ, Spec.map (φ i) = β.inv ≫ c.π.app i.unop :=
      fun i ↦ Scheme.Spec.map_preimage _
    let c' : Cocone D.leftOp :=
      { pt := Γ(c.pt, ⊤)
        ι :=
        { app := φ
          naturality i j f := by
            apply Quiver.Hom.op_inj
            apply Scheme.Spec.map_injective
            change Spec.map (D.leftOp.map f ≫ φ j) = Spec.map (φ i ≫ 𝟙 _)
            rw [Spec.map_comp, Spec.map_comp, hφ, hφ, Spec.map_id, Category.id_comp]
            exact (Category.assoc _ _ _).trans (congrArg (β.inv ≫ ·) (c.w f.unop)) } }
    have hcc : c ≅ Scheme.Spec.mapCone (coneOfCoconeLeftOp c') :=
      Cone.ext β fun i ↦ by
        change c.π.app i = β.hom ≫ Spec.map (φ (Opposite.op i))
        rw [hφ]
        exact (Iso.hom_inv_id_assoc β (c.π.app i)).symm
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (Scheme.Spec.mapCone (coneOfCoconeLeftOp c'))
      (IsLimit.ofIsoLimit hc hcc) (inferInstanceAs (IsAffine (Spec Γ(c.pt, ⊤))))
      (g ≫ β.hom) ⟨c', rfl⟩
    refine ⟨i, Y, hYaff, p, hp, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) β.symm (Iso.refl _) (by simp) (by simp)
      (by simp) ?_
    change Spec.map (φ (Opposite.op i)) ≫ 𝟙 _ = β.inv ≫ c.π.app i
    rw [Category.comp_id]
    exact hφ (Opposite.op i)
  obtain ⟨c', rfl⟩ := hc'
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  replace hc := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects Scheme.Spec hc)
  obtain ⟨i, T, γ, hγ, h, hpush⟩ := CommRingCat.exists_isPushout_of_finitePresentation
    D.leftOp c' hc ψ (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map ψ)›)
  refine ⟨i.unop, Spec T, inferInstance, Spec.map γ, HasRingHomProperty.Spec_iff.mpr hγ,
    Spec.map h, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

include hc in
/-- **Closed subschemes of finite presentation descend to a finite stage, affine case.**

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps and
let `g : X ⟶ lim Dᵢ` be a closed immersion that is locally of finite presentation. Then `X`
is the base change of a finitely presented closed subscheme of some `Dᵢ`. -/
lemma Scheme.exists_isPullback_of_isClosedImmersion_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} (g : X ⟶ c.pt) [LocallyOfFinitePresentation g] [IsClosedImmersion g] :
    ∃ (i : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation p) (_ : IsClosedImmersion p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  have hcpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- Reduce to the case where `X` is the spectrum of a ring.
  wlog hX : ∃ A, X = Spec A generalizing X
  · have hXaff : IsAffine X := isAffine_of_isAffineHom g
    obtain ⟨i, Y, hYaff, p, hp, hpc, h, hsq⟩ :=
      this (X.isoSpec.inv ≫ g) ⟨_, rfl⟩
    refine ⟨i, Y, hYaff, p, hp, hpc, X.isoSpec.hom ≫ h, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := X.isoSpec.hom) (snd := g)
      (f := X.isoSpec.inv ≫ g) (g := 𝟙 c.pt) ⟨by simp⟩).paste_horiz hsq
  obtain ⟨A, rfl⟩ := hX
  -- Reduce to the case where the diagram is the spectrum of a diagram of rings.
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := IsAffine.affine
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    have inst : ∀ {i j : I} (f : i ⟶ j),
        IsAffineHom ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map f) := fun f ↦ inferInstance
    have hg : @LocallyOfFinitePresentation (Spec A)
        ((Cone.postcompose (asIso e).hom).obj c).pt g := ‹_›
    have hg' : @IsClosedImmersion (Spec A)
        ((Cone.postcompose (asIso e).hom).obj c).pt g := ‹_›
    obtain ⟨i, Y, hYaff, p, hp, hpc, h, hsq⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      hcpt g ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    have hp' : LocallyOfFinitePresentation (p ≫ inv (e.app i)) := by
      have := hp; infer_instance
    have hpc' : IsClosedImmersion (p ≫ inv (e.app i)) := by
      have := hpc; infer_instance
    refine ⟨i, Y, hYaff, p ≫ inv (e.app i), hp', hpc', h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (e.app i)).symm
      (by simp) (Category.comp_id g) (by simp) ?_
    change (c.π.app i ≫ e.app i) ≫ inv (e.app i) = 𝟙 _ ≫ c.π.app i
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (c.π.app i)).symm
  obtain ⟨D, rfl⟩ := hD
  -- Reduce to the case where the limit cone is the spectrum of a colimit cocone of rings.
  wlog hc' : ∃ c' : Cocone D.leftOp, c = Scheme.Spec.mapCone (coneOfCoconeLeftOp c')
      generalizing c
  · let β : c.pt ≅ Spec Γ(c.pt, ⊤) := c.pt.isoSpec
    let φ : ∀ i : Iᵒᵖ, D.leftOp.obj i ⟶ Γ(c.pt, ⊤) :=
      fun i ↦ (Scheme.Spec.preimage (β.inv ≫ c.π.app i.unop)).unop
    have hφ : ∀ i : Iᵒᵖ, Spec.map (φ i) = β.inv ≫ c.π.app i.unop :=
      fun i ↦ Scheme.Spec.map_preimage _
    let c' : Cocone D.leftOp :=
      { pt := Γ(c.pt, ⊤)
        ι :=
        { app := φ
          naturality i j f := by
            apply Quiver.Hom.op_inj
            apply Scheme.Spec.map_injective
            change Spec.map (D.leftOp.map f ≫ φ j) = Spec.map (φ i ≫ 𝟙 _)
            rw [Spec.map_comp, Spec.map_comp, hφ, hφ, Spec.map_id, Category.id_comp]
            exact (Category.assoc _ _ _).trans (congrArg (β.inv ≫ ·) (c.w f.unop)) } }
    have hcc : c ≅ Scheme.Spec.mapCone (coneOfCoconeLeftOp c') :=
      Cone.ext β fun i ↦ by
        change c.π.app i = β.hom ≫ Spec.map (φ (Opposite.op i))
        rw [hφ]
        exact (Iso.hom_inv_id_assoc β (c.π.app i)).symm
    obtain ⟨i, Y, hYaff, p, hp, hpc, h, hsq⟩ := this (Scheme.Spec.mapCone (coneOfCoconeLeftOp c'))
      (IsLimit.ofIsoLimit hc hcc) (inferInstanceAs (IsAffine (Spec Γ(c.pt, ⊤))))
      (g ≫ β.hom) ⟨c', rfl⟩
    refine ⟨i, Y, hYaff, p, hp, hpc, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) β.symm (Iso.refl _) (by simp) (by simp)
      (by simp) ?_
    change Spec.map (φ (Opposite.op i)) ≫ 𝟙 _ = β.inv ≫ c.π.app i
    rw [Category.comp_id]
    exact hφ (Opposite.op i)
  obtain ⟨c', rfl⟩ := hc'
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  replace hc := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects Scheme.Spec hc)
  -- The map of global sections of a closed immersion of affine schemes is surjective.
  have : IsClosedImmersion (Spec.map ψ) := ‹_›
  have hψs : Function.Surjective ψ.hom := by
    obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)
    intro a
    obtain ⟨b, hb⟩ := hsurj ((Scheme.ΓSpecIso A).inv a)
    refine ⟨(Scheme.ΓSpecIso c'.pt).hom b, ?_⟩
    have hnat := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality ψ)) b
    calc ψ.hom ((Scheme.ΓSpecIso c'.pt).hom b)
        = (Scheme.ΓSpecIso A).hom ((Spec.map ψ).appTop.hom b) := hnat.symm
      _ = (Scheme.ΓSpecIso A).hom ((Scheme.ΓSpecIso A).inv a) := by rw [hb]
      _ = a := by simp
  obtain ⟨i, T, γ, hγ, hγs, h, hpush⟩ :=
    CommRingCat.exists_isPushout_of_finitePresentation_of_surjective D.leftOp c' hc ψ
      (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map ψ)›) hψs
  refine ⟨i.unop, Spec T, inferInstance, Spec.map γ, HasRingHomProperty.Spec_iff.mpr hγ,
    IsClosedImmersion.spec_of_surjective γ hγs, Spec.map h, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

end FinitePresentation

section FinitePresentationDescent

/-!
### Descending a scheme of finite presentation to a finite stage

Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and let `X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change
of a scheme of finite presentation over one of the stages (Stacks Project Tag 01ZM,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`). If `X` is moreover
separated over `lim Dⱼ`, the finite-stage model can be chosen separated (Stacks Project
Tag 01ZQ, `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`);
this rests on the fact that a finitely presented morphism whose base change to the limit is a
closed immersion is a closed immersion at a finite stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap`), applied to the diagonal
of the descended model.

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`. It
covers an affine `X` lying over an affine open `V` of a stage, by base changing the whole system
to `V` (`AlgebraicGeometry.DescendsToStage.of_isAffine`). The general case is an induction over
a finite cover of `X` by such affine opens: at each step one has to glue two
finite-stage models along a descent of their intersection. The gluing data is produced by
`AlgebraicGeometry.exists_descendsAtWithOpen` (a quasi-compact open descends) and
`AlgebraicGeometry.exists_iso_of_isPullback` (two finite-stage models of the same scheme become
isomorphic at a later stage), the gluing itself is the pushout of two open immersions of
`AlgebraicGeometry.pushoutOpensDesc`, and that the glued morphism is again cartesian is
`AlgebraicGeometry.isPullback_of_opensRange_sup_eq_top`.
-/

section Descent

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

instance baseChange_compactSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] : CompactSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst p (D.map f)) := inferInstance
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map f))

instance baseChange_quasiSeparatedSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] : QuasiSeparatedSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst p (D.map f)) := inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map f))

instance baseChangeDiagram_compactSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] (j : Over k) : CompactSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (CompactSpace ↥(pullback p (D.map j.hom)))

instance baseChangeDiagram_quasiSeparatedSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] (j : Over k) : QuasiSeparatedSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (QuasiSeparatedSpace ↥(pullback p (D.map j.hom)))

variable (D) in
/-- (Implementation) The structure morphism of the base changed diagram to the stage `i`. -/
@[simps] noncomputable def baseChangeDiagramStructure {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) :
    baseChangeDiagram D p ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := pullback.fst _ _ ≫ p

include hc in
/-- (Implementation) **Two finite-stage models of a scheme over the limit become isomorphic at
a later stage.** -/
lemma exists_iso_of_isPullback {X : Scheme.{u}} {g : X ⟶ c.pt} {k : I}
    {Y₁ Y₂ : Scheme.{u}} {p₁ : Y₁ ⟶ D.obj k} {p₂ : Y₂ ⟶ D.obj k} {h₁ : X ⟶ Y₁} {h₂ : X ⟶ Y₂}
    [LocallyOfFinitePresentation p₁] [LocallyOfFinitePresentation p₂]
    [CompactSpace Y₁] [QuasiSeparatedSpace Y₁] [CompactSpace Y₂] [QuasiSeparatedSpace Y₂]
    (H₁ : IsPullback h₁ g p₁ (c.π.app k)) (H₂ : IsPullback h₂ g p₂ (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {Y₁' Y₂' : Scheme.{u}} {p₁' : Y₁' ⟶ D.obj k'} {q₁ : Y₁' ⟶ Y₁}
      {p₂' : Y₂' ⟶ D.obj k'} {q₂ : Y₂' ⟶ Y₂} {h₁' : X ⟶ Y₁'} {h₂' : X ⟶ Y₂'},
      IsPullback q₁ p₁' p₁ (D.map f) → h₁' ≫ q₁ = h₁ → h₁' ≫ p₁' = g ≫ c.π.app k' →
      IsPullback q₂ p₂' p₂ (D.map f) → h₂' ≫ q₂ = h₂ → h₂' ≫ p₂' = g ≫ c.π.app k' →
      ∃ e : Y₁' ≅ Y₂', e.hom ≫ p₂' = p₁' ∧ h₁' ≫ e.hom = h₂' := by
  classical
  have hi₁fst : H₁.isoPullback.hom ≫ pullback.fst p₁ (c.π.app k) = h₁ :=
    IsPullback.isoPullback_hom_fst _
  have hi₁snd : H₁.isoPullback.hom ≫ pullback.snd p₁ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hi₂fst : H₂.isoPullback.hom ≫ pullback.fst p₂ (c.π.app k) = h₂ :=
    IsPullback.isoPullback_hom_fst _
  have hi₂snd : H₂.isoPullback.hom ≫ pullback.snd p₂ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hinvg₁ : H₁.isoPullback.inv ≫ g = pullback.snd p₁ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₁snd]
  have hinvg₂ : H₂.isoPullback.inv ≫ g = pullback.snd p₂ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₂snd]
  -- descend the two comparison morphisms
  obtain ⟨j₁, u₁, hu₁a, hu₁t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₂ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc) (H₁.isoPullback.inv ≫ h₂) (by
    ext j
    change ((baseChangeCone D c p₁).π.app j ≫ pullback.fst p₁ (D.map j.hom)) ≫ p₁ =
      (H₁.isoPullback.inv ≫ h₂) ≫ p₂
    rw [baseChangeCone_π_app_fst, Category.assoc, H₂.w, ← Category.assoc, hinvg₁]
    exact pullback.condition)
  obtain ⟨j₂, u₂, hu₂a, hu₂t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₁ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc) (H₂.isoPullback.inv ≫ h₁) (by
    ext j
    change ((baseChangeCone D c p₂).π.app j ≫ pullback.fst p₂ (D.map j.hom)) ≫ p₂ =
      (H₂.isoPullback.inv ≫ h₁) ≫ p₁
    rw [baseChangeCone_π_app_fst, Category.assoc, H₁.w, ← Category.assoc, hinvg₂]
    exact pullback.condition)
  -- move them to a common stage
  set j₃ := IsCofiltered.min j₁ j₂ with hj₃
  set m₁ : j₃ ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂ with hm₁
  set m₂ : j₃ ⟶ j₂ := IsCofiltered.minToRight j₁ j₂ with hm₂
  have hu₁t' : u₁ ≫ p₂ = pullback.fst p₁ (D.map j₁.hom) ≫ p₁ := hu₁t
  have hu₂t' : u₂ ≫ p₁ = pullback.fst p₂ (D.map j₂.hom) ≫ p₂ := hu₂t
  set v₁ : (baseChangeDiagram D p₁).obj j₃ ⟶ (baseChangeDiagram D p₂).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₁).map m₁ ≫ u₁) (pullback.snd p₁ (D.map j₃.hom))
      (by rw [Category.assoc, hu₁t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₁def
  set v₂ : (baseChangeDiagram D p₂).obj j₃ ⟶ (baseChangeDiagram D p₁).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₂).map m₂ ≫ u₂) (pullback.snd p₂ (D.map j₃.hom))
      (by rw [Category.assoc, hu₂t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₂def
  have hv₁fst : v₁ ≫ pullback.fst p₂ (D.map j₃.hom) = (baseChangeDiagram D p₁).map m₁ ≫ u₁ :=
    pullback.lift_fst ..
  have hv₁snd : v₁ ≫ pullback.snd p₂ (D.map j₃.hom) = pullback.snd p₁ (D.map j₃.hom) :=
    pullback.lift_snd ..
  have hv₂fst : v₂ ≫ pullback.fst p₁ (D.map j₃.hom) = (baseChangeDiagram D p₂).map m₂ ≫ u₂ :=
    pullback.lift_fst ..
  have hv₂snd : v₂ ≫ pullback.snd p₁ (D.map j₃.hom) = pullback.snd p₂ (D.map j₃.hom) :=
    pullback.lift_snd ..
  -- after base change to the limit they are the identifications with `X`
  have key₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ =
      H₁.isoPullback.inv ≫ H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁fst, ← Category.assoc, (baseChangeCone D c p₁).w m₁, hu₁a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hv₁snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₂.isoPullback.hom, hi₂snd,
        ← Category.assoc, hinvg₁]
  have key₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ =
      H₂.isoPullback.inv ≫ H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₂fst, ← Category.assoc, (baseChangeCone D c p₂).w m₂, hu₂a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hv₂snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₁.isoPullback.hom, hi₁snd,
        ← Category.assoc, hinvg₂]
  have hw₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ v₂ = (baseChangeCone D c p₁).π.app j₃ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, key₂, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  have hw₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ ≫ v₁ = (baseChangeCone D c p₂).π.app j₃ := by
    rw [← Category.assoc, key₂, Category.assoc, Category.assoc, key₁, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  -- the two composites become the identity at a later stage
  obtain ⟨j₄, n₁, hn₁⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₁ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc)
      (v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom)) (pullback.fst p₁ (D.map j₃.hom))
      (by
        change pullback.fst p₁ (D.map j₃.hom) ≫ p₁ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
          ← Category.assoc, hv₁snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₁ (D.map j₃.hom)) hw₁
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₅, n₂, hn₂⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₂ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc)
      (v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom)) (pullback.fst p₂ (D.map j₃.hom))
      (by
        change pullback.fst p₂ (D.map j₃.hom) ≫ p₂ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
          ← Category.assoc, hv₂snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₂ (D.map j₃.hom)) hw₂
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₇, e, he⟩ := IsCofilteredOrEmpty.cone_maps
    (IsCofiltered.minToLeft j₄ j₅ ≫ n₁) (IsCofiltered.minToRight j₄ j₅ ≫ n₂)
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : j₇ ⟶ j₃, t = (e ≫ IsCofiltered.minToLeft j₄ j₅) ≫ n₁ ∧
      t = (e ≫ IsCofiltered.minToRight j₄ j₅) ≫ n₂ :=
    ⟨_, rfl, by rw [Category.assoc, he, Category.assoc]⟩
  have hcomp₁ : (baseChangeDiagram D p₁).map t ≫ v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) =
      (baseChangeDiagram D p₁).map t ≫ pullback.fst p₁ (D.map j₃.hom) := by
    rw [ht₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₁]
  have hcomp₂ : (baseChangeDiagram D p₂).map t ≫ v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      (baseChangeDiagram D p₂).map t ≫ pullback.fst p₂ (D.map j₃.hom) := by
    rw [ht₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₂]
  -- the isomorphism at the stage `j₇`
  set V₁ : (baseChangeDiagram D p₁).obj j₇ ⟶ (baseChangeDiagram D p₂).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom))
      (pullback.snd p₁ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₁def
  set V₂ : (baseChangeDiagram D p₂).obj j₇ ⟶ (baseChangeDiagram D p₁).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom))
      (pullback.snd p₂ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₂def
  have hV₁fst : V₁ ≫ pullback.fst p₂ (D.map j₇.hom) =
      (baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₁snd : V₁ ≫ pullback.snd p₂ (D.map j₇.hom) = pullback.snd p₁ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hV₂fst : V₂ ≫ pullback.fst p₁ (D.map j₇.hom) =
      (baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₂snd : V₂ ≫ pullback.snd p₁ (D.map j₇.hom) = pullback.snd p₂ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hnat₁ : V₁ ≫ (baseChangeDiagram D p₂).map t = (baseChangeDiagram D p₁).map t ≫ v₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₁fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₁snd,
        Category.assoc, hv₁snd, baseChangeDiagram_map_snd]
  have hnat₂ : V₂ ≫ (baseChangeDiagram D p₁).map t = (baseChangeDiagram D p₂).map t ≫ v₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₂fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₂snd,
        Category.assoc, hv₂snd, baseChangeDiagram_map_snd]
  have hVV₁ : V₁ ≫ V₂ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₂fst, ← Category.assoc, hnat₁]
      simp only [Category.assoc]
      rw [hcomp₁, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₂snd, hV₁snd, Category.id_comp]
  have hVV₂ : V₂ ≫ V₁ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₁fst, ← Category.assoc, hnat₂]
      simp only [Category.assoc]
      rw [hcomp₂, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₁snd, hV₂snd, Category.id_comp]
  have key₁' : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      H₁.isoPullback.inv ≫ h₂ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
  have hcompat : (H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁ =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · have hlhs : ((H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        simp only [Category.assoc, hV₁fst]
        rw [← Category.assoc ((baseChangeCone D c p₁).π.app j₇), (baseChangeCone D c p₁).w t,
          key₁', Iso.hom_inv_id_assoc]
      have hrhs : (H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        rw [Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
      rw [hlhs, hrhs]
    · rw [Category.assoc, Category.assoc, hV₁snd, baseChangeCone_π_app_snd, ← Category.assoc,
        hi₁snd, Category.assoc, baseChangeCone_π_app_snd, ← Category.assoc, hi₂snd]
  -- transport to arbitrary models of the base changes
  refine ⟨j₇.left, j₇.hom, ?_⟩
  intro Y₁' Y₂' p₁' q₁ p₂' q₂ h₁' h₂' HH₁ hh₁ hh₁' HH₂ hh₂ hh₂'
  have hα₁fst : HH₁.isoPullback.hom ≫ pullback.fst p₁ (D.map j₇.hom) = q₁ :=
    IsPullback.isoPullback_hom_fst _
  have hα₁snd : HH₁.isoPullback.hom ≫ pullback.snd p₁ (D.map j₇.hom) = p₁' :=
    IsPullback.isoPullback_hom_snd _
  have hα₂fst : HH₂.isoPullback.hom ≫ pullback.fst p₂ (D.map j₇.hom) = q₂ :=
    IsPullback.isoPullback_hom_fst _
  have hα₂snd : HH₂.isoPullback.hom ≫ pullback.snd p₂ (D.map j₇.hom) = p₂' :=
    IsPullback.isoPullback_hom_snd _
  have hh₁α : h₁' ≫ HH₁.isoPullback.hom =
      H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₁fst, hh₁, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hα₁snd, hh₁', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₁snd]
  have hh₂α : h₂' ≫ HH₂.isoPullback.hom =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂fst, hh₂, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hα₂snd, hh₂', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₂snd]
  refine ⟨HH₁.isoPullback ≪≫ ⟨V₁, V₂, hVV₁, hVV₂⟩ ≪≫ HH₂.isoPullback.symm, ?_, ?_⟩
  · change HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv ≫ p₂' = p₁'
    rw [show HH₂.isoPullback.inv ≫ p₂' = pullback.snd p₂ (D.map j₇.hom) by
      rw [Iso.inv_comp_eq, hα₂snd], hV₁snd, hα₁snd]
  · change h₁' ≫ HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv = h₂'
    rw [← Category.assoc, ← Category.assoc, hh₁α, hcompat, ← hh₂α, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

variable (D c) in
/-- (Implementation) The comparison morphism to the base change of a finite-stage model. -/
noncomputable def isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    X ⟶ pullback p (D.map f) :=
  pullback.lift h (g ≫ c.π.app k') (by rw [H.w, ← c.w f, Category.assoc])

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_fst {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.fst p (D.map f) = h := pullback.lift_fst ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_snd {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.snd p (D.map f) = g ≫ c.π.app k' := pullback.lift_snd ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma isPullback_isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    IsPullback (isPullbackLift D c f H) g (pullback.snd p (D.map f)) (c.π.app k') := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p (D.map f))
  rw [isPullbackLift_fst, c.w f]
  exact H


variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change along
`lim Dⱼ ⟶ D_k` of a scheme of finite presentation over the stage `D_k`. -/
def DescendsAt (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y), LocallyOfFinitePresentation p ∧
    CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsPullback h g p (c.π.app k)

variable (D c) in
/-- (Implementation) Refinement of `AlgebraicGeometry.DescendsAt` remembering a descent of a
quasi-compact open `W ⊆ X` to a quasi-compact open of the finite-stage model. -/
def DescendsAtWithOpen (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) (W : X.Opens) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y) (O : Y.Opens),
    LocallyOfFinitePresentation p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsPullback h g p (c.π.app k) ∧ IsCompact (O : Set Y) ∧ h ⁻¹ᵁ O = W

variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change of a scheme of
finite presentation over one of the stages. -/
def DescendsToStage {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop := ∃ k, DescendsAt D c k g

omit [IsCofiltered I] in
lemma DescendsAt.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) : DescendsAt D c k' g := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  exact ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq, inferInstance,
    inferInstance, inferInstance, isPullback_isPullbackLift f hsq⟩

omit [IsCofiltered I] in
lemma DescendsAtWithOpen.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    {W : X.Opens} (H : DescendsAtWithOpen D c k g W) : DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, hOc, hO⟩ := H
  have := hp; have := hcpt; have := hqs
  have : QuasiCompact (pullback.fst p (D.map f)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq,
    pullback.fst p (D.map f) ⁻¹ᵁ O, inferInstance, inferInstance, inferInstance,
    isPullback_isPullbackLift f hsq,
    QuasiCompact.isCompact_preimage _ O.isOpen hOc, ?_⟩
  rw [← Scheme.Hom.comp_preimage, isPullbackLift_fst, hO]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsAtWithOpen.descendsAt {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt} {W : X.Opens}
    (H : DescendsAtWithOpen D c k g W) : DescendsAt D c k g := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, -, -⟩ := H
  exact ⟨Y, p, h, hp, hcpt, hqs, hsq⟩


include hc in
/-- (Implementation) A quasi-compact open of a scheme over the limit descends to a
finite stage (Stacks Project Tag 01ZB). -/
lemma exists_descendsAtWithOpen {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ k' : I, DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  have hlim : IsLimit ((baseChangeCone D c p).extend hsq.isoPullback.hom) :=
    (isLimitBaseChangeCone D c p hc).ofIsoLimit
      (Cone.ext hsq.isoPullback.symm (fun j ↦ by simp))
  obtain ⟨j, O, hOc, hO⟩ := exists_preimage_eq (baseChangeDiagram D p) _ hlim W hW
  refine ⟨j.left, pullback p (D.map j.hom), pullback.snd _ _, isPullbackLift D c j.hom hsq, O,
    inferInstance, inferInstance, inferInstance, isPullback_isPullbackLift j.hom hsq, hOc, ?_⟩
  have hmap : isPullbackLift D c j.hom hsq =
      ((baseChangeCone D c p).extend hsq.isoPullback.hom).π.app j := by
    apply pullback.hom_ext <;>
      simp [Cone.extend, IsPullback.isoPullback_hom_fst]
  rw [← hO, hmap]

include hc in
/-- (Implementation) **An affine scheme of finite presentation over the limit that lies over an
affine open of one of the stages descends to a finite stage.**

The system is base changed to the affine open `V ⊆ Dᵢ₀`: the base changed system has affine
stages, so the affine case
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`
applies to it. -/
lemma DescendsToStage.of_isAffine {i₀ : I} {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {V : (D.obj i₀).Opens} (hV : IsAffineOpen V)
    (q : X ⟶ V.toScheme) (hq : q ≫ V.ι = g ≫ c.π.app i₀) : DescendsToStage D c g := by
  have : IsAffine V.toScheme := hV
  have : ∀ j : Over i₀, IsAffine ((baseChangeDiagram D V.ι).obj j) := fun j ↦
    inferInstanceAs (IsAffine (pullback V.ι (D.map j.hom)))
  have hsnd : pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀) = g := pullback.lift_snd ..
  have hmono : MorphismProperty.monomorphisms Scheme.{u} (pullback.snd V.ι (c.π.app i₀)) :=
    inferInstanceAs (Mono _)
  have hcomp : LocallyOfFinitePresentation
      (pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀)) := by
    rw [hsnd]
    exact ‹LocallyOfFinitePresentation g›
  have : @LocallyOfFinitePresentation X (baseChangeCone D c V.ι).pt (pullback.lift q g hq) :=
    MorphismProperty.of_postcomp (W := @LocallyOfFinitePresentation)
      (W' := MorphismProperty.monomorphisms Scheme.{u}) _ (pullback.snd V.ι (c.π.app i₀))
      hmono hcomp
  obtain ⟨j, Y, hYaff, p, hp, h, hsq⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (baseChangeDiagram D V.ι) (baseChangeCone D c V.ι)
      (isLimitBaseChangeCone D c V.ι hc) (pullback.lift q g hq)
  have := hYaff
  have := hp
  have : IsOpenImmersion ((baseChangeDiagramπ D V.ι).app j) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd V.ι (D.map j.hom)))
  have hP : LocallyOfFinitePresentation (p ≫ (baseChangeDiagramπ D V.ι).app j) := inferInstance
  refine ⟨j.left, Y, p ≫ (baseChangeDiagramπ D V.ι).app j, h, hP, inferInstance,
    inferInstance, ?_⟩
  rw [← hsnd]
  exact hsq.paste_vert (isPullback_baseChangeCone_π D c V.ι j)

include hc in
/-- (Implementation) An affine open of a scheme over the limit that lies over an affine open of
one of the stages descends to a finite stage. -/
lemma DescendsToStage.of_isAffineOpen {i₀ : I} {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {W : X.Opens} (hW : IsAffineOpen W)
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (hle : W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c (W.ι ≫ g) := by
  have : IsAffine W.toScheme := hW
  refine DescendsToStage.of_isAffine hc _ hV ((g ≫ c.π.app i₀).resLE V W hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsToStage.comp_iso {X X' : Scheme.{u}} (e : X' ≅ X) {g : X ⟶ c.pt}
    (H : DescendsToStage D c g) : DescendsToStage D c (e.hom ≫ g) := by
  obtain ⟨k, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  refine ⟨k, Y, p, e.hom ≫ h, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback e.hom (e.hom ≫ g) g (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq


include hc in
/-- (Implementation) **The two-open gluing step**: if a scheme over the limit is covered by
two opens with quasi-compact intersection, each of which descends to a finite stage, then it
descends to a finite stage. -/
lemma DescendsToStage.of_sup_eq_top {Z : Scheme.{u}} (gZ : Z ⟶ c.pt) (U V : Z.Opens)
    (hUV : U ⊔ V = ⊤) (hWc : IsCompact ((U ⊓ V : Z.Opens) : Set Z))
    (hU : DescendsToStage D c (U.ι ≫ gZ)) (hV : DescendsToStage D c (V.ι ≫ gZ)) :
    DescendsToStage D c gZ := by
  obtain ⟨k₁, hU⟩ := hU
  obtain ⟨k₂, hV⟩ := hV
  -- the intersection is quasi-compact in each of the two charts
  have hWU : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
    have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    rw [he]
    refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  have hWV : IsCompact ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme) := by
    have he : (V.ι ⁻¹ᵁ U : V.toScheme.Opens) = V.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [he]
    refine V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_right
  -- descend the intersection inside both charts, over a common stage
  obtain ⟨k₃, hU⟩ := exists_descendsAtWithOpen hc hU _ hWU
  obtain ⟨k₄, hV⟩ := exists_descendsAtWithOpen hc hV _ hWV
  replace hU := hU.mono (IsCofiltered.minToLeft k₃ k₄)
  replace hV := hV.mono (IsCofiltered.minToRight k₃ k₄)
  set k := IsCofiltered.min k₃ k₄ with hk
  obtain ⟨YU, pU, hUh, OU, hpU, hcU, hqU, HU, hOUc, hOU⟩ := hU
  obtain ⟨YV, pV, hVh, OV, hpV, hcV, hqV, HV, hOVc, hOV⟩ := hV
  have := hpU; have := hcU; have := hqU; have := hpV; have := hcV; have := hqV
  have : CompactSpace OU.toScheme := isCompact_iff_compactSpace.mp hOUc
  have : CompactSpace OV.toScheme := isCompact_iff_compactSpace.mp hOVc
  have : QuasiSeparatedSpace OU.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OU.ι.isOpenEmbedding
  have : QuasiSeparatedSpace OV.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OV.ι.isOpenEmbedding
  -- the two descended models of the intersection
  have hrangeU : (Scheme.Opens.infHomLeft U V).opensRange = U.ι ⁻¹ᵁ V := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      top_inf_eq]
  have hrangeV : (Scheme.Opens.infHomRight U V).opensRange = V.ι ⁻¹ᵁ U := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      inf_top_eq]
  have hsubU : Set.range (Scheme.Opens.infHomLeft U V ≫ hUh) ⊆ Set.range OU.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hUh ((Scheme.Opens.infHomLeft U V) x) ∈ OU
    have : (Scheme.Opens.infHomLeft U V) x ∈ hUh ⁻¹ᵁ OU := by
      rw [hOU, ← hrangeU]
      exact ⟨x, rfl⟩
    exact this
  have hsubV : Set.range (Scheme.Opens.infHomRight U V ≫ hVh) ⊆ Set.range OV.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hVh ((Scheme.Opens.infHomRight U V) x) ∈ OV
    have : (Scheme.Opens.infHomRight U V) x ∈ hVh ⁻¹ᵁ OV := by
      rw [hOV, ← hrangeV]
      exact ⟨x, rfl⟩
    exact this
  set aU₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OU.toScheme :=
    IsOpenImmersion.lift OU.ι (Scheme.Opens.infHomLeft U V ≫ hUh) hsubU with haU₀
  set aV₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OV.toScheme :=
    IsOpenImmersion.lift OV.ι (Scheme.Opens.infHomRight U V ≫ hVh) hsubV with haV₀
  have HaU : IsPullback aU₀ (Scheme.Opens.infHomLeft U V) OU.ι hUh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubU).symm
      (by rw [Scheme.Opens.opensRange_ι, hOU, hrangeU])
  have HaV : IsPullback aV₀ (Scheme.Opens.infHomRight U V) OV.ι hVh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubV).symm
      (by rw [Scheme.Opens.opensRange_ι, hOV, hrangeV])
  have HWU : IsPullback aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OU.ι ≫ pU) (c.π.app k) := by
    have h := HaU.paste_vert HU
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have HWV : IsPullback aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OV.ι ≫ pV) (c.π.app k) := by
    have h := HaV.paste_vert HV
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  -- the two models of the intersection agree at a later stage
  obtain ⟨k', f', hiso⟩ := exists_iso_of_isPullback hc HWU HWV
  -- base change everything to that stage
  set YU' := pullback pU (D.map f') with hYU'
  set YV' := pullback pV (D.map f') with hYV'
  set pU' : YU' ⟶ D.obj k' := pullback.snd pU (D.map f') with hpU'
  set pV' : YV' ⟶ D.obj k' := pullback.snd pV (D.map f') with hpV'
  set hU' : U.toScheme ⟶ YU' := isPullbackLift D c f' HU with hhU'
  set hV' : V.toScheme ⟶ YV' := isPullbackLift D c f' HV with hhV'
  have HU' : IsPullback hU' (U.ι ≫ gZ) pU' (c.π.app k') := isPullback_isPullbackLift f' HU
  have HV' : IsPullback hV' (V.ι ≫ gZ) pV' (c.π.app k') := isPullback_isPullbackLift f' HV
  set OU' : YU'.Opens := pullback.fst pU (D.map f') ⁻¹ᵁ OU with hOU'
  set OV' : YV'.Opens := pullback.fst pV (D.map f') ⁻¹ᵁ OV with hOV'
  have HqU : IsPullback (pullback.fst pU (D.map f') ∣_ OU) (OU'.ι ≫ pU') (OU.ι ≫ pU)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pU (D.map f')) OU).paste_vert
      (IsPullback.of_hasPullback pU (D.map f'))
  have HqV : IsPullback (pullback.fst pV (D.map f') ∣_ OV) (OV'.ι ≫ pV') (OV.ι ≫ pV)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pV (D.map f')) OV).paste_vert
      (IsPullback.of_hasPullback pV (D.map f'))
  set h₁' : (U ⊓ V : Z.Opens).toScheme ⟶ OU'.toScheme :=
    HqU.lift aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWU.w]; simp only [Category.assoc]; rw [c.w f']) with hh₁'
  set h₂' : (U ⊓ V : Z.Opens).toScheme ⟶ OV'.toScheme :=
    HqV.lift aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWV.w]; simp only [Category.assoc]; rw [c.w f']) with hh₂'
  obtain ⟨e, he₁, he₂⟩ := hiso (h₁' := h₁') (h₂' := h₂') HqU
    (by rw [hh₁']; exact IsPullback.lift_fst ..)
    (by rw [hh₁', IsPullback.lift_snd, Category.assoc]) HqV
    (by rw [hh₂']; exact IsPullback.lift_fst ..)
    (by rw [hh₂', IsPullback.lift_snd, Category.assoc])
  -- glue the two charts along the descended intersection
  have hOU'c : IsCompact ((OU' : YU'.Opens) : Set YU') := by
    have : QuasiCompact (pullback.fst pU (D.map f')) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    rw [hOU']
    exact QuasiCompact.isCompact_preimage _ OU.isOpen hOUc
  have : CompactSpace ↥(OU'.toScheme) := isCompact_iff_compactSpace.mp hOU'c
  have hcomm : OU'.ι ≫ pU' = (e.hom ≫ OV'.ι) ≫ pV' := by rw [Category.assoc, he₁]
  have hpreU : hU' ⁻¹ᵁ OU' = U.ι ⁻¹ᵁ V := by
    rw [hOU', ← Scheme.Hom.comp_preimage, hhU', isPullbackLift_fst, hOU]
  have hpreV : hV' ⁻¹ᵁ OV' = V.ι ⁻¹ᵁ U := by
    rw [hOV', ← Scheme.Hom.comp_preimage, hhV', isPullbackLift_fst, hOV]
  have hcommU : Scheme.Opens.infHomLeft U V ≫ hU' = h₁' ≫ OU'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhU', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pU (D.map f')) OU, ← Category.assoc, hh₁',
        IsPullback.lift_fst, haU₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhU', isPullbackLift_snd, Category.assoc]
      change _ = h₁' ≫ OU'.ι ≫ pU'
      rw [← Category.assoc, hh₁', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomLeft U V), Scheme.homOfLE_ι]
  have hcommV' : Scheme.Opens.infHomRight U V ≫ hV' = h₂' ≫ OV'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhV', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pV (D.map f')) OV, ← Category.assoc, hh₂',
        IsPullback.lift_fst, haV₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhV', isPullbackLift_snd, Category.assoc]
      change _ = h₂' ≫ OV'.ι ≫ pV'
      rw [← Category.assoc, hh₂', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomRight U V), Scheme.homOfLE_ι]
  have hcommV : Scheme.Opens.infHomRight U V ≫ hV' = h₁' ≫ e.hom ≫ OV'.ι := by
    rw [← Category.assoc, he₂, hcommV']
  have HsqU : IsPullback h₁' (Scheme.Opens.infHomLeft U V) OU'.ι hU' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommU
      (by rw [Scheme.Opens.opensRange_ι, hpreU, hrangeU])
  have HsqV : IsPullback h₁' (Scheme.Opens.infHomRight U V) (e.hom ≫ OV'.ι) hV' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommV
      (by
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι, hpreV, hrangeV])
  -- the glued finite-stage model
  have hf : h₁' ≫ OU'.ι = Scheme.Opens.infHomLeft U V ≫ hU' := hcommU.symm
  have hg : h₁' ≫ (e.hom ≫ OV'.ι) = Scheme.Opens.infHomRight U V ≫ hV' := hcommV.symm
  set p : pushout OU'.ι (e.hom ≫ OV'.ι) ⟶ D.obj k' := pushout.desc pU' pV' hcomm with hp
  set ρ := pushout.map (Scheme.Opens.infHomLeft U V)
    (Scheme.Opens.infHomRight U V) OU'.ι (e.hom ≫ OV'.ι) hU' hV' h₁'
    hf.symm hg.symm with hρ
  have hchartU := isPullback_pushout_map_inl_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqV
  have hchartV := isPullback_pushout_map_inr_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqU
  have hw : ρ ≫ p = (pushoutOpensDesc U V ≫ gZ) ≫ c.π.app k' := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hρ, pushout.inl_desc, Category.assoc, hp, pushout.inl_desc]
      have hw' := HU'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inl_pushoutOpensDesc_assoc]
      exact hw'
    · rw [← Category.assoc, hρ, pushout.inr_desc, Category.assoc, hp, pushout.inr_desc]
      have hw' := HV'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inr_pushoutOpensDesc_assoc]
      exact hw'
  have hmain : IsPullback ρ (pushoutOpensDesc U V ≫ gZ) p (c.π.app k') := by
    refine isPullback_of_opensRange_sup_eq_top hw (pushout.inl OU'.ι (e.hom ≫ OV'.ι))
      (pushout.inr OU'.ι (e.hom ≫ OV'.ι))
      (opensRange_pushout_inl_sup_opensRange_pushout_inr OU'.ι (e.hom ≫ OV'.ι))
      hchartU hchartV ?_ ?_
    · rw [inl_pushoutOpensDesc_assoc, hp, pushout.inl_desc]
      exact HU'
    · rw [inr_pushoutOpensDesc_assoc, hp, pushout.inr_desc]
      exact HV'
  have := isIso_pushoutOpensDesc U V hUV
  refine ⟨k', pushout OU'.ι (e.hom ≫ OV'.ι), p, inv (pushoutOpensDesc U V) ≫ ρ,
    IsZariskiLocalAtSource.pushout_desc OU'.ι (e.hom ≫ OV'.ι) hcomm inferInstance inferInstance,
    inferInstance,
    quasiSeparatedSpace_pushout OU'.ι (e.hom ≫ OV'.ι), ?_⟩
  have hiso : IsPullback (inv (pushoutOpensDesc U V)) gZ (pushoutOpensDesc U V ≫ gZ)
      (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hmain

include hc in
/-- (Implementation) **Descent to a finite stage for a finite union of affine opens**, each of
which lies over an affine open of the stage `i₀`. -/
lemma descendsToStage_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X] {i₀ : I} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] (s : Finset X.Opens)
    (hs : ∀ W ∈ s, IsAffineOpen W ∧
      ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c ((s.sup id : X.Opens).ι ≫ g) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      exact DescendsToStage.of_isAffineOpen hc g (isAffineOpen_bot X)
        (isAffineOpen_bot (D.obj i₀)) bot_le
  | insert a s ha ih =>
      obtain ⟨haff, Va, hVa, hale⟩ := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ W ∈ s, IsAffineOpen W ∧
          ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V :=
        fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      rw [Finset.sup_insert, id]
      set Z : X.Opens := a ⊔ s.sup id with hZ
      have : QuasiSeparatedSpace Z.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding Z.ι.isOpenEmbedding
      set U : Z.toScheme.Opens := Z.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Z.toScheme.Opens := Z.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hZ,
          Scheme.Opens.ι_preimage_self]
      -- the intersection is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun W hW ↦ (hsaff W hW).1.isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Z.toScheme.Opens) : Set Z.toScheme) := by
        have he : (U ⊓ V : Z.toScheme.Opens) = Z.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Z.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      refine DescendsToStage.of_sup_eq_top hc (Z.ι ≫ g) U V hUV hUVc ?_ ?_
      · -- the first open is the union over `s`, which descends by the induction hypothesis
        have hrange : Set.range (U.ι ≫ Z.ι) = Set.range (s.sup id : X.Opens).ι := by
          rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
          congr 1
          simp only [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hUdef,
            Scheme.Hom.image_preimage_eq_opensRange_inf, hZ]
          exact inf_eq_right.mpr (le_sup_right : (s.sup id : X.Opens) ≤ a ⊔ s.sup id)
        have := DescendsToStage.comp_iso
          (IsOpenImmersion.isoOfRangeEq (U.ι ≫ Z.ι) (s.sup id : X.Opens).ι hrange) (ih hsaff)
        rwa [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc] at this
      · -- the second open is affine and lies over an affine open of the stage `i₀`
        refine DescendsToStage.of_isAffineOpen hc (Z.ι ≫ g) ?_ hVa ?_
        · refine haff.preimage_of_isOpenImmersion Z.ι ?_
          rw [Scheme.Opens.opensRange_ι, hZ]
          exact le_sup_left
        · rw [Category.assoc, Scheme.Hom.comp_preimage]
          exact Z.ι.preimage_mono hale

set_option backward.isDefEq.respectTransparency false in
include hc in
/-- **Schemes of finite presentation over a cofiltered limit of quasi-compact quasi-separated
schemes descend to a finite stage** (Stacks Project Tag 01ZM). Let `{Dⱼ}` be a cofiltered
inverse system of quasi-compact quasi-separated schemes with affine transition maps and let
`X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change of a scheme `Y` of
finite presentation over one of the `Dⱼ`.

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`; the
general case follows by induction over a finite cover of `X` by affine opens each of which
lies over an affine open of a fixed stage, gluing the descended charts over a common stage.
(Blueprint: `lemma:nagata-finite-presentation-descends`;
`proposition-jacobian-over-ground-field--1`, part (1).) -/
@[stacks 01ZM]
theorem Scheme.exists_isPullback_of_finitePresentation [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : QuasiSeparated p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc
  have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (g ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have H := descendsToStage_finsetSup hc (i₀ := i₀) g hUsfin.toFinset
    (fun W hW ↦ hUsB (hUsfin.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at H
  replace H := DescendsToStage.comp_iso X.topIso.symm H
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at H
  obtain ⟨i, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  exact ⟨i, Y, p, hp, inferInstance, inferInstance, h, hsq⟩


include hc in
/-- **A finitely presented closed subscheme of the limit is closed at a finite stage.**

Let `{Dⱼ}` be a cofiltered inverse system of schemes with affine transition maps, let
`q : Z ⟶ D_k` be a morphism of finite presentation to a quasi-compact stage and let
`X = Z ×_{D_k} lim Dⱼ` be its base change to the limit. If `X ⟶ lim Dⱼ` is a closed
immersion, then the base change of `q` to some later stage `k' ⟶ k`, and to every stage
after that, is a closed immersion. -/
lemma Scheme.exists_isClosedImmersion_pullback_snd {k : I} [CompactSpace (D.obj k)]
    {Z : Scheme.{u}} {q : Z ⟶ D.obj k}
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {X : Scheme.{u}} {w : X ⟶ c.pt} [IsClosedImmersion w]
    {h : X ⟶ Z} (H : IsPullback h w q (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {k'' : I} (f' : k'' ⟶ k'),
      IsClosedImmersion (pullback.snd q (D.map (f' ≫ f))) := by
  classical
  have : LocallyOfFinitePresentation w := MorphismProperty.of_isPullback H inferInstance
  set 𝒰 := (D.obj k).affineCover.finiteSubcover with h𝒰
  -- For every affine chart of the base stage, the canonical chart-restricted model of `Z`
  -- becomes a closed immersion at some later stage.
  have key : ∀ a : 𝒰.I₀, ∃ ja : Over k,
      IsClosedImmersion (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) := by
    intro a
    -- The system base changed to the chart has affine stages.
    have : ∀ j : Over k, IsAffine ((baseChangeDiagram D (𝒰.f a)).obj j) := fun j ↦
      inferInstanceAs (IsAffine (pullback (𝒰.f a) (D.map j.hom)))
    -- The base change of `w` to the chart-restricted limit is a finitely presented closed
    -- immersion.
    obtain ⟨wA, hwsq⟩ : ∃ wA : pullback (𝒰.f a) (h ≫ q) ⟶
          (baseChangeCone D c (𝒰.f a)).pt,
        IsPullback wA (pullback.snd (𝒰.f a) (h ≫ q))
          (pullback.snd (𝒰.f a) (c.π.app k)) w :=
      ⟨_, isPullback_pullback_map (𝒰.f a) (h ≫ q) (c.π.app k) w H.w.symm⟩
    have hwA₁ : IsClosedImmersion wA :=
      MorphismProperty.of_isPullback hwsq.flip ‹IsClosedImmersion w›
    have hwA₂ : LocallyOfFinitePresentation wA :=
      MorphismProperty.of_isPullback hwsq.flip ‹LocallyOfFinitePresentation w›
    -- Apply the affine case to obtain a closed immersion model at a stage `ja`.
    obtain ⟨ja, Ya, hYaff, pa, hpa, hpac, ha, Ha⟩ :=
      Scheme.exists_isPullback_of_isClosedImmersion_of_isAffine
        (baseChangeDiagram D (𝒰.f a)) (baseChangeCone D c (𝒰.f a))
        (isLimitBaseChangeCone D c (𝒰.f a) hc) wA
    -- The canonical chart model of `Z` at the stage `ja` is a second finite-stage model.
    have hbot : (baseChangeCone D c (𝒰.f a)).π.app ja ≫
        (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a) =
        pullback.snd (𝒰.f a) (c.π.app k) ≫ c.π.app k := by
      rw [← Category.assoc, baseChangeCone_π_app_fst]
      exact pullback.condition
    have BIG : IsPullback (pullback.snd (𝒰.f a) (h ≫ q) ≫ h) wA q
        ((baseChangeCone D c (𝒰.f a)).π.app ja ≫
          (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      (hwsq.flip.paste_horiz H).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simpa using hbot.symm)
    have hMsq := BIG.of_right'
      (IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    -- Instances for the comparison of the two models.
    have := hYaff
    have := hpa
    have : CompactSpace Ya := inferInstance
    have : QuasiSeparatedSpace Ya := inferInstance
    have : QuasiCompact (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ ‹QuasiCompact q›
    have : QuasiSeparated (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ ‹QuasiSeparated q›
    have : LocallyOfFinitePresentation
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _
        ‹LocallyOfFinitePresentation q›
    have : @LocallyOfFinitePresentation
        (pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        ((baseChangeDiagram D (𝒰.f a)).obj ja)
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) := ‹_›
    have : CompactSpace ↥(pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    have : QuasiSeparatedSpace ↥(pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      quasiSeparatedSpace_of_quasiSeparated
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    -- The two models agree at a later stage `ka`, so the chart model becomes closed there.
    obtain ⟨ka, fa, tail⟩ :=
      exists_iso_of_isPullback (isLimitBaseChangeCone D c (𝒰.f a) hc) Ha hMsq
    obtain ⟨e, he₁, -⟩ := tail
      (IsPullback.of_hasPullback pa ((baseChangeDiagram D (𝒰.f a)).map fa))
      (isPullbackLift_fst fa Ha) (isPullbackLift_snd fa Ha)
      (IsPullback.of_hasPullback (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        ((baseChangeDiagram D (𝒰.f a)).map fa))
      (isPullbackLift_fst fa hMsq) (isPullbackLift_snd fa hMsq)
    have hclosed₁ :
        IsClosedImmersion (pullback.snd pa ((baseChangeDiagram D (𝒰.f a)).map fa)) :=
      MorphismProperty.pullback_snd _ _ hpac
    have hclosed₂ : IsClosedImmersion
        (pullback.snd (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa)) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom, he₁]
      exact hclosed₁
    -- Identify the further base change with the canonical chart model at the stage `ka`.
    have hpaste : IsPullback
        (pullback.fst (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
            ((baseChangeDiagram D (𝒰.f a)).map fa :
              pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom)) ≫
          pullback.fst q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        (pullback.snd (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa :
            pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom)))
        q (pullback.fst (𝒰.f a) (D.map ka.hom) ≫ 𝒰.f a) := by
      have h1 := (IsPullback.of_hasPullback
          (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa :
            pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom))).paste_horiz
        (IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
      exact h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
    have hχ := IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ka.hom) ≫ 𝒰.f a)
    refine ⟨ka, (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk (hpaste.isoIsPullback _ _ hχ) (Iso.refl _)
        (by simp))).mp hclosed₂⟩
  -- Choose a stage below the finitely many chart stages.
  choose ja hja using key
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image ja)
  refine ⟨jstar.left, jstar.hom, ?_⟩
  intro k'' f'
  -- It suffices to prove the claim at the stage `jstar` itself.
  have hlater : IsClosedImmersion (pullback.snd q (D.map jstar.hom)) →
      IsClosedImmersion (pullback.snd q (D.map (f' ≫ jstar.hom))) := fun hj ↦
    MorphismProperty.of_isPullback
      (isPullback_pullback_map q (D.map (f' ≫ jstar.hom)) (D.map jstar.hom) (D.map f')
        (by rw [← D.map_comp])) hj
  apply hlater
  -- The chart models at the stage `jstar` are closed immersions.
  have hstage : ∀ a : 𝒰.I₀,
      IsClosedImmersion (pullback.snd q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)) := by
    intro a
    obtain ⟨g⟩ := hjstar (Finset.mem_image_of_mem ja (Finset.mem_univ a))
    have hsq := isPullback_pullback_map q
      (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)
      (pullback.fst (𝒰.f a) (D.map (ja a).hom) ≫ 𝒰.f a)
      ((baseChangeDiagram D (𝒰.f a)).map g)
      (baseChangeDiagram_map_fst_assoc D (𝒰.f a) g (𝒰.f a))
    exact MorphismProperty.of_isPullback hsq (hja a)
  -- Glue: being a closed immersion is local on the target.
  refine IsZariskiLocalAtTarget.of_openCover (𝒰.pullback₁ (D.map jstar.hom)) ?_
  intro a
  -- The piece of the pulled-back cover is the canonical chart model at `jstar`.
  have h1 := (IsPullback.of_hasPullback (pullback.snd q (D.map jstar.hom))
      ((𝒰.pullback₁ (D.map jstar.hom)).f a)).paste_horiz
    (IsPullback.of_hasPullback q (D.map jstar.hom))
  have h2 : IsPullback
      (pullback.fst (pullback.snd q (D.map jstar.hom)) ((𝒰.pullback₁ (D.map jstar.hom)).f a) ≫
        pullback.fst q (D.map jstar.hom))
      (Scheme.Cover.pullbackHom (𝒰.pullback₁ (D.map jstar.hom))
          (pullback.snd q (D.map jstar.hom)) a ≫
        (pullbackSymmetry (D.map jstar.hom) (𝒰.f a)).hom)
      q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a) := by
    refine h1.of_iso (Iso.refl _) (Iso.refl _)
      (pullbackSymmetry (D.map jstar.hom) (𝒰.f a)) (Iso.refl _) (by simp) ?_ (by simp) ?_
    · simp [Scheme.Cover.pullbackHom]
    · simp [pullback.condition]
  have hχ := IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (h2.isoIsPullback _ _ hχ) (pullbackSymmetry (D.map jstar.hom) (𝒰.f a))
      (IsPullback.isoIsPullback_hom_snd _ _ h2 hχ))).mpr (hstage a)

include hc in
/-- **A finitely presented morphism whose base change to the limit is a closed immersion is a
closed immersion at a finite stage.**

Let `γ` be a morphism of finite presentation between schemes over a stage `D_k`, with
quasi-compact quasi-separated target. If the base change of `γ` to the limit `lim Dⱼ` is a
closed immersion, then so is its base change to some stage `k' ⟶ k` and to every stage after
that. (Blueprint: `lemma:nagata-closed-immersion-stage-exists`.) -/
lemma Scheme.exists_isClosedImmersion_overPullbackMap {k : I}
    {Z Y : Over (D.obj k)} (γ : Z ⟶ Y)
    [LocallyOfFinitePresentation γ.left] [QuasiCompact γ.left] [QuasiSeparated γ.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {k'' : I} (f' : k'' ⟶ k'),
      IsClosedImmersion ((Over.pullback (D.map (f' ≫ f))).map γ).left := by
  classical
  -- The identity-stage model of `γ` over the system base changed to `Y`.
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  have : QuasiCompact (pullback.lift γ.left Z.hom hw) := by rw [hq₀]; infer_instance
  have : QuasiSeparated (pullback.lift γ.left Z.hom hw) := by rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFinitePresentation Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw))
  have hI2 : @QuasiCompact Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (QuasiCompact (pullback.lift γ.left Z.hom hw))
  have hI3 : @QuasiSeparated Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (QuasiSeparated (pullback.lift γ.left Z.hom hw))
  have hI4 : @IsClosedImmersion (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  obtain ⟨k', fA, tail⟩ :=
    @Scheme.exists_isClosedImmersion_pullback_snd (Over k) _ (baseChangeDiagram D Y.hom)
      (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc) _ _
      (Over.mk (𝟙 k)) inferInstance
      Z.left (pullback.lift γ.left Z.hom hw) hI1 hI2 hI3
      (pullback Z.hom (c.π.app k)) ((Over.pullback (c.π.app k)).map γ).left hI4
      (pullback.fst Z.hom (c.π.app k)) hsq
  refine ⟨k'.left, k'.hom, ?_⟩
  intro k'' f'
  have htail := tail (Over.homMk f' : Over.mk (f' ≫ k'.hom) ⟶ k')
  -- Both the resulting closed immersion and the base change of `γ` to the stage `k''` are
  -- pullbacks of `γ.left` along the projection of the stage model of `Y`.
  have hργ : IsPullback (pullback.fst Z.hom (D.map (f' ≫ k'.hom)))
      ((Over.pullback (D.map (f' ≫ k'.hom))).map γ).left γ.left
      (pullback.fst Y.hom (D.map (f' ≫ k'.hom))) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map (f' ≫ k'.hom)))
    · refine (IsPullback.of_hasPullback Z.hom (D.map (f' ≫ k'.hom))).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _)))
      (pullback.snd (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _)))
      γ.left (pullback.fst Y.hom (D.map (f' ≫ k'.hom))) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map
          (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _))).paste_horiz hsq3
    exact h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (hρq.isoIsPullback _ _ hργ) (Iso.refl _)
      (by simp))).mp htail

include hc in
/-- **A finite-presentation model of a separated morphism is separated at a later stage.**

If `X ⟶ lim Dⱼ` is separated and `p : Y ⟶ D_k` is a finite presentation model of it at the
stage `k`, then the base change of the model to some later stage `k' ⟶ k` is separated.
(Blueprint: `lemma:nagata-separated-descent-stage-exists`.) -/
lemma Scheme.exists_isSeparated_pullback_snd {k : I} [CompactSpace (D.obj k)]
    [QuasiSeparatedSpace (D.obj k)] {Y : Scheme.{u}} {p : Y ⟶ D.obj k}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    {X : Scheme.{u}} {g : X ⟶ c.pt} [IsSeparated g] {h : X ⟶ Y}
    (H : IsPullback h g p (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), IsSeparated (pullback.snd p (D.map f)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have : QuasiCompact (pullback.snd p p) := MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiSeparated (pullback.snd p p) := MorphismProperty.pullback_snd _ _ ‹_›
  have : CompactSpace ↥(pullback p p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace ↥(pullback p p) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  -- The diagonal of the model, as a morphism of schemes over the stage.
  let γ : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p) (by simp)
  have : LocallyOfFinitePresentation γ.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.diagonal p))
  have : QuasiCompact γ.left := inferInstanceAs (QuasiCompact (pullback.diagonal p))
  have : QuasiSeparated γ.left := inferInstanceAs (QuasiSeparated (pullback.diagonal p))
  -- The base change of the model to the limit is separated, being isomorphic to `g`.
  have hsep : IsSeparated (pullback.fst (c.π.app k) p) := by
    refine (MorphismProperty.arrow_mk_iso_iff @IsSeparated
      (Arrow.isoMk (H.isoPullback ≪≫ pullbackSymmetry p (c.π.app k)) (Iso.refl _) ?_)).mp
      ‹IsSeparated g›
    simp
  -- Hence the base change of the diagonal to the limit is a closed immersion.
  have hlim : IsClosedImmersion (pullback.diagonal (pullback.fst (c.π.app k) p)) :=
    inferInstance
  rw [diagonal_pullback_fst] at hlim
  have hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left :=
    (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp
      ((MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp hlim)
  have : CompactSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹CompactSpace ↥(pullback p p)›
  have : QuasiSeparatedSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹QuasiSeparatedSpace ↥(pullback p p)›
  obtain ⟨k', f, tail⟩ := Scheme.exists_isClosedImmersion_overPullbackMap hc γ hS
  have htail := tail (𝟙 k')
  rw [Category.id_comp] at htail
  -- Hence the diagonal of the stage model is a closed immersion.
  have hdiag : IsClosedImmersion (pullback.diagonal (pullback.fst (D.map f) p)) := by
    rw [diagonal_pullback_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mpr htail)
  refine ⟨k', f, ?_⟩
  have : IsSeparated (pullback.fst (D.map f) p) := ⟨hdiag⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated
    (pullbackSymmetry (D.map f) p).hom, pullbackSymmetry_hom_comp_snd]
  infer_instance

include hc in
/-- **A separated morphism of finite presentation over the limit descends to a finite stage**
(Stacks 01ZQ).

Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and let `X` be separated and of finite presentation over `lim Dⱼ`. Then `X` is
the base change of a scheme that is separated and of finite presentation over one of the
stages. (Blueprint: `lemma:nagata-separated-eventually`.) -/
@[stacks 01ZQ]
theorem Scheme.exists_isPullback_of_finitePresentation_of_isSeparated
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [IsSeparated g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : IsSeparated p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc g
  have := hp₁; have := hp₂; have := hp₃
  obtain ⟨i', f, hsep⟩ := Scheme.exists_isSeparated_pullback_snd hc H
  exact ⟨i', pullback p (D.map f), pullback.snd p (D.map f), inferInstance, inferInstance,
    hsep, isPullbackLift D c f H, isPullback_isPullbackLift f H⟩

include hc in
/-- **Morphisms between schemes of finite presentation descend to a finite stage**
(Stacks Project Tag 01ZM, part (2)). Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact
quasi-separated schemes with affine transition maps, and let `V`, `W` be of finite presentation
over a stage `Dᵢ`. Every morphism `V ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} lim Dⱼ` over `lim Dⱼ`, given here by
its composite `ψ` with the projection to `W`, is the base change of a morphism
`V ×_{Dᵢ} Dⱼ ⟶ W ×_{Dᵢ} Dⱼ` over some later stage `Dⱼ`.

Part (1) is `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, part (3) is
`AlgebraicGeometry.Scheme.exists_pullback_fst_comp_eq_of_isLimit`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
@[stacks 01ZM]
theorem Scheme.exists_pullback_hom_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {V W : Scheme.{u}} (pV : V ⟶ D.obj i)
    (pW : W ⟶ D.obj i) [LocallyOfFinitePresentation pV] [QuasiCompact pV] [QuasiSeparated pV]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW]
    (ψ : pullback pV (c.π.app i) ⟶ W) (hψ : ψ ≫ pW = pullback.fst pV (c.π.app i) ≫ pV) :
    ∃ (j : I) (f : j ⟶ i) (ψj : pullback pV (D.map f) ⟶ W),
      ψj ≫ pW = pullback.fst pV (D.map f) ≫ pV ∧
        pullback.map pV (c.π.app i) pV (D.map f) (𝟙 V) (c.π.app j) (𝟙 _) (by simp)
          (by simp) ≫ ψj = ψ := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace pV
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated pV
  obtain ⟨j, g, hga, hgt⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D pV) (baseChangeDiagramStructure D pV) pW (baseChangeCone D c pV)
    (isLimitBaseChangeCone D c pV hc) ψ (by
      ext j
      change ((baseChangeCone D c pV).π.app j ≫ pullback.fst pV (D.map j.hom)) ≫ pV = ψ ≫ pW
      rw [baseChangeCone_π_app_fst, hψ])
  exact ⟨j.left, j.hom, g, hgt, hga⟩

include hc in
/-- **Equalities of morphisms between schemes of finite presentation descend to a finite stage**
(Stacks Project Tag 01ZM, part (3)). Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact
quasi-separated schemes with affine transition maps, let `V`, `W` be of finite presentation over a
stage `Dᵢ` and let `ψ χ : V ⟶ W` be morphisms over `Dᵢ` whose base changes to `lim Dⱼ` agree.
Then their base changes to some later stage `Dⱼ` agree.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
@[stacks 01ZM]
theorem Scheme.exists_pullback_fst_comp_eq_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {V W : Scheme.{u}} (pV : V ⟶ D.obj i)
    (pW : W ⟶ D.obj i) [LocallyOfFinitePresentation pV] [QuasiCompact pV] [QuasiSeparated pV]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW] (ψ χ : V ⟶ W)
    (hψ : ψ ≫ pW = pV) (hχ : χ ≫ pW = pV)
    (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ) :
    ∃ (j : I) (f : j ⟶ i), pullback.fst pV (D.map f) ≫ ψ = pullback.fst pV (D.map f) ≫ χ := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace pV
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated pV
  obtain ⟨k, hk, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D pV) (baseChangeDiagramStructure D pV) pW (baseChangeCone D c pV)
    (isLimitBaseChangeCone D c pV hc) (i := Over.mk (𝟙 i))
    (pullback.fst _ _ ≫ ψ) (pullback.fst _ _ ≫ χ)
    (by simp [baseChangeDiagramStructure, hψ]) (by simp [baseChangeDiagramStructure, hχ])
    (by rw [baseChangeCone_π_app_fst_assoc, baseChangeCone_π_app_fst_assoc, h])
  refine ⟨k.left, k.hom, ?_⟩
  simpa using heq

end Descent

end FinitePresentationDescent


section SeparatedDescent

/-!
### Separatedness descends to a finite stage

Stacks Project Tags 086Q and 01ZH.
-/

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- (Implementation) If the preimage in the limit of a quasi-compact open of a stage is affine,
then so is its preimage at some later stage. -/
lemma exists_isAffineOpen_preimage {i₀ : I} {W : (D.obj i₀).Opens}
    (hWc : IsCompact (W : Set (D.obj i₀))) (hW : IsAffineOpen (c.π.app i₀ ⁻¹ᵁ W)) :
    ∃ j : Over i₀, IsAffineOpen (D.map j.hom ⁻¹ᵁ W) := by
  have (j : Over i₀) : CompactSpace ((opensDiagram D i₀ W).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ W.2 hWc)
  have (j : Over i₀) : QuasiSeparatedSpace ((opensDiagram D i₀ W).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i₀ W).pt := hW
  exact Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i₀ W)

section SeparatingPair

variable (i₀ : I) {U V : (D.obj i₀).Opens}

-- descending the finitely many generators through the three systems of opens is a long
-- computation
omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
lemma exists_isSeparatingPair_of_isLimit
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (h : IsSeparatingPair c.pt (c.π.app i₀ ⁻¹ᵁ U) (c.π.app i₀ ⁻¹ᵁ V)) :
    ∃ j : Over i₀, ∀ {k : Over i₀} (_ : k ⟶ j),
      IsSeparatingPair (D.obj k.left) (D.map k.hom ⁻¹ᵁ U) (D.map k.hom ⁻¹ᵁ V) := by
  classical
  set E := opensDiagram D i₀ (U ⊓ V) with hE
  set A := opensDiagram D i₀ U with hA
  set B := opensDiagram D i₀ V with hB
  set cE := opensCone D c i₀ (U ⊓ V) with hcE
  set cA := opensCone D c i₀ U with hcA
  set cB := opensCone D c i₀ V with hcB
  have hlimE : IsLimit cE := isLimitOpensCone D c hc i₀ (U ⊓ V)
  have hlimA : IsLimit cA := isLimitOpensCone D c hc i₀ U
  have hlimB : IsLimit cB := isLimitOpensCone D c hc i₀ V
  have hEaff : ∀ j : Over i₀, IsAffine (E.obj j) := fun j ↦ hUV.preimage (D.map j.hom)
  have hAaff : ∀ j : Over i₀, IsAffine (A.obj j) := fun j ↦ hU.preimage (D.map j.hom)
  have hBaff : ∀ j : Over i₀, IsAffine (B.obj j) := fun j ↦ hV.preimage (D.map j.hom)
  have hleU : ∀ j : Over i₀,
      (D.map j.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j.left).Opens) ≤ D.map j.hom ⁻¹ᵁ U := by
    intro j x hx
    exact hx.1
  have hleV : ∀ j : Over i₀,
      (D.map j.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j.left).Opens) ≤ D.map j.hom ⁻¹ᵁ V := by
    intro j x hx
    exact hx.2
  have hleUlim : (c.π.app i₀ ⁻¹ᵁ (U ⊓ V) : c.pt.Opens) ≤ c.π.app i₀ ⁻¹ᵁ U := by
    intro x hx
    exact hx.1
  have hleVlim : (c.π.app i₀ ⁻¹ᵁ (U ⊓ V) : c.pt.Opens) ≤ c.π.app i₀ ⁻¹ᵁ V := by
    intro x hx
    exact hx.2
  set a : ∀ j : Over i₀, E.obj j ⟶ A.obj j :=
    fun j ↦ (D.obj j.left).homOfLE (hleU j) with ha
  set b : ∀ j : Over i₀, E.obj j ⟶ B.obj j :=
    fun j ↦ (D.obj j.left).homOfLE (hleV j) with hb
  set aLim : cE.pt ⟶ cA.pt := c.pt.homOfLE hleUlim with haLim
  set bLim : cE.pt ⟶ cB.pt := c.pt.homOfLE hleVlim with hbLim
  set R : ∀ j : Over i₀, Subring Γ(E.obj j, ⊤) := fun j ↦
    Subring.closure (Set.range ⇑(a j).appTop.hom ∪ Set.range ⇑(b j).appTop.hom) with hR
  have hpreim : ∀ {j k : Over i₀} (g : k ⟶ j) (W : (D.obj i₀).Opens),
      D.map g.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ W) = D.map k.hom ⁻¹ᵁ W := by
    intro j k g W
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]
  have hpreimlim : ∀ (j : Over i₀) (W : (D.obj i₀).Opens),
      c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ W) = c.π.app i₀ ⁻¹ᵁ W := by
    intro j W
    rw [← Scheme.Hom.comp_preimage, c.w]
  -- the comparison squares
  have sqA : ∀ {j k : Over i₀} (g : k ⟶ j), IsPullback (E.map g) (a k) (a j) (A.map g) := by
    intro j k g
    exact isPullback_resLE_homOfLE (D.map g.left) (hleU j) (hleU k) _ _
      (by rw [hpreim g (U ⊓ V)]; exact inf_le_right)
  have sqB : ∀ {j k : Over i₀} (g : k ⟶ j), IsPullback (E.map g) (b k) (b j) (B.map g) := by
    intro j k g
    exact isPullback_resLE_homOfLE (D.map g.left) (hleV j) (hleV k) _ _
      (by rw [hpreim g (U ⊓ V)]; exact inf_le_right)
  have sqAlim : ∀ j : Over i₀, IsPullback (cE.π.app j) aLim (a j) (cA.π.app j) := by
    intro j
    exact isPullback_resLE_homOfLE (c.π.app j.left) (hleU j) hleUlim _ _
      (by rw [hpreimlim j (U ⊓ V)]; exact inf_le_right)
  have sqBlim : ∀ j : Over i₀, IsPullback (cE.π.app j) bLim (b j) (cB.π.app j) := by
    intro j
    exact isPullback_resLE_homOfLE (c.π.app j.left) (hleV j) hleVlim _ _
      (by rw [hpreimlim j (U ⊓ V)]; exact inf_le_right)
  -- sections at a later stage are generated by those from the earlier stage and those from `U`
  have hgen : ∀ {j k : Over i₀} (g : k ⟶ j),
      Subring.closure (Set.range ⇑(E.map g).appTop.hom ∪ Set.range ⇑(a k).appTop.hom) = ⊤ := by
    intro j k g
    have := hEaff j
    have := hAaff j
    have := hAaff k
    exact CommRingCat.closure_range_union_range_eq_top_of_isPushout
      (isPushout_appTop_of_isPullback (sqA g))
  -- the transition maps respect the subrings `R`
  have hmapR : ∀ {j k : Over i₀} (g : k ⟶ j) (w : Γ(E.obj j, ⊤)), w ∈ R j →
      (E.map g).appTop.hom w ∈ R k := by
    intro j k g w hw
    have hle : R j ≤ Subring.comap (E.map g).appTop.hom (R k) := by
      simp only [hR, Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · refine Subring.subset_closure (Or.inl ⟨(A.map g).appTop.hom z, ?_⟩)
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          ← Scheme.Hom.comp_appTop, (sqA g).w]
      · refine Subring.subset_closure (Or.inr ⟨(B.map g).appTop.hom z, ?_⟩)
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          ← Scheme.Hom.comp_appTop, (sqB g).w]
    exact hle hw
  have hcone : ∀ {j k : Over i₀} (g : k ⟶ j) (w : Γ(E.obj j, ⊤)),
      (cE.π.app k).appTop.hom ((E.map g).appTop.hom w) = (cE.π.app j).appTop.hom w := by
    intro j k g w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, cE.w g]
    rfl
  -- every section over the limit comes from a stage, inside the subring `R`
  have hdesc : ∀ z : Γ(cE.pt, ⊤), ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)),
      w ∈ R j ∧ (cE.π.app j).appTop.hom w = z := by
    have hmerge : ∀ z₁ z₂ : Γ(cE.pt, ⊤),
        (∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z₁) →
        (∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z₂) →
        ∃ (j : Over i₀) (w₁ : Γ(E.obj j, ⊤)) (w₂ : Γ(E.obj j, ⊤)), w₁ ∈ R j ∧ w₂ ∈ R j ∧
          (cE.π.app j).appTop.hom w₁ = z₁ ∧ (cE.π.app j).appTop.hom w₂ = z₂ := by
      rintro z₁ z₂ ⟨j₁, w₁, hw₁, rfl⟩ ⟨j₂, w₂, hw₂, rfl⟩
      obtain ⟨j₃, g₁, g₂, -⟩ := IsCofilteredOrEmpty.cone_objs j₁ j₂
      exact ⟨j₃, (E.map g₁).appTop.hom w₁, (E.map g₂).appTop.hom w₂,
        hmapR g₁ _ hw₁, hmapR g₂ _ hw₂, hcone g₁ w₁, hcone g₂ w₂⟩
    have hS : ∀ z : Γ(cE.pt, ⊤), z ∈ (Subring.closure
        (Set.range ⇑aLim.appTop.hom ∪ Set.range ⇑bLim.appTop.hom)) →
        ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z := by
      intro z hz
      let S : Subring Γ(cE.pt, ⊤) :=
        { carrier := {z | ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧
            (cE.π.app j).appTop.hom w = z}
          one_mem' := ⟨Over.mk (𝟙 i₀), 1, one_mem _, map_one _⟩
          zero_mem' := ⟨Over.mk (𝟙 i₀), 0, zero_mem _, map_zero _⟩
          add_mem' := by
            rintro z₁ z₂ h₁ h₂
            obtain ⟨j, w₁, w₂, hw₁, hw₂, e₁, e₂⟩ := hmerge z₁ z₂ h₁ h₂
            exact ⟨j, w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂]⟩
          mul_mem' := by
            rintro z₁ z₂ h₁ h₂
            obtain ⟨j, w₁, w₂, hw₁, hw₂, e₁, e₂⟩ := hmerge z₁ z₂ h₁ h₂
            exact ⟨j, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, e₁, e₂]⟩
          neg_mem' := by
            rintro z ⟨j, w, hw, rfl⟩
            exact ⟨j, -w, neg_mem hw, by rw [map_neg]⟩ }
      have hsub : Subring.closure
          (Set.range ⇑aLim.appTop.hom ∪ Set.range ⇑bLim.appTop.hom) ≤ S := by
        rw [Subring.closure_le]
        rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
        · obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit A cA hlimA x
          refine ⟨j, (a j).appTop.hom t, Subring.subset_closure (Or.inl ⟨t, rfl⟩), ?_⟩
          have h2 : (a j).appTop ≫ (cE.π.app j).appTop
              = (cA.π.app j).appTop ≫ aLim.appTop := by
            rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, (sqAlim j).w]
          rw [← ht]
          exact congrArg (fun φ : Γ(A.obj j, ⊤) ⟶ Γ(cE.pt, ⊤) => φ.hom t) h2
        · obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit B cB hlimB x
          refine ⟨j, (b j).appTop.hom t, Subring.subset_closure (Or.inr ⟨t, rfl⟩), ?_⟩
          have h2 : (b j).appTop ≫ (cE.π.app j).appTop
              = (cB.π.app j).appTop ≫ bLim.appTop := by
            rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, (sqBlim j).w]
          rw [← ht]
          exact congrArg (fun φ : Γ(B.obj j, ⊤) ⟶ Γ(cE.pt, ⊤) => φ.hom t) h2
      exact hsub hz
    intro z
    exact hS z (h.ge (Subring.mem_top z))
  -- finitely many generators at the initial stage
  set j₀ : Over i₀ := Over.mk (𝟙 i₀) with hj₀
  have : IsAffine (E.obj j₀) := hEaff j₀
  have : IsAffine (A.obj j₀) := hAaff j₀
  have : LocallyOfFiniteType (a j₀) := by rw [ha]; infer_instance
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top (a j₀)
  -- every generator lies in `R` at a late enough stage
  have key : ∀ x : Γ(E.obj j₀, ⊤), ∃ (j : Over i₀) (g : j ⟶ j₀),
      (E.map g).appTop.hom x ∈ R j := by
    intro x
    obtain ⟨j₁, w, hw, hwz⟩ := hdesc ((cE.π.app j₀).appTop.hom x)
    obtain ⟨g₁⟩ : Nonempty (j₁ ⟶ j₀) := ⟨Over.homMk j₁.hom (Category.comp_id j₁.hom)⟩
    have h1 : (cE.π.app j₁).appTop.hom ((E.map g₁).appTop.hom x - w) = 0 := by
      rw [map_sub, hcone g₁ x, hwz, sub_self]
    have : IsAffine (E.obj j₁) := hEaff j₁
    obtain ⟨j₂, g₂, h2⟩ := exists_appTop_map_eq_zero_of_isLimit E cE hlimE
      ((E.map g₁).appTop.hom x - w) h1
    refine ⟨j₂, g₂ ≫ g₁, ?_⟩
    rw [map_sub, sub_eq_zero] at h2
    have h3 : (E.map (g₂ ≫ g₁)).appTop.hom x
        = (E.map g₂).appTop.hom ((E.map g₁).appTop.hom x) := by
      rw [E.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [h3, h2]
    exact hmapR g₂ _ hw
  choose jj gg hjj using key
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.image jj s)
  refine ⟨jstar, ?_⟩
  have gstar : jstar ⟶ j₀ := Over.homMk jstar.hom (Category.comp_id jstar.hom)
  have hterm : ∀ {j : Over i₀} (m₁ m₂ : j ⟶ j₀), m₁ = m₂ := fun m₁ m₂ ↦
    Over.mkIdTerminal.hom_ext m₁ m₂
  have hRstar : R jstar = ⊤ := by
    rw [eq_top_iff, ← hgen gstar, Subring.closure_le]
    rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · have hz : z ∈ Subring.closure (Set.range ⇑(a j₀).appTop.hom ∪
          (s : Set Γ(E.obj j₀, ⊤))) := hs.ge (Subring.mem_top z)
      have hle : Subring.closure (Set.range ⇑(a j₀).appTop.hom ∪ (s : Set Γ(E.obj j₀, ⊤))) ≤
          Subring.comap (E.map gstar).appTop.hom (R jstar) := by
        rw [Subring.closure_le]
        rintro y (⟨t, rfl⟩ | hy)
        · exact hmapR gstar _ (Subring.subset_closure (Or.inl ⟨t, rfl⟩))
        · obtain ⟨m⟩ := hjstar (Finset.mem_image_of_mem jj hy)
          have h4 := hmapR m _ (hjj y)
          have h5 : (E.map gstar).appTop.hom y
              = (E.map m).appTop.hom ((E.map (gg y)).appTop.hom y) := by
            rw [hterm gstar (m ≫ gg y), E.map_comp, Scheme.Hom.comp_appTop]
            rfl
          change (E.map gstar).appTop.hom y ∈ R jstar
          rw [h5]
          exact h4
      exact hle hz
    · exact Subring.subset_closure (Or.inl ⟨z, rfl⟩)
  intro k gk
  change R k = ⊤
  rw [eq_top_iff, ← hgen gk, Subring.closure_le]
  rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
  · exact hmapR gk z (hRstar.ge (Subring.mem_top z))
  · exact Subring.subset_closure (Or.inl ⟨z, rfl⟩)

end SeparatingPair


-- the reduction to the affine criterion goes through two common refinements of stages
include hc in
/-- **Separatedness descends to a finite stage.**

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps. If `lim Dᵢ` is separated, then `Dᵢ` is separated for every `i` past some stage.
(Blueprint: `theorem-nagata-s-compactification-theorem--1`.) -/
@[stacks 086Q]
theorem Scheme.exists_isSeparated_of_isLimit [c.pt.IsSeparated] :
    ∃ i₀ : I, ∀ {i : I} (_ : i ⟶ i₀), (D.obj i).IsSeparated := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : ∀ i, IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc
  set 𝒰 := (D.obj i₀).affineCover.finiteSubcover with h𝒰
  have h𝒰aff : ∀ a : 𝒰.I₀, IsAffine (𝒰.X a) := fun a ↦ inferInstanceAs (IsAffine (Spec _))
  set U : 𝒰.I₀ → (D.obj i₀).Opens := fun a ↦ (𝒰.f a).opensRange with hU
  have haff : ∀ a, IsAffineOpen (U a) := fun a ↦ isAffineOpen_opensRange _
  have hcov : TopologicalSpace.IsOpenCover U := 𝒰.isOpenCover_opensRange
  have hcpt : ∀ a b, IsCompact ((U a ⊓ U b : (D.obj i₀).Opens) : Set (D.obj i₀)) := fun a b ↦
    isQuasiSeparated_univ _ _ (Set.subset_univ _) (U a).2 (haff a).isCompact
      (Set.subset_univ _) (U b).2 (haff b).isCompact
  have haffLim : ∀ a, IsAffineOpen (c.π.app i₀ ⁻¹ᵁ U a) := fun a ↦ (haff a).preimage _
  have haffLimInf : ∀ a b, IsAffineOpen (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)) := fun a b ↦
    IsAffineOpen.inf (X := c.pt) (haffLim a) (haffLim b)
  -- pass to a stage where all the (finitely many) intersections are affine
  have hstage : ∀ a b, ∃ j : Over i₀, IsAffineOpen (D.map j.hom ⁻¹ᵁ (U a ⊓ U b)) := fun a b ↦
    exists_isAffineOpen_preimage hc (hcpt a b) (haffLimInf a b)
  choose jj hjj using hstage
  cases nonempty_fintype 𝒰.I₀
  obtain ⟨i₁, hi₁⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : 𝒰.I₀ × 𝒰.I₀ ↦ jj p.1 p.2) Finset.univ)
  set U' : 𝒰.I₀ → (D.obj i₁.left).Opens := fun a ↦ D.map i₁.hom ⁻¹ᵁ U a with hU'
  have haff' : ∀ a, IsAffineOpen (U' a) := fun a ↦ (haff a).preimage _
  have haffInf' : ∀ a b, IsAffineOpen (U' a ⊓ U' b) := by
    intro a b
    obtain ⟨m⟩ := hi₁ (Finset.mem_image_of_mem _ (Finset.mem_univ (a, b)))
    have : (U' a ⊓ U' b : (D.obj i₁.left).Opens)
        = D.map m.left ⁻¹ᵁ (D.map (jj a b).hom ⁻¹ᵁ (U a ⊓ U b)) := by
      rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w m]
      rfl
    rw [this]
    exact (hjj a b).preimage _
  have hcov' : TopologicalSpace.IsOpenCover U' := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [hU']
    rw [← Scheme.Hom.preimage_iSup, hcov.iSup_eq_top, Scheme.Hom.preimage_top]
  -- the pairs separate in the limit
  have hsep : ∀ a b, IsSeparatingPair c.pt (c.π.app i₁.left ⁻¹ᵁ U' a) (c.π.app i₁.left ⁻¹ᵁ U' b) :=
    fun a b ↦ isSeparatingPair_of_isSeparated ((haff' a).preimage _) ((haff' b).preimage _)
  have hpair : ∀ a b, ∃ j : Over i₁.left, ∀ {k : Over i₁.left} (_ : k ⟶ j),
      IsSeparatingPair (D.obj k.left) (D.map k.hom ⁻¹ᵁ U' a) (D.map k.hom ⁻¹ᵁ U' b) := fun a b ↦
    exists_isSeparatingPair_of_isLimit hc i₁.left (haff' a) (haff' b) (haffInf' a b) (hsep a b)
  choose kk hkk using hpair
  obtain ⟨kstar, hkstar⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : 𝒰.I₀ × 𝒰.I₀ ↦ kk p.1 p.2) Finset.univ)
  refine ⟨kstar.left, ?_⟩
  intro i g
  set k : Over i₁.left := Over.mk (g ≫ kstar.hom) with hk
  have gk : k ⟶ kstar := Over.homMk g
  refine Scheme.isSeparated_of_isSeparatingPair (fun a ↦ D.map k.hom ⁻¹ᵁ U' a) ?_
    (fun a ↦ (haff' a).preimage _) (fun a b ↦ (haffInf' a b).preimage _) ?_
  · refine TopologicalSpace.IsOpenCover.mk ?_
    rw [← Scheme.Hom.preimage_iSup, hcov'.iSup_eq_top, Scheme.Hom.preimage_top]
  · intro a b
    obtain ⟨m⟩ := hkstar (Finset.mem_image_of_mem _ (Finset.mem_univ (a, b)))
    exact hkk a b (gk ≫ m)

variable {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) [∀ i, QuasiCompact (t.app i)]

-- the reduction to the absolute case goes through a finite affine cover of the image
include hc in
/-- **Separatedness over a fixed base descends to a finite stage.**

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes over a base
`S`, with affine transition maps and quasi-compact structure morphisms. If `lim Dᵢ ⟶ S` is
separated, then `Dᵢ ⟶ S` is separated for every `i` past some stage.
(Blueprint: `theorem-nagata-s-compactification-theorem--1`,
`theorem-nagata-s-compactification-theorem--1`.) -/
@[stacks 01ZH]
theorem Scheme.exists_isSeparated_app_of_isLimit (i₀ : I)
    [IsSeparated (c.π.app i₀ ≫ t.app i₀)] :
    ∃ j : I, ∀ {i : I} (_ : i ⟶ j), IsSeparated (t.app i) := by
  classical
  set f : c.pt ⟶ S := c.π.app i₀ ≫ t.app i₀ with hf
  -- finitely many affine opens of `S` covering the image of `D.obj i₀`
  have hcpt : IsCompact (Set.range ⇑(t.app i₀).base) := isCompact_range (t.app i₀).continuous
  obtain ⟨s, hs⟩ := hcpt.elim_finite_subcover (fun V : S.affineOpens ↦ (V : Set S))
    (fun V ↦ (V : S.Opens).2) (by
      intro x _
      have : x ∈ (⊤ : S.Opens) := trivial
      rw [← iSup_affineOpens_eq_top S] at this
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- for every affine open of `S`, the preimages become separated at some stage
  have hstage : ∀ V : S.affineOpens, ∃ j : Over i₀, ∀ {k : Over i₀} (_ : k ⟶ j),
      Scheme.IsSeparated ((D.map k.hom ⁻¹ᵁ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).toScheme) := by
    intro V
    have hVaff : IsAffine (V : S.Opens).toScheme := V.2
    have hWc : IsCompact ((t.app i₀ ⁻¹ᵁ (V : S.Opens) : (D.obj i₀).Opens) : Set (D.obj i₀)) :=
      QuasiCompact.isCompact_preimage _ (V : S.Opens).2 V.2.isCompact
    have : ∀ j : Over i₀,
        CompactSpace ((opensDiagram D i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).obj j) := fun j ↦
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage _ (t.app i₀ ⁻¹ᵁ (V : S.Opens)).2 hWc)
    have : ∀ j : Over i₀,
        QuasiSeparatedSpace ((opensDiagram D i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).obj j) := fun j ↦
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
    have : Scheme.IsSeparated (opensCone D c i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).pt := by
      constructor
      have he : terminal.from ((f ⁻¹ᵁ (V : S.Opens)).toScheme)
          = (f ∣_ (V : S.Opens)) ≫ terminal.from _ := Subsingleton.elim _ _
      change IsSeparated (terminal.from ((f ⁻¹ᵁ (V : S.Opens)).toScheme))
      rw [he]
      infer_instance
    exact Scheme.exists_isSeparated_of_isLimit
      (isLimitOpensCone D c hc i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens)))
  choose jj hjj using hstage
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.image jj s)
  refine ⟨jstar.left, ?_⟩
  intro i g
  set k : Over i₀ := Over.mk (g ≫ jstar.hom) with hk
  have gk : k ⟶ jstar := Over.homMk g
  have hnat : D.map k.hom ≫ t.app i₀ = t.app i := by
    have hn := t.naturality k.hom
    simp only [Functor.const_obj_map] at hn
    exact hn
  set U : S.Opens := ⨆ V ∈ s, (V : S.Opens) with hU
  have hrange : Set.range ⇑(t.app i).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    have : (t.app i).base y = (t.app i₀).base ((D.map k.hom).base y) := by
      rw [← hnat]
      rfl
    rw [this]
    have hmem := hs (Set.mem_range_self ((D.map k.hom).base y))
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨V, hVs, hV⟩ := hmem
    exact hU ▸ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨V, TopologicalSpace.Opens.mem_iSup.mpr ⟨hVs, hV⟩⟩
  set lift := IsOpenImmersion.lift U.ι (t.app i) hrange with hlift
  have hfac : lift ≫ U.ι = t.app i := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac]
  have hsep : IsSeparated lift := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun V : {V // V ∈ s} ↦ U.ι ⁻¹ᵁ (V.1 : S.Opens)) ?_ ?_
    · rw [← Scheme.Opens.ι_preimage_self U, hU, ← Scheme.Hom.preimage_iSup]
      congr 1
      rw [iSup_subtype]
    · intro V
      obtain ⟨m⟩ := hjstar (Finset.mem_image_of_mem jj V.2)
      have h2 := hjj V.1 (gk ≫ m)
      have h1 : lift ⁻¹ᵁ (U.ι ⁻¹ᵁ (V.1 : S.Opens)) = D.map k.hom ⁻¹ᵁ (t.app i₀ ⁻¹ᵁ (V.1 : S.Opens))
          := by rw [← Scheme.Hom.comp_preimage, hfac, ← hnat, Scheme.Hom.comp_preimage]
      have : Scheme.IsSeparated ((lift ⁻¹ᵁ (U.ι ⁻¹ᵁ (V.1 : S.Opens))).toScheme) := by
        rw [h1]; exact h2
      infer_instance
  infer_instance

end SeparatedDescent


section FinitePresentationModel

/-!
## Immersing a finite type scheme into a scheme of finite presentation

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ S` be a morphism locally of
finite type with `X` quasi-compact and quasi-separated. Then `X` immerses over `S` into a
scheme of finite presentation over `S`, see
`AlgebraicGeometry.Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation` (Stacks Project
Tag 01ZE).

The model is built from an absolute Noetherian approximation `X = lim Xⱼ` of `X` itself
(`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`): the model is `Xₖ ×_ℤ S` for a
suitable stage `k`, and the comparison morphism is `(πₖ, f)`. Since `Xₖ` is of finite type over
the Noetherian ring `ℤ`, the model is of finite presentation over `S`. The stage `k` has to be
chosen large enough for the comparison morphism to be an immersion: this needs finitely many
algebra generators of the charts of `X` over the charts of `S` to be defined at the stage `k`.
-/

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- A section over the preimage of an affine open `U` of a stage `D.obj i` comes from a
section over the preimage of `U` at some stage `D.obj j`. -/
lemma exists_appLE_π_app_eq [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) (i : I)
    {U : (D.obj i).Opens} (hU : IsAffineOpen U) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (g : j ⟶ i) (t : Γ(D.obj j, D.map g ⁻¹ᵁ U)),
      ∀ e : c.π.app i ⁻¹ᵁ U ≤ c.π.app j ⁻¹ᵁ (D.map g ⁻¹ᵁ U),
        (c.π.app j).appLE (D.map g ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) e t = s := by
  have haff : ∀ j : Over i, IsAffine ((opensDiagram D i U).obj j) :=
    fun j ↦ hU.preimage (D.map j.hom)
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit (opensDiagram D i U)
    (opensCone D c i U) (isLimitOpensCone D c hc i U) ((c.π.app i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, fun e ↦ ?_⟩
  rw [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at ht
  have h2 := congrArg (c.π.app i ⁻¹ᵁ U).topIso.hom ht
  simp only [CommRingCat.comp_apply] at h2
  simpa [← CommRingCat.comp_apply] using h2

/-- Finitely many sections, each over the preimage of an affine open of a fixed stage
`D.obj i`, all descend to a common stage. -/
lemma exists_hom_forall_mem_range_appLE [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) (i : I)
    {σ : Type*} [Finite σ] {U : σ → (D.obj i).Opens} (hU : ∀ a, IsAffineOpen (U a))
    (s : ∀ a, Γ(c.pt, c.π.app i ⁻¹ᵁ U a)) :
    ∃ (k : I) (g : k ⟶ i), ∀ (a : σ)
      (e : c.π.app i ⁻¹ᵁ U a ≤ c.π.app k ⁻¹ᵁ (D.map g ⁻¹ᵁ U a)),
      s a ∈ Set.range ((c.π.app k).appLE (D.map g ⁻¹ᵁ U a) (c.π.app i ⁻¹ᵁ U a) e) := by
  classical
  cases nonempty_fintype σ
  have hc' : IsLimit (c.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have haff : ∀ {j k : Over i} (g : j ⟶ k),
      IsAffineHom ((Over.forget i ⋙ D).map g) := fun g ↦ by dsimp; infer_instance
  have hA : ∀ a, ∃ (j : Over i) (g : j ⟶ Over.mk (𝟙 i))
      (t : Γ((Over.forget i ⋙ D).obj j, (Over.forget i ⋙ D).map g ⁻¹ᵁ U a)),
      ∀ e : (c.whisker (Over.forget i)).π.app (Over.mk (𝟙 i)) ⁻¹ᵁ U a ≤
        (c.whisker (Over.forget i)).π.app j ⁻¹ᵁ ((Over.forget i ⋙ D).map g ⁻¹ᵁ U a),
        ((c.whisker (Over.forget i)).π.app j).appLE ((Over.forget i ⋙ D).map g ⁻¹ᵁ U a)
          ((c.whisker (Over.forget i)).π.app (Over.mk (𝟙 i)) ⁻¹ᵁ U a) e t = s a :=
    fun a ↦ exists_appLE_π_app_eq hc' (Over.mk (𝟙 i)) (hU a) (s a)
  choose j g t ht using hA
  obtain ⟨k, fk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  have ψ : ∀ a, k ⟶ j a := fun a ↦ (fk (by simp)).some
  refine ⟨k.left, k.hom, fun a e ↦ ?_⟩
  have hw : (ψ a).left ≫ (g a).left = k.hom := by
    simpa using Over.w (ψ a ≫ g a)
  have hRP : (D.map k.hom ⁻¹ᵁ U a : (D.obj k.left).Opens) ≤
      D.map (ψ a).left ⁻¹ᵁ (D.map (g a).left ⁻¹ᵁ U a) := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, hw]
  refine Scheme.Hom.range_appLE_subset_of_comp_eq (c.π.app k.left) (D.map (ψ a).left)
    (c.π.app (j a).left) (c.w (ψ a).left) hRP e ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, c.w]
    exact le_rfl
  · exact ⟨t a, ht a _⟩

open TopologicalSpace in
/-- **The comparison with a stage of a Noetherian approximation is an immersion** (the key step of
Stacks Project Tag 01ZE): if `X` is quasi-compact and quasi-separated, `f : X ⟶ S` is locally of
finite type and `X = lim Xⱼ` is a Noetherian approximation of `X`, then for some stage `k` the
morphism `(πₖ, f) : X ⟶ Xₖ ×_ℤ S` is an immersion. -/
theorem Scheme.Hom.exists_isImmersion_lift_noetherianApproximation {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType f]
    (N : X.NoetherianApproximation) :
    ∃ k : N.I, IsImmersion (pullback.lift (N.π.app k) f (specULiftZIsTerminal.hom_ext _ _) :
      X ⟶ pullback (specULiftZIsTerminal.from (N.D.obj k)) (specULiftZIsTerminal.from S)) := by
  classical
  have hπaff : ∀ j : N.I, IsAffineHom (N.π.app j) :=
    fun j ↦ isAffineHom_π_app N.D (Cone.mk X N.π) N.isLimit j
  -- an affine open cover of `X`, each member mapping into an affine open of `S`
  have key : ∀ x : X, ∃ (Wx : X.Opens) (Vx : S.Opens), IsAffineOpen Wx ∧ IsAffineOpen Vx ∧
      x ∈ Wx ∧ Wx ≤ f ⁻¹ᵁ Vx := by
    intro x
    obtain ⟨_, ⟨Vx, hVx, rfl⟩, hfx, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨Wx, hWx, rfl⟩, hxWx, hlex⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (f ⁻¹ᵁ Vx : X.Opens) from hfx)
        (f ⁻¹ᵁ Vx).isOpen
    exact ⟨Wx, Vx, hWx, hVx, hxWx, hlex⟩
  choose W V hW hV hxW hWV using key
  have hcov : IsOpenCover W := top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  obtain ⟨τ, hτ⟩ := hcov.exists_finite_of_compactSpace
  -- descend the cover to a stage
  obtain ⟨i, U, hUcov, hU⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite N.D
    (Cone.mk X N.π) N.isLimit (fun a : τ ↦ W a.1) hτ (fun a ↦ hW a.1)
  have haff : ∀ a : τ, IsAffineOpen (N.π.app i ⁻¹ᵁ U a) := fun a ↦ (hU a).1.preimage _
  have hle : ∀ a : τ, (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ f ⁻¹ᵁ V a.1 := by
    intro a
    rw [← (hU a).2]
    exact hWV a.1
  -- the sections of `X` over the members of the cover are finitely generated algebras
  have hft : ∀ a : τ, RingHom.FiniteType
      (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom :=
    fun a ↦ HasRingHomProperty.appLE (@LocallyOfFiniteType) f ‹LocallyOfFiniteType f›
      ⟨V a.1, hV a.1⟩ ⟨_, haff a⟩ (hle a)
  have hgen : ∀ a : τ, ∃ gens : Finset Γ(X, N.π.app i ⁻¹ᵁ U a),
      ∀ T : Subring Γ(X, N.π.app i ⁻¹ᵁ U a),
        (∀ r, (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom r ∈ T) →
        (∀ x ∈ gens, x ∈ T) → ∀ z, z ∈ T := by
    intro a
    let := (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom.toAlgebra
    obtain ⟨gens, hgens⟩ := (hft a).out
    refine ⟨gens, fun T h1 h2 z ↦ ?_⟩
    have hT : (⊤ : Subalgebra Γ(S, V a.1) Γ(X, N.π.app i ⁻¹ᵁ U a)) ≤
        (⟨T.toSubsemiring, h1⟩ : Subalgebra Γ(S, V a.1) Γ(X, N.π.app i ⁻¹ᵁ U a)) := by
      rw [← hgens]
      exact Algebra.adjoin_le (fun x hx ↦ h2 x (by simpa using hx))
    exact hT (Algebra.mem_top)
  choose gens hgens using hgen
  -- descend the generators to a common stage
  obtain ⟨k, gk, hk⟩ := exists_hom_forall_mem_range_appLE (D := N.D) (c := Cone.mk X N.π)
    N.isLimit i (σ := Σ a : τ, {x // x ∈ gens a}) (U := fun q ↦ U q.1)
    (fun q ↦ (hU q.1).1) (fun q ↦ q.2.1)
  refine ⟨k, ?_⟩
  set tZ := specULiftZIsTerminal.from (N.D.obj k) with htZ
  set tS := specULiftZIsTerminal.from S with htS
  set u : X ⟶ pullback tZ tS :=
    pullback.lift (N.π.app k) f (specULiftZIsTerminal.hom_ext _ _) with hu
  set A : τ → (N.D.obj k).Opens := fun a ↦ N.D.map gk ⁻¹ᵁ U a with hA
  set O : τ → (pullback tZ tS).Opens :=
    fun a ↦ pullback.fst tZ tS ⁻¹ᵁ A a ⊓ pullback.snd tZ tS ⁻¹ᵁ V a.1 with hO
  have hufst : u ≫ pullback.fst tZ tS = N.π.app k := pullback.lift_fst _ _ _
  have husnd : u ≫ pullback.snd tZ tS = f := pullback.lift_snd _ _ _
  have hpreA : ∀ a : τ, N.π.app k ⁻¹ᵁ A a = N.π.app i ⁻¹ᵁ U a := by
    intro a
    change N.π.app k ⁻¹ᵁ (N.D.map gk ⁻¹ᵁ U a) = _
    have hw : N.π.app k ≫ N.D.map gk = N.π.app i := (Cone.mk X N.π).w gk
    rw [← Scheme.Hom.comp_preimage, hw]
  have hupre : ∀ a : τ, u ⁻¹ᵁ O a = N.π.app i ⁻¹ᵁ U a := by
    intro a
    change u ⁻¹ᵁ (_ ⊓ _) = _
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, hufst, husnd, hpreA a]
    exact inf_eq_left.mpr (hle a)
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) O ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have htop : (⨆ a : τ, N.π.app i ⁻¹ᵁ U a) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hUcov.iSup_eq_top]
      simp
    have hx : x ∈ (⨆ a : τ, N.π.app i ⁻¹ᵁ U a) := by rw [htop]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    rw [← hupre a] at ha
    exact SetLike.mem_coe.mpr (Opens.mem_iSup.mpr ⟨a, ha⟩)
  · intro a
    have hOaff : IsAffineOpen (O a) :=
      isAffineOpen_preimage_inf_preimage_pullback tZ tS ((hU a).1.preimage (N.D.map gk)) (hV a.1)
    have : IsAffine (O a).toScheme := hOaff
    have hsurj : ∀ (e : (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ u ⁻¹ᵁ O a),
        Function.Surjective (u.appLE (O a) (N.π.app i ⁻¹ᵁ U a) e) := by
      intro e z
      have hmem := hgens a ((u.appLE (O a) (N.π.app i ⁻¹ᵁ U a) e).hom.range) ?_ ?_ z
      · exact RingHom.mem_range.mp hmem
      · intro r
        exact Scheme.Hom.range_appLE_subset_of_comp_eq u (pullback.snd tZ tS) f husnd
          inf_le_right e (hle a) ⟨r, rfl⟩
      · intro x hx
        exact Scheme.Hom.range_appLE_subset_of_comp_eq u (pullback.fst tZ tS) (N.π.app k) hufst
          inf_le_left e (le_of_eq (hpreA a).symm) (hk ⟨a, ⟨x, hx⟩⟩ _)
    have hcl : ∀ (e : (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ u ⁻¹ᵁ O a),
        IsClosedImmersion (u.resLE (O a) (N.π.app i ⁻¹ᵁ U a) e) := by
      intro e
      rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
      exact ⟨haff a, Scheme.Hom.surjective_resLE_appTop u e (hsurj e)⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr u _ rfl (hupre a) @IsImmersion]
    have := hcl (le_of_eq (hupre a).symm)
    infer_instance

/-- **Immersion into a scheme of finite presentation** (Stacks Project Tag 01ZE): a
quasi-compact quasi-separated scheme `X` that is locally of finite type over a quasi-compact
quasi-separated scheme `S` admits an immersion over `S` into a scheme of finite presentation
over `S`. (Blueprint: `lemma:nagata-immersion-into-fp-model`.) -/
@[stacks 01ZE]
theorem Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (i : X ⟶ Y), LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
      QuasiSeparated p ∧ IsImmersion i ∧ i ≫ p = f := by
  obtain ⟨N⟩ := X.nonempty_noetherianApproximation
  obtain ⟨k, hk⟩ := f.exists_isImmersion_lift_noetherianApproximation N
  -- the finite presentation model
  have : LocallyOfFinitePresentation (specULiftZIsTerminal.from (N.D.obj k)) := inferInstance
  have : QuasiCompact (specULiftZIsTerminal.from (N.D.obj k)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : QuasiSeparated (specULiftZIsTerminal.from (N.D.obj k)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr inferInstance
  exact ⟨pullback (specULiftZIsTerminal.from (N.D.obj k)) (specULiftZIsTerminal.from S),
    pullback.snd _ _, pullback.lift (N.π.app k) f (specULiftZIsTerminal.hom_ext _ _),
    MorphismProperty.pullback_snd _ _ ‹_›, MorphismProperty.pullback_snd _ _ ‹_›,
    MorphismProperty.pullback_snd _ _ ‹_›, hk, pullback.lift_snd _ _ _⟩

end FinitePresentationModel



section ClosedSubschemeLimit

/-!
## A closed subscheme as the limit of its closed neighbours of finite presentation

Let `I` be a quasi-coherent ideal sheaf on a quasi-compact quasi-separated scheme `Y`. Every
section of `I` over an affine open lies in a subideal sheaf of `I` of finite type
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_of_mem`). This is proved by
absolute Noetherian approximation of the ambient scheme rather than by the quasi-coherent
extension theorem of Stacks Project Tag 01PF: the section descends to an affine open of a
Noetherian stage `Yⱼ`, and there the scheme-theoretic image `I.map (π j)` of `V(I)` has
finitely generated ideals of sections, because a closed immersion into a Noetherian scheme is
locally of finite presentation. Its inverse image on `Y` is then a subideal sheaf of `I` of
finite type containing the given section.

Consequently `V(I)` is the cofiltered limit of the closed subschemes `V(J)`, for `J` running
over the subideal sheaves of `I` of finite type
(`AlgebraicGeometry.Scheme.IdealSheafData.isLimitFgSubCone`, Stacks Project Tag 09ZP). The
index category is the directed poset
`AlgebraicGeometry.Scheme.IdealSheafData.FGSub`, the diagram is
`AlgebraicGeometry.Scheme.IdealSheafData.fgSubDiagram`, its transition morphisms are the
subscheme inclusions, hence closed immersions, and each `V(J) ⟶ Y` is locally of finite
presentation.
-/

set_option backward.defeqAttrib.useBackward true

namespace Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}}

/-- (Implementation) A section over an affine open `V` of `Y` lies in the pushforward `I.map f`
as soon as its pullback to `f ⁻¹ᵁ V` lies in `I`. -/
private lemma mem_ideal_map_of_preimage_eq (I : X.IdealSheafData)
    (f : X ⟶ Y) [QuasiCompact f] (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : f ⁻¹ᵁ V.1 = U.1) (t : Γ(Y, V.1)) (h : U.1 ≤ f ⁻¹ᵁ V.1)
    (hmem : f.appLE V.1 U.1 h t ∈ I.ideal U) : t ∈ (I.map f).ideal V := by
  obtain ⟨U, hU⟩ := U
  dsimp only at hUV h hmem
  subst hUV
  rw [ideal_map I f V hU, Ideal.mem_comap, Scheme.Hom.app_eq_appLE]
  exact hmem

/-- (Implementation) The inverse image along `π : Y ⟶ Z` of the scheme-theoretic image of
`V(I)` in a locally Noetherian scheme `Z` is a subideal sheaf of `I` of finite type, and it
contains every section of `I` that comes from `Z`. -/
private lemma exists_finiteType_le_of_appLE_eq [IsLocallyNoetherian Z]
    (I : Y.IdealSheafData) (π : Y ⟶ Z) [QuasiCompact π] (V : Z.affineOpens) (U : Y.affineOpens)
    (hUV : π ⁻¹ᵁ V.1 = U.1) (h : U.1 ≤ π ⁻¹ᵁ V.1) (t : Γ(Z, V.1)) {s : Γ(Y, U.1)}
    (hts : π.appLE V.1 U.1 h t = s) (hs : s ∈ I.ideal U) :
    ∃ J : Y.IdealSheafData, J ≤ I ∧ (∀ W : Y.affineOpens, (J.ideal W).FG) ∧ s ∈ J.ideal U := by
  refine ⟨(I.map π).comap π, le_map_iff_comap_le.mp le_rfl, ?_, ?_⟩
  · have : LocallyOfFinitePresentation ((I.map π).comap π).subschemeι := by
      rw [← comapIso_hom_fst (I.map π) π]
      exact MorphismProperty.comp_mem _ _ _ inferInstance
        (MorphismProperty.pullback_fst _ _ inferInstance)
    intro W
    have hfg := Scheme.Hom.fg_ideal_ker ((I.map π).comap π).subschemeι W
    rwa [ker_subschemeι] at hfg
  · have htV : t ∈ (I.map π).ideal V :=
      mem_ideal_map_of_preimage_eq I π V U hUV t h (by rw [hts]; exact hs)
    have hmem := ideal_map_appLE_le_ideal_comap (I.map π) π V U h (Ideal.mem_map_of_mem _ htV)
    rwa [hts] at hmem

/-- **Every section of an ideal sheaf on a quasi-compact quasi-separated scheme lies in a
subideal sheaf of finite type.** (Blueprint: `lemma:nagata-closed-subscheme-fp-system`.) -/
theorem exists_finiteType_le_of_mem [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Y.IdealSheafData) (U : Y.affineOpens) {s : Γ(Y, U.1)} (hs : s ∈ I.ideal U) :
    ∃ J : Y.IdealSheafData, J ≤ I ∧ (∀ V : Y.affineOpens, (J.ideal V).FG) ∧ s ∈ J.ideal U := by
  obtain ⟨N⟩ := Y.nonempty_noetherianApproximation
  obtain ⟨U, hU⟩ := U
  dsimp only at s hs ⊢
  obtain ⟨k, V, hV, hkV⟩ : ∃ (k : N.I) (V : (N.D.obj k).Opens), IsAffineOpen V ∧
      N.π.app k ⁻¹ᵁ V = U := by
    obtain ⟨i, W, hWc, hWU⟩ := exists_preimage_eq N.D (Cone.mk Y N.π) N.isLimit U hU.isCompact
    obtain ⟨j, hVj⟩ := exists_isAffineOpen_preimage (D := N.D) (c := Cone.mk Y N.π) N.isLimit hWc
      (hWU ▸ hU)
    have hWU' : N.π.app i ⁻¹ᵁ W = U := hWU
    have hwj : N.π.app j.left ≫ N.D.map j.hom = N.π.app i := (Cone.mk Y N.π).w j.hom
    refine ⟨j.left, _, hVj, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hwj]
    exact hWU'
  subst hkV
  obtain ⟨m, g, t, ht⟩ :=
    exists_appLE_π_app_eq (D := N.D) (c := Cone.mk Y N.π) N.isLimit k hV s
  have ht' : ∀ e : N.π.app k ⁻¹ᵁ V ≤ N.π.app m ⁻¹ᵁ (N.D.map g ⁻¹ᵁ V),
      (N.π.app m).appLE (N.D.map g ⁻¹ᵁ V) (N.π.app k ⁻¹ᵁ V) e t = s := ht
  have hwm : N.π.app m ≫ N.D.map g = N.π.app k := (Cone.mk Y N.π).w g
  have hmk : N.π.app m ⁻¹ᵁ (N.D.map g ⁻¹ᵁ V) = N.π.app k ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hwm]
  have : IsAffineHom (N.π.app m) := isAffineHom_π_app N.D (Cone.mk Y N.π) N.isLimit m
  exact exists_finiteType_le_of_appLE_eq I (N.π.app m) ⟨N.D.map g ⁻¹ᵁ V, hV.preimage _⟩
    ⟨N.π.app k ⁻¹ᵁ V, hU⟩ hmk hmk.ge t (ht' hmk.ge) hs

/-- The subideal sheaves of finite type of an ideal sheaf `I`, ordered by inclusion.
(Blueprint: `def:nagata-closed-subscheme-fp-system`.) -/
protected abbrev FGSub (I : Y.IdealSheafData) : Type u :=
  {J : Y.IdealSheafData // J ≤ I ∧ ∀ U : Y.affineOpens, (J.ideal U).FG}

variable (I : Y.IdealSheafData)

instance : OrderBot I.FGSub where
  bot := ⟨⊥, bot_le, fun _ ↦ Submodule.fg_bot⟩
  bot_le _ := Subtype.coe_le_coe.mp bot_le

instance : Inhabited I.FGSub := ⟨⊥⟩

@[simp]
lemma FGSub.coe_bot : ((⊥ : I.FGSub) : Y.IdealSheafData) = ⊥ := rfl

/-- The subideal sheaves of finite type of `I` are directed: the sum of two of them is one. -/
instance : IsDirectedOrder I.FGSub :=
  ⟨fun J J' ↦ ⟨⟨J.1 ⊔ J'.1, sup_le J.2.1 J'.2.1, fun U ↦ Submodule.FG.sup (J.2.2 U) (J'.2.2 U)⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The cofiltered diagram of the closed subschemes cut out by the subideal sheaves of finite
type of `I`, with the subscheme inclusions as transition morphisms.
(Blueprint: `def:nagata-closed-subscheme-fp-system`.) -/
@[simps]
noncomputable def fgSubDiagram : (I.FGSub)ᵒᵖ ⥤ Scheme.{u} where
  obj J := J.unop.1.subscheme
  map f := inclusion (Subtype.coe_le_coe.mpr f.unop.le)
  map_id _ := inclusion_id _
  map_comp _ _ := (inclusion_comp _ _).symm

set_option backward.isDefEq.respectTransparency false in
instance isClosedImmersion_fgSubDiagram_map {J J' : (I.FGSub)ᵒᵖ} (f : J ⟶ J') :
    IsClosedImmersion (I.fgSubDiagram.map f) := by
  have h : I.fgSubDiagram.map f ≫ (J'.unop : Y.IdealSheafData).subschemeι =
      (J.unop : Y.IdealSheafData).subschemeι := inclusion_subschemeι _
  have : IsClosedImmersion
      (I.fgSubDiagram.map f ≫ (J'.unop : Y.IdealSheafData).subschemeι) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (J'.unop : Y.IdealSheafData).subschemeι

instance compactSpace_fgSubDiagram_obj [CompactSpace Y] (J : (I.FGSub)ᵒᵖ) :
    CompactSpace (I.fgSubDiagram.obj J) :=
  inferInstanceAs (CompactSpace (J.unop : Y.IdealSheafData).subscheme)

instance quasiSeparatedSpace_fgSubDiagram_obj [QuasiSeparatedSpace Y] (J : (I.FGSub)ᵒᵖ) :
    QuasiSeparatedSpace (I.fgSubDiagram.obj J) :=
  inferInstanceAs (QuasiSeparatedSpace (J.unop : Y.IdealSheafData).subscheme)

instance locallyOfFinitePresentation_fgSub_subschemeι (J : I.FGSub) :
    LocallyOfFinitePresentation (J.1).subschemeι :=
  locallyOfFinitePresentation_subschemeι J.2.2

/-- The cone with point the closed subscheme cut out by `I` over the diagram of the closed
subschemes cut out by the subideal sheaves of finite type of `I`. -/
@[simps]
noncomputable def fgSubCone : Cone I.fgSubDiagram where
  pt := I.subscheme
  π := { app J := inclusion J.unop.2.1 }

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) All the legs of a cone over `I.fgSubDiagram` induce the same morphism
to the ambient scheme. -/
lemma π_app_comp_subschemeι (s : Cone I.fgSubDiagram) (J : (I.FGSub)ᵒᵖ) :
    s.π.app J ≫ J.unop.1.subschemeι =
      s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι := by
  rw [← s.w (Quiver.Hom.op (homOfLE (bot_le : (⊥ : I.FGSub) ≤ J.unop)))]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The ideal sheaf `I` is contained in the kernel of the morphism to the
ambient scheme induced by any cone over `I.fgSubDiagram`. -/
lemma le_ker_π_app_bot_comp_subschemeι [CompactSpace Y] [QuasiSeparatedSpace Y]
    (s : Cone I.fgSubDiagram) :
    I.subschemeι.ker ≤
      (s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι).ker := by
  rw [ker_subschemeι]
  intro U x hx
  obtain ⟨J, hJI, hJfg, hxJ⟩ := I.exists_finiteType_le_of_mem U hx
  have hle : J ≤ (s.π.app (Opposite.op ⟨J, hJI, hJfg⟩) ≫ J.subschemeι).ker := by
    simpa using Scheme.Hom.le_ker_comp (s.π.app (Opposite.op ⟨J, hJI, hJfg⟩)) J.subschemeι
  rw [← π_app_comp_subschemeι I s (Opposite.op ⟨J, hJI, hJfg⟩)]
  exact hle U hxJ

set_option backward.isDefEq.respectTransparency false in
/-- **A closed subscheme of a quasi-compact quasi-separated scheme is the cofiltered limit of
the closed subschemes cut out by the subideal sheaves of finite type of its ideal sheaf.**
(Blueprint: `lemma:nagata-closed-subscheme-fp-system`.) -/
@[stacks 09ZP]
noncomputable def isLimitFgSubCone [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsLimit I.fgSubCone where
  lift s := IsClosedImmersion.lift I.subschemeι
    (s.π.app (Opposite.op ⊥) ≫ (⊥ : Y.IdealSheafData).subschemeι)
    (le_ker_π_app_bot_comp_subschemeι I s)
  fac s J := by
    rw [← cancel_mono J.unop.1.subschemeι, Category.assoc, fgSubCone_π_app,
      inclusion_subschemeι, IsClosedImmersion.lift_fac, π_app_comp_subschemeι I s J]
  uniq s m hm := by
    rw [← cancel_mono I.subschemeι, IsClosedImmersion.lift_fac,
      ← inclusion_subschemeι (⊥ : I.FGSub).2.1, ← fgSubCone_π_app, ← Category.assoc,
      hm (Opposite.op ⊥)]
    rfl

end Scheme.IdealSheafData

end ClosedSubschemeLimit

section FinitePresentationApproximation

/-!
## The finite presentation model system of a morphism of finite type

A morphism `f : X ⟶ S` locally of finite type between quasi-compact quasi-separated schemes
exhibits `X` as a cofiltered limit of schemes of finite presentation over `S` with closed
immersions as transition morphisms, see
`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation` (Stacks Project
Tag 09ZQ).
-/

set_option backward.defeqAttrib.useBackward true

open TopologicalSpace in
/-- **Closed immersion into a scheme of finite presentation**: a quasi-compact quasi-separated
scheme `X` that is locally of finite type over a quasi-compact quasi-separated scheme `S`
admits a closed immersion over `S` into a scheme of finite presentation over `S`.

This is Stacks Project Tag 01ZE followed by the shrinking step of Tag 01ZG.
(Blueprint: `lemma:nagata-finite-type-fp-model-system`.) -/
theorem Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (i : X ⟶ Y), LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
      QuasiSeparated p ∧ IsClosedImmersion i ∧ i ≫ p = f := by
  obtain ⟨Y, p, i, hp, hpc, hpqs, hi, hcomp⟩ :=
    f.exists_isImmersion_locallyOfFinitePresentation
  have := hp; have := hpc; have := hpqs; have := hi
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨W, g, hWc, hg, hgW⟩ := i.exists_isCompact_isClosedImmersion
  have := hg
  have : QuasiCompact W.ι := W.quasiCompact_ι hWc
  refine ⟨W.toScheme, W.ι ≫ p, g, inferInstance, inferInstance, inferInstance, hg, ?_⟩
  rw [← Category.assoc, hgW, hcomp]

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the closed subscheme cut out by an ideal sheaf `I` into the closed
subscheme cut out by a subideal sheaf of finite type of `I` is a closed immersion. -/
instance Scheme.IdealSheafData.isClosedImmersion_fgSubCone_π_app {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (J : (I.FGSub)ᵒᵖ) :
    IsClosedImmersion (I.fgSubCone.π.app J) := by
  have h : I.fgSubCone.π.app J ≫ (J.unop : Y.IdealSheafData).subschemeι = I.subschemeι :=
    inclusion_subschemeι _
  have : IsClosedImmersion (I.fgSubCone.π.app J ≫
      (J.unop : Y.IdealSheafData).subschemeι) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (J.unop : Y.IdealSheafData).subschemeι

/-- A **finite presentation approximation** of a morphism `f : X ⟶ S` is a cofiltered system
`D` of quasi-compact quasi-separated schemes of finite presentation over `S`, whose transition
morphisms are closed immersions, together with a limit cone with point `X` whose projections
are closed immersions compatible with `f`:

```
              X
    π.app i  ↙    ↓    ↘  π.app j
  D.obj i  ────────────⟶  D.obj j
                D.map g            ↘ p.app j
                                       S
```

Every morphism locally of finite type between quasi-compact quasi-separated schemes admits one
(`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation`, Stacks Project
Tag 09ZQ). (Blueprint: `def:nagata-finite-type-fp-model-system`.) -/
structure Scheme.Hom.FinitePresentationApproximation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of models. -/
  D : I ⥤ Scheme.{u}
  /-- The structure morphisms of the models to `S`. -/
  p : D ⟶ (Functor.const I).obj S
  /-- Every model is locally of finite presentation over `S`. -/
  locallyOfFinitePresentation_p (i : I) : LocallyOfFinitePresentation (p.app i)
  /-- Every model is quasi-compact over `S`. -/
  quasiCompact_p (i : I) : QuasiCompact (p.app i)
  /-- Every model is quasi-separated over `S`. -/
  quasiSeparated_p (i : I) : QuasiSeparated (p.app i)
  /-- Every model is quasi-compact. -/
  compactSpace_obj (i : I) : CompactSpace (D.obj i)
  /-- Every model is quasi-separated. -/
  quasiSeparatedSpace_obj (i : I) : QuasiSeparatedSpace (D.obj i)
  /-- The transition morphisms of the system are closed immersions. -/
  isClosedImmersion_map {i j : I} (g : i ⟶ j) : IsClosedImmersion (D.map g)
  /-- The morphisms from `X` to the models. -/
  π : (Functor.const I).obj X ⟶ D
  /-- The morphisms from `X` to the models are closed immersions. -/
  isClosedImmersion_π (i : I) : IsClosedImmersion (π.app i)
  /-- `X` is the limit of the models. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The morphisms from `X` to the models are compatible with `f`. -/
  w (i : I) : π.app i ≫ p.app i = f

namespace Scheme.Hom.FinitePresentationApproximation

attribute [instance] smallCategory isCofiltered locallyOfFinitePresentation_p quasiCompact_p
  quasiSeparated_p compactSpace_obj quasiSeparatedSpace_obj isClosedImmersion_map
  isClosedImmersion_π

end Scheme.Hom.FinitePresentationApproximation

set_option backward.isDefEq.respectTransparency false in
/-- The finite presentation approximation of `f : X ⟶ S` determined by a closed immersion
`i : X ⟶ Y` over `S` into an `S`-scheme `Y` that is quasi-compact, quasi-separated and locally of
finite presentation over `S`: the system of closed subschemes of `Y` cut out by the subideal
sheaves of finite type of the kernel of `i`. (Blueprint:
`theorem-nagata-s-compactification-theorem--1`, `theorem-nagata-s-compactification-theorem--1`.) -/
noncomputable def Scheme.Hom.FinitePresentationApproximation.ofIsClosedImmersion
    {X Y S : Scheme.{u}} {f : X ⟶ S} [CompactSpace S] [QuasiSeparatedSpace S] (q : Y ⟶ S)
    (i : X ⟶ Y) [IsClosedImmersion i] [LocallyOfFinitePresentation q] [QuasiCompact q]
    [QuasiSeparated q] (hcomp : i ≫ q = f) : f.FinitePresentationApproximation :=
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  { I := (i.ker.FGSub)ᵒᵖ
    D := i.ker.fgSubDiagram
    p :=
      { app J := (J.unop : Y.IdealSheafData).subschemeι ≫ q
        naturality := by
          intro J J' g
          simp }
    locallyOfFinitePresentation_p J := by
      change LocallyOfFinitePresentation ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    quasiCompact_p J := by
      change QuasiCompact ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    quasiSeparated_p J := by
      change QuasiSeparated ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    compactSpace_obj J := inferInstance
    quasiSeparatedSpace_obj J := inferInstance
    isClosedImmersion_map g := inferInstance
    π := (Functor.const _).map i.toImage ≫ i.ker.fgSubCone.π
    isClosedImmersion_π J := by
      change IsClosedImmersion (i.toImage ≫ i.ker.fgSubCone.π.app J)
      infer_instance
    isLimit := i.ker.isLimitFgSubCone.ofIsoLimit (Cone.ext (asIso i.toImage).symm fun J ↦ by simp)
    w J := by
      change (i.toImage ≫ i.ker.fgSubCone.π.app J) ≫
        (J.unop : Y.IdealSheafData).subschemeι ≫ q = f
      simpa using hcomp }

/-- **The finite presentation model system of a morphism of finite type** (Stacks Project
Tag 09ZQ): a quasi-compact quasi-separated scheme `X` that is locally of finite type over a
quasi-compact quasi-separated scheme `S` is the cofiltered limit of a system of schemes of
finite presentation over `S` whose transition morphisms and whose morphisms from `X` are all
closed immersions.

The system is that of the closed subschemes of a finite presentation model `Y` of `X` over `S`
cut out by the subideal sheaves of finite type of the kernel of the closed immersion `X ⟶ Y`.
(Blueprint: `lemma:nagata-finite-type-fp-model-system`,
`theorem-nagata-s-compactification-theorem--1`.)
-/
@[stacks 09ZQ]
theorem Scheme.Hom.nonempty_finitePresentationApproximation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty f.FinitePresentationApproximation := by
  obtain ⟨Y, q, i, hq, hqc, hqs, hi, hcomp⟩ :=
    f.exists_isClosedImmersion_locallyOfFinitePresentation
  have := hq; have := hqc; have := hqs; have := hi
  exact ⟨.ofIsClosedImmersion q i hcomp⟩

/-- The interface consumed by the descent of a separated morphism of finite presentation to a
finite stage (Stacks Project Tag 01ZQ): all the instance arguments of
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated` are provided
by the fields of a finite presentation approximation. -/
example {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FinitePresentationApproximation)
    {X' : Scheme.{u}} (g : X' ⟶ X) [LocallyOfFinitePresentation g] [QuasiCompact g]
    [IsSeparated g] :
    ∃ (i : F.I) (Y : Scheme.{u}) (p : Y ⟶ F.D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : IsSeparated p) (h : X' ⟶ Y),
      IsPullback h g p ((Cone.mk X F.π).π.app i) :=
  Scheme.exists_isPullback_of_finitePresentation_of_isSeparated F.isLimit g

/-- The interface consumed by the descent of separatedness over a fixed base to a finite stage
(Stacks Project Tag 01ZH): the structure morphisms of a finite presentation approximation form
the natural transformation `t` required by
`AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit`. -/
example {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FinitePresentationApproximation) (i₀ : F.I)
    [IsSeparated ((Cone.mk X F.π).π.app i₀ ≫ F.p.app i₀)] :
    ∃ j : F.I, ∀ {i : F.I} (_ : i ⟶ j), IsSeparated (F.p.app i) :=
  Scheme.exists_isSeparated_app_of_isLimit F.isLimit F.p i₀

/-- **The separated finite presentation envelope of a morphism of finite type** (Stacks Project
Tag 01ZJ): a separated morphism `f : X ⟶ S` locally of finite type between quasi-compact
quasi-separated schemes factors as a closed immersion `i : X ⟶ X'` followed by a separated,
quasi-compact morphism `f' : X' ⟶ S` locally of finite presentation.

Take a finite presentation approximation of `f` (Stacks Project Tag 09ZQ) and descend the
separatedness of `f` to a stage of the system (Stacks Project Tag 01ZH); that stage is the
required envelope. (Blueprint: `prop:nagata-finite-type-closed-in-fp`.) -/
@[stacks 01ZJ]
theorem Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S), IsClosedImmersion i ∧
      LocallyOfFinitePresentation f' ∧ QuasiCompact f' ∧ IsSeparated f' ∧ i ≫ f' = f := by
  obtain ⟨F⟩ := f.nonempty_finitePresentationApproximation
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := F.I)
  have : IsSeparated ((Cone.mk X F.π).π.app i₀ ≫ F.p.app i₀) := by
    change IsSeparated (F.π.app i₀ ≫ F.p.app i₀)
    rw [F.w i₀]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isSeparated_app_of_isLimit F.isLimit F.p i₀
  exact ⟨F.D.obj j, F.π.app j, F.p.app j, inferInstance, inferInstance, inferInstance,
    hj (𝟙 j), F.w j⟩

end FinitePresentationApproximation

section MinimalCounterexample

/-- A property `P` of quasi-compact quasi-separated schemes over a quasi-compact
quasi-separated base `T`, that is, a predicate on morphisms `T' ⟶ T` with `T'` qcqs, is
*qcqs-local* when it satisfies the three stability conditions of Stacks `0F06` and fails for
the empty scheme. -/
structure Scheme.IsQcqsLocalProperty (T : Scheme.{u})
    (P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop) : Prop where
  /-- `P` is invariant under thickenings: if `i : T₁ ⟶ T₂` is a closed immersion which is
  surjective on points and `f₂ : T₂ ⟶ T`, then `P (i ≫ f₂)` holds if and only if `P f₂`
  does. -/
  invariant_under_thickening : ∀ {T₁ T₂ : Scheme.{u}} [CompactSpace T₂]
    [QuasiSeparatedSpace T₂] (i : T₁ ⟶ T₂) [IsClosedImmersion i], Function.Surjective i.base →
    ∀ f₂ : T₂ ⟶ T, P (i ≫ f₂) ↔ P f₂
  /-- `P` is compatible with cofiltered limits with affine transition morphisms: if
  `D : I ⥤ Over T` is a cofiltered diagram of qcqs schemes over `T` whose transition
  morphisms are affine and `c` is a cone on `D` whose underlying cone of schemes is a limit
  cone, then `P` for every stage implies `P` for the limit. -/
  compatible_with_cofilteredLimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over T) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Limits.Cone D), Limits.IsLimit ((Over.forget T).mapCone c) →
    (∀ i, P (D.obj i).hom) → P c.pt.hom
  /-- `P` propagates to an open or to its closed complement: if `V` is a quasi-compact open
  of a qcqs scheme `T'` over `T` and `i : Z ⟶ T'` is a closed immersion onto the complement
  of `V`, then `P` for `T' ⟶ T` implies `P` for `V ⟶ T` or for `Z ⟶ T`. -/
  of_opens_or_closedComplement : ∀ {T' Z : Scheme.{u}} [CompactSpace T']
    [QuasiSeparatedSpace T'] (f : T' ⟶ T) (V : T'.Opens), IsCompact (V : Set T') →
    ∀ (i : Z ⟶ T') [IsClosedImmersion i], Set.range i.base = (V : Set T')ᶜ →
    P f → P (V.ι ≫ f) ∨ P (i ≫ f)
  /-- `P` fails for the empty scheme. -/
  not_of_isEmpty : ∀ {T' : Scheme.{u}} (f : T' ⟶ T), IsEmpty T' → ¬ P f

namespace Scheme.IsQcqsLocalProperty

variable {T : Scheme.{u}} {P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop}

/-- A qcqs-local property is invariant under isomorphisms of qcqs schemes over the base. -/
lemma comp_iff_of_isIso (hP : T.IsQcqsLocalProperty P) {T₁ T₂ : Scheme.{u}} [CompactSpace T₂]
    [QuasiSeparatedSpace T₂] (e : T₁ ⟶ T₂) [IsIso e] (f : T₂ ⟶ T) : P (e ≫ f) ↔ P f :=
  hP.invariant_under_thickening e (fun x ↦ ⟨(inv e).base x, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩) f

set_option backward.isDefEq.respectTransparency false in
/-- A qcqs-local property holding for the closed subschemes cut out by the members of a nonempty
chain of ideal sheaves holds for the closed subscheme cut out by their supremum, which is the
cofiltered limit of these closed subschemes. This gives the lower bounds of chains in the Zorn
argument of `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`. -/
lemma subschemeι_sSup [CompactSpace T] [QuasiSeparatedSpace T] (hP : T.IsQcqsLocalProperty P)
    {c : Set T.IdealSheafData} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (h : ∀ I ∈ c, P I.subschemeι) : P (sSup c).subschemeι := by
  obtain ⟨I₀, hI₀⟩ := hne
  have : Nonempty c := ⟨⟨I₀, hI₀⟩⟩
  have : IsDirectedOrder c := ⟨fun a b ↦ by
    rcases hc.total a.2 b.2 with hab | hab
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hab⟩⟩
  let F : cᵒᵖ ⥤ Scheme.{u} :=
    { obj I := I.unop.1.subscheme
      map f := IdealSheafData.inclusion (leOfHom f.unop)
      map_id _ := IdealSheafData.inclusion_id _
      map_comp _ _ := (IdealSheafData.inclusion_comp _ _).symm }
  let D : cᵒᵖ ⥤ Over T := F.toOver T (fun I ↦ I.unop.1.subschemeι)
    (fun _ ↦ IdealSheafData.inclusion_subschemeι _)
  let c' : Cone D :=
    { pt := Over.mk (sSup c).subschemeι
      π :=
      { app I := Over.homMk (IdealSheafData.inclusion (le_sSup I.unop.2))
          (IdealSheafData.inclusion_subschemeι _)
        naturality I J f := by
          ext1
          change IdealSheafData.inclusion _ =
            IdealSheafData.inclusion _ ≫ IdealSheafData.inclusion _
          exact (IdealSheafData.inclusion_comp _ _).symm } }
  have hπ (s : Cone (D ⋙ Over.forget T)) {I J : c} (hIJ : I ≤ J) :
      s.π.app (.op I) ≫ I.1.subschemeι = s.π.app (.op J) ≫ J.1.subschemeι := by
    rw [← s.w (homOfLE hIJ).op]
    exact (Category.assoc _ _ _).trans
      (congrArg (s.π.app (.op J) ≫ ·) (IdealSheafData.inclusion_subschemeι _))
  have hπ₀ (s : Cone (D ⋙ Over.forget T)) (I : c) :
      s.π.app (.op I) ≫ I.1.subschemeι = s.π.app (.op ⟨I₀, hI₀⟩) ≫ I₀.subschemeι := by
    rcases hc.total I.2 hI₀ with hle | hle
    · exact hπ s (I := I) (J := ⟨I₀, hI₀⟩) hle
    · exact (hπ s (I := ⟨I₀, hI₀⟩) (J := I) hle).symm
  have hker (s : Cone (D ⋙ Over.forget T)) :
      (sSup c).subschemeι.ker ≤ (s.π.app (.op ⟨I₀, hI₀⟩) ≫ I₀.subschemeι).ker := by
    rw [IdealSheafData.ker_subschemeι]
    refine sSup_le fun I hI ↦ ?_
    rw [← hπ₀ s ⟨I, hI⟩]
    have := Scheme.Hom.le_ker_comp (s.π.app (.op ⟨I, hI⟩)) I.subschemeι
    rwa [IdealSheafData.ker_subschemeι] at this
  have hlim : IsLimit ((Over.forget T).mapCone c') :=
    { lift s := (IsClosedImmersion.lift (sSup c).subschemeι _ (hker s) :
        s.pt ⟶ (sSup c).subscheme)
      fac s I := by
        change (IsClosedImmersion.lift (sSup c).subschemeι _ (hker s) :
          s.pt ⟶ (sSup c).subscheme) ≫ IdealSheafData.inclusion (le_sSup I.unop.2) = s.π.app I
        rw [← cancel_mono I.unop.1.subschemeι, Category.assoc,
          IdealSheafData.inclusion_subschemeι, IsClosedImmersion.lift_fac]
        exact (hπ₀ s I.unop).symm
      uniq s m hm := by
        rw [← cancel_mono (sSup c).subschemeι, IsClosedImmersion.lift_fac, ← hm (.op ⟨I₀, hI₀⟩)]
        change _ = (m ≫ IdealSheafData.inclusion _) ≫ _
        rw [Category.assoc, IdealSheafData.inclusion_subschemeι] }
  have (I : cᵒᵖ) : CompactSpace (D.obj I).left :=
    inferInstanceAs (CompactSpace I.unop.1.subscheme)
  have (I : cᵒᵖ) : QuasiSeparatedSpace (D.obj I).left :=
    inferInstanceAs (QuasiSeparatedSpace I.unop.1.subscheme)
  have {I J : cᵒᵖ} (f : I ⟶ J) : IsAffineHom (D.map f).left := by
    have hf : (D.map f).left = IdealSheafData.inclusion (leOfHom f.unop) := rfl
    have h : IdealSheafData.inclusion (leOfHom f.unop) ≫ J.unop.1.subschemeι =
        I.unop.1.subschemeι := IdealSheafData.inclusion_subschemeι _
    have : IsClosedImmersion
        (IdealSheafData.inclusion (leOfHom f.unop) ≫ J.unop.1.subschemeι) := by
      rw [h]; infer_instance
    have : IsClosedImmersion (IdealSheafData.inclusion (leOfHom f.unop)) :=
      IsClosedImmersion.of_comp_isClosedImmersion _ J.unop.1.subschemeι
    rw [hf]
    infer_instance
  exact hP.compatible_with_cofilteredLimit D c' hlim fun I ↦ h I.unop.1 I.unop.2

end Scheme.IsQcqsLocalProperty

open CommRingCat in
set_option backward.isDefEq.respectTransparency false in
/-- **Minimal counterexamples occur over a point.** A qcqs-local property `P` of
quasi-compact quasi-separated schemes over a quasi-compact quasi-separated base `T` which
holds for `T` itself holds for some morphism `Spec K ⟶ T` with `K` a field.

By Zorn's lemma there is a minimal closed subscheme `T'` of `T` with `P`. Every nonempty
quasi-compact open of `T'` has `P`, as otherwise its closed complement would be a smaller closed
subscheme with `P`. Take a nonempty affine open `Spec A` of `T'` and a minimal prime `p` of `A`;
then `Spec A_p` is the cofiltered limit of the nonempty basic opens `Spec A[1/f]`, `f ∉ p`, so
it has `P`, and it is a thickening of the spectrum of its residue field, as `A_p` has a single
prime ideal. (Blueprint: `lemma-reduction-field`.) -/
@[stacks 0F06]
theorem exists_spec_field_of_isQcqsLocalProperty (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop) (hP' : T.IsQcqsLocalProperty P)
    (hP : P (𝟙 T)) :
    ∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ T), P g := by
  classical
  -- Zorn's lemma gives a maximal ideal sheaf `J` (a minimal closed subscheme) with `P`
  obtain ⟨J, -, hJ⟩ := zorn_le_nonempty₀ {I : T.IdealSheafData | P I.subschemeι}
    (fun c hcs hc y hy ↦ ⟨sSup c, hP'.subschemeι_sSup hc ⟨y, hy⟩ fun I hI ↦ hcs hI,
      fun _ hz ↦ le_sSup hz⟩) ⊥ (by
      have hsurj : Function.Surjective (⊥ : T.IdealSheafData).subschemeι.base := by
        rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.support_bot]
        rfl
      have := (hP'.invariant_under_thickening _ hsurj (𝟙 T)).mpr hP
      rwa [Category.comp_id] at this)
  have hJP : P J.subschemeι := hJ.prop
  -- a closed subscheme of `V(J)` with `P` is all of `V(J)`
  have hsurj {Z : Scheme.{u}} (g : Z ⟶ J.subscheme) [IsClosedImmersion g]
      (hg : P (g ≫ J.subschemeι)) : Function.Surjective g.base := by
    have hker : P (g ≫ J.subschemeι).ker.subschemeι := by
      have := (hP'.comp_iff_of_isIso (g ≫ J.subschemeι).toImage (g ≫ J.subschemeι).imageι).mp
        (by rwa [Scheme.Hom.toImage_imageι])
      exact this
    have hJk : J ≤ (g ≫ J.subschemeι).ker := by
      have := Scheme.Hom.le_ker_comp g J.subschemeι
      rwa [Scheme.IdealSheafData.ker_subschemeι] at this
    have heq : (g ≫ J.subschemeι).ker = J := le_antisymm (hJ.2 hker hJk) hJk
    have hrange : Set.range (g ≫ J.subschemeι).base = Set.range J.subschemeι.base := by
      rw [← (g ≫ J.subschemeι).isClosedEmbedding.isClosed_range.closure_eq,
        ← Scheme.Hom.support_ker, heq, Scheme.IdealSheafData.range_subschemeι]
    intro z
    obtain ⟨w, hw⟩ : J.subschemeι.base z ∈ Set.range (g ≫ J.subschemeι).base :=
      hrange ▸ ⟨z, rfl⟩
    exact ⟨w, J.subschemeι.isClosedEmbedding.injective (by simpa using hw)⟩
  -- a nonempty quasi-compact open subscheme of `V(J)` has `P`
  have hopen {W : Scheme.{u}} (o : W ⟶ J.subscheme) [IsOpenImmersion o] [CompactSpace W]
      [Nonempty W] : P (o ≫ J.subschemeι) := by
    have hV : IsCompact (o.opensRange : Set J.subscheme) := by
      simpa using isCompact_range o.continuous
    let Z : TopologicalSpace.Closeds J.subscheme :=
      ⟨(o.opensRange : Set J.subscheme)ᶜ, o.opensRange.isOpen.isClosed_compl⟩
    have hZ : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base =
        (o.opensRange : Set J.subscheme)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rcases hP'.of_opens_or_closedComplement J.subschemeι o.opensRange hV _ hZ hJP with h | h
    · have : CompactSpace o.opensRange := isCompact_iff_compactSpace.mp hV
      have : QuasiSeparatedSpace o.opensRange :=
        quasiSeparatedSpace_of_quasiSeparated o.opensRange.ι
      rw [← o.isoOpensRange_hom_ι, Category.assoc, hP'.comp_iff_of_isIso]
      exact h
    · obtain ⟨w⟩ := ‹Nonempty W›
      obtain ⟨z, hz⟩ := hsurj _ h (o.base w)
      have : o.base w ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base :=
        ⟨z, hz⟩
      rw [hZ] at this
      exact (this ⟨w, rfl⟩).elim
  -- `V(J)` is nonempty, choose a nonempty affine open and a minimal prime of its sections
  obtain ⟨x⟩ : Nonempty J.subscheme := by
    by_contra hne
    exact hP'.not_of_isEmpty _ (not_nonempty_iff.mp hne) hJP
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    J.subscheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV : IsAffineOpen V := hV
  obtain ⟨y, -⟩ : x ∈ Set.range hV.fromSpec.base := by rwa [hV.range_fromSpec]
  have : Nontrivial Γ(J.subscheme, V) := ⟨⟨0, 1, fun h ↦ y.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ zero_mem _))⟩⟩
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal Γ(J.subscheme, V))) bot_ne_top
  have : p.IsPrime := hp.1.1
  -- `Spec A_p` is the limit of the nonempty basic opens `Spec A[1/f]`, `f ∉ p`, of `V`
  let q : Spec Γ(J.subscheme, V) ⟶ T := hV.fromSpec ≫ J.subschemeι
  have hstage (s : Finset p.primeCompl) :
      P (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s))) ≫ q) := by
    have : Nontrivial (AwayProd p s) := (awayProdToAtPrime p s).toRingHom.domain_nontrivial
    have : Nonempty (Spec (.of (AwayProd p s))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    have : IsOpenImmersion (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s)))) :=
      IsOpenImmersion.of_isLocalization (∏ x ∈ s, (x : Γ(J.subscheme, V)))
    have := hopen (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s))) ≫ hV.fromSpec)
    rwa [Category.assoc] at this
  let F : (Finset p.primeCompl)ᵒᵖ ⥤ Scheme.{u} := (awayProdDiagram p).op ⋙ Scheme.Spec
  let D : (Finset p.primeCompl)ᵒᵖ ⥤ Over T := F.toOver T
    (fun s ↦ Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s.unop))) ≫ q)
    (fun {s t} f ↦ by
      change Spec.map ((awayProdDiagram p).map f.unop) ≫ _ = _
      rw [← Spec.map_comp_assoc, ofHom_algebraMap_comp_awayProdDiagram_map])
  let c' : Cone D :=
    { pt := Over.mk (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (Localization.AtPrime p))) ≫ q)
      π :=
      { app s := Over.homMk (Spec.map ((awayProdCocone p).ι.app s.unop)) (by
          change _ ≫ Spec.map _ ≫ q = _
          rw [← Spec.map_comp_assoc, ofHom_algebraMap_comp_awayProdCocone_ι_app]
          rfl)
        naturality s t f := by
          ext1
          change Spec.map ((awayProdCocone p).ι.app t.unop) =
            Spec.map ((awayProdCocone p).ι.app s.unop) ≫ Spec.map ((awayProdDiagram p).map f.unop)
          rw [← Spec.map_comp, (awayProdCocone p).w] } }
  have hlim : IsLimit ((Over.forget T).mapCone c') :=
    isLimitOfPreserves Scheme.Spec (isColimitAwayProdCocone p).op
  have (s : (Finset p.primeCompl)ᵒᵖ) : IsAffine (D.obj s).left :=
    inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset p.primeCompl)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f).left :=
    isAffineHom_of_isAffine _
  have hlimP : P c'.pt.hom :=
    hP'.compatible_with_cofilteredLimit D c' hlim fun s ↦ hstage s.unop
  -- `Spec A_p` has a single point, so the residue field is a thickening of it
  have hunique (z : PrimeSpectrum (Localization.AtPrime p)) :
      z.asIdeal = IsLocalRing.maximalIdeal _ := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := Localization.AtPrime p) p ⊥ hp
    rw [Ideal.map_bot, IsLocalization.AtPrime.map_eq_maximalIdeal p] at hrad
    refine le_antisymm (IsLocalRing.le_maximalIdeal z.isPrime.ne_top) ?_
    rw [← hrad]
    exact z.isPrime.radical_le_iff.mpr bot_le
  have : Subsingleton (Spec (.of (Localization.AtPrime p))) :=
    ⟨fun a b ↦ PrimeSpectrum.ext ((hunique a).trans (hunique b).symm)⟩
  let K := IsLocalRing.ResidueField (Localization.AtPrime p)
  let i : Spec (.of K) ⟶ Spec (.of (Localization.AtPrime p)) :=
    Spec.map (ofHom (IsLocalRing.residue _))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : Nonempty (Spec (.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  exact ⟨K, inferInstance, i ≫ c'.pt.hom, (hP'.invariant_under_thickening i
    (fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩) _).mpr hlimP⟩

end MinimalCounterexample


section ClosedImmersionDescent

/-!
## Closed immersions spread out from a limit

We prove Stacks Project Tag 081B (1): a closed immersion into the limit of a cofiltered
system with affine transition morphisms, from a scheme locally of finite type over the base,
is already a closed immersion into the stages from some index on
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_comp_π`). Combined with the descent of
quasi-compact opens (Stacks Project Tag 01Z4), a quasi-compact open of the limit is closed in a
quasi-compact open of some stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit`).
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit, affine case.** Let `{Dᵢ}` be a cofiltered
system of affine schemes and `g : Y ⟶ lim Dᵢ` a closed immersion such that `Y` is locally of
finite type over an affine scheme `W` receiving a morphism from some `D_{i₀}`. Then
`Y ⟶ D_j` is a closed immersion for some `j ⟶ i₀`: finitely many generators of `Γ(Y)` over
`Γ(W)` lift to a common stage, whose ring of sections then surjects onto `Γ(Y)`. -/
lemma Scheme.exists_isClosedImmersion_comp_π_of_isAffine [IsCofiltered I]
    [∀ i, IsAffine (D.obj i)] (hc : IsLimit c) {Y W : Scheme.{u}} [IsAffine W]
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (q : D.obj i₀ ⟶ W)
    [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ q)] :
    ∃ (j : I) (_ : j ⟶ i₀), IsClosedImmersion (g ≫ c.π.app j) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine Y := isAffine_of_isAffineHom g
  have hft : (g ≫ c.π.app i₀ ≫ q).appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := (g ≫ c.π.app i₀ ≫ q).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  have hlift (y : Γ(Y, ⊤)) :
      ∃ (i : I) (t : Γ(D.obj i, ⊤)), (g ≫ c.π.app i).appTop t = y := by
    obtain ⟨x, rfl⟩ := g.app_surjective ⊤ (isAffineOpen_top _) y
    obtain ⟨i, t, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit D c hc x
    exact ⟨i, t, by simp⟩
  choose i t ht using hlift
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (insert i₀ (s.image i))
  have e₀ : j ⟶ i₀ := (hj (Finset.mem_insert_self _ _)).some
  have e (y : Γ(Y, ⊤)) (hy : y ∈ s) : j ⟶ i y :=
    (hj (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))).some
  refine ⟨j, e₀, IsClosedImmersion.of_surjective_of_isAffine _ fun y ↦ ?_⟩
  -- the image of `Γ(D_j)` is a `Γ(W)`-subalgebra containing the chosen generators
  let R : Subalgebra Γ(W, ⊤) Γ(Y, ⊤) :=
    { (g ≫ c.π.app j).appTop.hom.range with
      algebraMap_mem' := fun r ↦ ⟨(D.map e₀ ≫ q).appTop r, (by
        have h : (g ≫ c.π.app j) ≫ D.map e₀ ≫ q = g ≫ c.π.app i₀ ≫ q := by
          rw [Category.assoc, c.w_assoc]
        change _ = (g ≫ c.π.app i₀ ≫ q).appTop r
        rw [← h, Scheme.Hom.comp_appTop]
        rfl)⟩ }
  have hsR : Algebra.adjoin Γ(W, ⊤) (s : Set Γ(Y, ⊤)) ≤ R := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    refine ⟨(D.map (e y hy)).appTop (t y), ?_⟩
    have h : (g ≫ c.π.app j) ≫ D.map (e y hy) = g ≫ c.π.app (i y) := by
      rw [Category.assoc, c.w]
    calc _ = ((g ≫ c.π.app j) ≫ D.map (e y hy)).appTop (t y) := by
          rw [Scheme.Hom.comp_appTop]; rfl
      _ = y := by rw [h, ht y]
  rw [hs] at hsR
  exact hsR (Algebra.mem_top (x := y))


private lemma isClosedImmersion_morphismRestrict_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (e : a = b)
    {U U' : Y.Opens} (e' : U = U') :
    IsClosedImmersion (a ∣_ U) ↔ IsClosedImmersion (b ∣_ U') := by
  subst e e'; rfl

variable {D c}

/-- If `Y ⟶ lim Dᵢ ⟶ D_j` is a closed immersion, then so is `Y ⟶ lim Dᵢ ⟶ D_k` for every
`k ⟶ j`, the transition morphisms being affine, hence separated. -/
lemma Scheme.isClosedImmersion_comp_π_of_comp {Y : Scheme.{u}} (g : Y ⟶ c.pt)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : I} (h : k ⟶ j)
    [IsClosedImmersion (g ≫ c.π.app j)] : IsClosedImmersion (g ≫ c.π.app k) := by
  have : IsClosedImmersion ((g ≫ c.π.app k) ≫ D.map h) := by
    rwa [Category.assoc, c.w]
  exact .of_comp _ (D.map h)

/-- The local version of `AlgebraicGeometry.Scheme.isClosedImmersion_comp_π_of_comp`: being a
closed immersion over the preimage of an open `U ⊆ D_{i₀}` persists to later stages. -/
lemma Scheme.isClosedImmersion_morphismRestrict_comp_π_of_comp {Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i₀ j k : I} (f : j ⟶ i₀)
    (h : k ⟶ j) (f' : k ⟶ i₀) (hf : h ≫ f = f') (U : (D.obj i₀).Opens)
    [IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U))] :
    IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map f' ⁻¹ᵁ U)) := by
  subst hf
  have : IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map h ⁻¹ᵁ (D.map f ⁻¹ᵁ U)) ≫
      D.map h ∣_ (D.map f ⁻¹ᵁ U)) := by
    rw [← morphismRestrict_comp]
    exact (isClosedImmersion_morphismRestrict_congr (by rw [Category.assoc, c.w]) rfl).mpr
      inferInstance
  have : IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map h ⁻¹ᵁ (D.map f ⁻¹ᵁ U))) :=
    .of_comp _ (D.map h ∣_ (D.map f ⁻¹ᵁ U))
  exact (isClosedImmersion_morphismRestrict_congr rfl
    (by rw [D.map_comp, Scheme.Hom.comp_preimage])).mpr this


private lemma Scheme.Hom.isClosedImmersion_resLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    {V V' : X.Opens} (e : V = V') (h : V ≤ f ⁻¹ᵁ W) (h' : V' ≤ f ⁻¹ᵁ W) :
    IsClosedImmersion (f.resLE W V h) ↔ IsClosedImmersion (f.resLE W V' h') := by
  subst e; rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit, over an affine open.** If `U ⊆ D_{i₀}` is an
affine open mapping into an affine open `W` of `S`, then `Y ⟶ D_j` is a closed immersion over
the preimage of `U` for some `j ⟶ i₀`. This is the affine case applied to the system of the
preimages of `U`, whose limit is the preimage of `U` in `lim Dᵢ`. -/
lemma Scheme.exists_isClosedImmersion_morphismRestrict_comp_π [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) {S Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (t : D.obj i₀ ⟶ S)
    [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ t)] {U : (D.obj i₀).Opens}
    (hU : IsAffineOpen U) {W : S.Opens} (hW : IsAffineOpen W) (hUW : U ≤ t ⁻¹ᵁ W) :
    ∃ (j : I) (f : j ⟶ i₀), IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U)) := by
  have (j : Over i₀) : IsAffine ((opensDiagram D i₀ U).obj j) := hU.preimage _
  have : IsAffine W := hW
  let V := c.π.app i₀ ⁻¹ᵁ U
  let q : (opensDiagram D i₀ U).obj (Over.mk (𝟙 i₀)) ⟶ W :=
    t.resLE W (D.map (𝟙 i₀) ⁻¹ᵁ U) (by simpa using hUW)
  have : LocallyOfFiniteType (g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) := by
    have e : (g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) ≫ W.ι =
        (g ⁻¹ᵁ V).ι ≫ g ≫ c.π.app i₀ ≫ t := by
      simp [q, V]
    have : LocallyOfFiniteType
        ((g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) ≫ W.ι) := by
      rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp _ W.ι
  obtain ⟨j, -, hj⟩ := Scheme.exists_isClosedImmersion_comp_π_of_isAffine _ _
    (isLimitOpensCone D c hc i₀ U) (g ∣_ V) q
  refine ⟨j.left, j.hom, ?_⟩
  rw [← Scheme.Hom.resLE_eq_morphismRestrict] at hj ⊢
  rw [opensCone_π_app, Scheme.Hom.resLE_comp_resLE] at hj
  refine (Scheme.Hom.isClosedImmersion_resLE_congr _ _ ?_ _ _).mp hj
  rw [Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage (c.π.app j.left), c.w]


set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit** (Stacks Project Tag 081B, part (1);
blueprint `pqf-lem-limit-immersion-descends`). Let `{Dᵢ}` be a cofiltered system of schemes
with affine transition morphisms and `D_{i₀}` quasi-compact, let `q : D_{i₀} ⟶ S` and let
`g : Y ⟶ lim Dᵢ` be a closed immersion with `Y` locally of finite type over `S`. Then
`Y ⟶ D_k` is a closed immersion for every `k` beyond some `j ⟶ i₀`.

Cover `D_{i₀}` by finitely many affine opens mapping into affine opens of `S`, apply the
affine case over each of them and pass to a common later stage. -/
@[stacks 081B "(1)"]
theorem Scheme.exists_isClosedImmersion_comp_π [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) {S Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (t : D.obj i₀ ⟶ S)
    [CompactSpace (D.obj i₀)] [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ t)] :
    ∃ (j : I) (_ : j ⟶ i₀), ∀ {k : I} (_ : k ⟶ j), IsClosedImmersion (g ≫ c.π.app k) := by
  classical
  have H (x : D.obj i₀) : ∃ (U : (D.obj i₀).Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (j : I) (f : j ⟶ i₀), IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U)) := by
    obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t x)) isOpen_univ
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, hUW⟩ :=
      (D.obj i₀).isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxW
        (t ⁻¹ᵁ W).isOpen
    obtain ⟨j, f, hj⟩ := Scheme.exists_isClosedImmersion_morphismRestrict_comp_π hc g t hU hW hUW
    exact ⟨U, hU, hxU, j, f, hj⟩
  choose U hU hxU j f hj using H
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (U ·) (fun x ↦ (U x).2.mem_nhds (hxU x))
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i₀ (s.image j)) (by
    exact s.attach.image fun x ↦ ⟨j x.1, i₀, Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ x.2), by simp, f x.1⟩)
  refine ⟨k, fk (by simp), fun {k'} e ↦ ?_⟩
  suffices IsClosedImmersion (g ≫ c.π.app k) from
    Scheme.isClosedImmersion_comp_π_of_comp g e
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun x : s ↦ D.map (fk (Finset.mem_insert_self _ _)) ⁻¹ᵁ U x)]
  · intro x
    have h₁ : fk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2)) ≫ f x =
        fk (Finset.mem_insert_self _ _) :=
      hk _ (by simp) (Finset.mem_image.mpr ⟨⟨x, x.2⟩, by simp, by simp⟩)
    have := hj x
    exact Scheme.isClosedImmersion_morphismRestrict_comp_π_of_comp g (f x) _ _ h₁ (U x)
  · refine top_le_iff.mp fun y _ ↦ ?_
    obtain ⟨l, hl, hlU⟩ := Set.mem_iUnion₂.mp
      (hs.ge (Set.mem_univ ((D.map (fk (Finset.mem_insert_self _ _))) y)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨l, hl⟩, hlU⟩


set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-compact open of a limit is closed in an open of some stage.** Let `{Dᵢ}` be a
cofiltered system of quasi-compact schemes with affine transition morphisms and morphisms
`q i : Dᵢ ⟶ S`, and let `ι : X ⟶ lim Dᵢ` be an open immersion from a quasi-compact `X` that is
locally of finite type over `S`. Then there are a stage `i`, a quasi-compact open `U ⊆ Dᵢ` and
a closed immersion `X ⟶ U` lifting `X ⟶ lim Dᵢ ⟶ Dᵢ`.

The image of `X` descends to a quasi-compact open `V₁` of some stage (Stacks Project
Tag 01Z4); `X` is then the limit of the preimages of `V₁`, and the closed immersion spreads
out by Tag 081B. These are Steps 1 and 2 of the proof of blueprint
`thm-pqf-immersion-descent`. -/
theorem Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] (hc : IsLimit c)
    {X S : Scheme.{u}} (q : ∀ i, D.obj i ⟶ S) (ι : X ⟶ c.pt) [IsOpenImmersion ι]
    [CompactSpace X] [∀ i, LocallyOfFiniteType (ι ≫ c.π.app i ≫ q i)] :
    ∃ (i : I) (U : (D.obj i).Opens) (g : X ⟶ U), IsCompact (U : Set (D.obj i)) ∧
      IsClosedImmersion g ∧ g ≫ U.ι = ι ≫ c.π.app i := by
  obtain ⟨i₁, V₁, hV₁, hV⟩ := exists_preimage_eq D c hc ι.opensRange
    (isCompact_range ι.continuous)
  let g₀ : X ⟶ (opensCone D c i₁ V₁).pt := ι.isoOpensRange.hom ≫ (c.pt.isoOfEq hV.symm).hom
  have hg₀ : g₀ ≫ (c.π.app i₁ ⁻¹ᵁ V₁).ι = ι := by simp [g₀]
  have : CompactSpace ((opensDiagram D i₁ V₁).obj (Over.mk (𝟙 i₁))) :=
    isCompact_iff_compactSpace.mp (by simpa using hV₁)
  let q' : (opensDiagram D i₁ V₁).obj (Over.mk (𝟙 i₁)) ⟶ S :=
    (D.map (𝟙 i₁) ⁻¹ᵁ V₁).ι ≫ q i₁
  have h₁ : (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ (D.map (𝟙 i₁) ⁻¹ᵁ V₁).ι =
      (c.π.app i₁ ⁻¹ᵁ V₁).ι ≫ c.π.app i₁ :=
    opensCone_π_ι D c i₁ V₁ (Over.mk (𝟙 i₁))
  have : LocallyOfFiniteType (g₀ ≫ (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ q') := by
    have e : g₀ ≫ (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ q' = ι ≫ c.π.app i₁ ≫ q i₁ := by
      simp only [q']
      rw [reassoc_of% h₁, reassoc_of% hg₀]
    rw [e]; infer_instance
  obtain ⟨j, -, hj⟩ := Scheme.exists_isClosedImmersion_comp_π (isLimitOpensCone D c hc i₁ V₁)
    g₀ q'
  have := hj (𝟙 j)
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ V₁, g₀ ≫ (opensCone D c i₁ V₁).π.app j,
    (D.map j.hom).isCompact_preimage hV₁, this, ?_⟩
  have h₂ : (opensCone D c i₁ V₁).π.app j ≫ (D.map j.hom ⁻¹ᵁ V₁).ι =
      (c.π.app i₁ ⁻¹ᵁ V₁).ι ≫ c.π.app j.left :=
    opensCone_π_ι D c i₁ V₁ j
  rw [Category.assoc, h₂, reassoc_of% hg₀]

/-- **Quasi-compact opens of a cofiltered limit descend** (Stacks Project Tag 01Z4, parts (1)
and (3); blueprint `pqf-lem-limit-qc-open-descends`, items 1 and 3). Let `{Dᵢ}` be a cofiltered
system of quasi-compact schemes with affine transition morphisms and limit `S = lim Dᵢ`, and let
`V ⊆ S` be a quasi-compact open. Then `V = fᵢ⁻¹(Vᵢ)` for a quasi-compact open `Vᵢ` of some
stage; the preimages `Vⱼ` of `Vᵢ` at later stages are quasi-compact, their transition morphisms
are affine, and the projections exhibit `V = fᵢ⁻¹(Vᵢ)` as the limit `lim_{j ≥ i} Vⱼ`. -/
theorem Scheme.exists_preimage_eq_and_isLimit_opensCone [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) (V : c.pt.Opens)
    (hV : IsCompact (V : Set c.pt)) :
    ∃ (i : I) (Vᵢ : (D.obj i).Opens), IsCompact (Vᵢ : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ Vᵢ = V ∧
      (∀ j : Over i, IsCompact ((D.map j.hom ⁻¹ᵁ Vᵢ : (D.obj j.left).Opens) : Set (D.obj j.left))) ∧
      (∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((opensDiagram D i Vᵢ).map f)) ∧
      Nonempty (IsLimit (opensCone D c i Vᵢ)) := by
  obtain ⟨i, Vᵢ, hVᵢ, hVᵢV⟩ := exists_preimage_eq D c hc V hV
  exact ⟨i, Vᵢ, hVᵢ, hVᵢV, fun j ↦ QuasiCompact.isCompact_preimage _ Vᵢ.2 hVᵢ,
    fun f ↦ inferInstance, ⟨isLimitOpensCone D c hc i Vᵢ⟩⟩

/-- **Two descents of a quasi-compact open eventually agree** (Stacks Project Tag 01Z4, part
(2); blueprint `pqf-lem-limit-qc-open-descends`, item 2). If quasi-compact opens `Vᵢ ⊆ Dᵢ` and
`Vᵢ' ⊆ Dᵢ'` have the same preimage in the limit, then their preimages agree at some stage
`i'' ≥ i, i'`. -/
theorem Scheme.exists_map_preimage_eq_map_preimage_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) {i i' : I}
    {V : (D.obj i).Opens} {V' : (D.obj i').Opens} (hV : IsCompact (V : Set (D.obj i)))
    (hV' : IsCompact (V' : Set (D.obj i'))) (H : c.π.app i ⁻¹ᵁ V = c.π.app i' ⁻¹ᵁ V') :
    ∃ (i'' : I) (f : i'' ⟶ i) (f' : i'' ⟶ i'), D.map f ⁻¹ᵁ V = D.map f' ⁻¹ᵁ V' := by
  obtain ⟨k, g, g'⟩ : ∃ (k : I) (_ : k ⟶ i), Nonempty (k ⟶ i') :=
    ⟨IsCofiltered.min i i', IsCofiltered.minToLeft i i', ⟨IsCofiltered.minToRight i i'⟩⟩
  obtain ⟨g'⟩ := g'
  obtain ⟨l, h, hl⟩ := exists_map_preimage_eq_map_preimage D c hc (i := k)
    (U := D.map g ⁻¹ᵁ V) (V := D.map g' ⁻¹ᵁ V') (QuasiCompact.isCompact_preimage _ V.2 hV)
    (QuasiCompact.isCompact_preimage _ V'.2 hV')
    (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, c.w, c.w, H])
  refine ⟨l, h ≫ g, h ≫ g', ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hl]


end ClosedImmersionDescent

end AlgebraicGeometry

/-! ### Ported from the `proetale` package
(`Proetale.Mathlib.AlgebraicGeometry.AffineTransitionLimit`) -/

universe t
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory

lemma IsConnected.of_forall_nonempty_hom_left {C : Type*} [Category* C]
    (X : C) (h : ∀ (Y : C), Nonempty (X ⟶ Y)) :
    IsConnected C :=
  have : Nonempty C := ⟨X⟩
  zigzag_isConnected fun _ _ ↦ .trans (.of_inv (h _).some) (.of_hom (h _).some)

lemma IsConnected.of_forall_nonempty_hom_right {C : Type*} [Category* C]
    (X : C) (h : ∀ (Y : C), Nonempty (Y ⟶ X)) :
    IsConnected C :=
  have : Nonempty C := ⟨X⟩
  zigzag_isConnected fun _ _ ↦ .trans (.of_hom (h _).some) (.of_inv (h _).some)


variable {C : Type u₁} [Category.{v₁} C]
  {I : Type u₂} {I' : Type u₃} [Category.{v₂} I]
  [Category.{v₃} I']
  {D : I ⥤ C} {D' : I' ⥤ C}
  {c : Cone D} {c' : Cone D'}
  (hc : IsLimit c) (hc' : IsLimit c')
  (f : c.pt ⟶ c'.pt)

end CategoryTheory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

-- `Scheme.preservesColimit_yoneda` has been upstreamed to
-- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.

variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)

variable [IsCofiltered I]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ (i : I), CompactSpace (D.obj i)] [∀ (i : I), QuasiSeparatedSpace (D.obj i)]

open TopologicalSpace

-- `Scheme.exists_isOpenCover_and_isAffine_of_finite` and
-- `Scheme.OpenCover.exists_of_isCofiltered_of_finite` have been upstreamed to
-- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.

section

variable (D' : I ⥤ Scheme.{u}) (t' : D' ⟶ (Functor.const I).obj S) (c' : Cone D')
  (hc' : IsLimit c')

variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D'.map f)]
  [∀ (i : I), CompactSpace (D'.obj i)] [∀ (i : I), QuasiSeparatedSpace (D'.obj i)]

omit [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ (i : I), CompactSpace ↥(D.obj i)]
  [∀ (i : I), QuasiSeparatedSpace ↥(D.obj i)] [∀ (i : I), QuasiSeparatedSpace ↥(D'.obj i)] in
include hc' in
/-- If `lim fᵢ` is surjective and `fᵢ` has open image (e.g. if `fᵢ` is étale), then the image of
a deep enough transition map `D'ₖ ⟶ D'ᵢ` is contained in the image of `fᵢ`. In particular, the
base change of `fᵢ` along `D'ₖ ⟶ D'ᵢ` is surjective. Compare [EGA4.3, Thm. 8.10.5 (vi)].

Note that the naive statement "`fₖ` is surjective for all `k ⟶ i` for `i` deep enough" is false
for a general natural transformation `f`: EGA 8.10.5 considers systems induced from a single
morphism by base change. (Counterexample: `I = ℕᵒᵖ`, `D k = 𝔸¹ ∖ {0, …, k}`,
`D' k = 𝔸¹ ∖ {0, …, k - 1}` with `f.app k` the open immersion; no `f.app k` is surjective,
but the limit map is an isomorphism.) -/
lemma exists_range_map_subset_range_app_of_surjective_isLimitMap (f : D ⟶ D') (i : I)
    (hopen : IsOpen (Set.range (f.app i).base))
    (hf : Surjective (IsLimit.map c hc' f)) :
    ∃ (k : I) (fki : k ⟶ i), Set.range (D'.map fki).base ⊆ Set.range (f.app i).base := by
  let U : (D'.obj i).Opens := ⟨Set.range (f.app i).base, hopen⟩
  obtain ⟨k, fki, hk⟩ := exists_map_eq_top D' c' hc' (i := i) U <| by
    rw [TopologicalSpace.Opens.ext_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hf.surj y
    refine ⟨c.π.app i x, ?_⟩
    calc f.app i (c.π.app i x)
        = (c.π.app i ≫ f.app i) x := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (IsLimit.map c hc' f ≫ c'.π.app i) x :=
        (congrArg (fun g : c.pt ⟶ D'.obj i ↦ g x) (IsLimit.map_π c hc' f i)).symm
      _ = c'.π.app i (IsLimit.map c hc' f x) := Scheme.Hom.comp_apply _ _ _
  refine ⟨k, fki, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : z ∈ (D'.map fki ⁻¹ᵁ U : Set (D'.obj k)) := by
    rw [hk]
    trivial
  exact this

end

variable {I' : Type u} [SmallCategory I'] (D' : I' ⥤ Scheme.{u})
  (t' : D' ⟶ (Functor.const I').obj S)
  (c' : Cone D') (hc' : IsLimit c')

variable [IsCofiltered I']

instance {C : Type*} [Category* C] (X : C) : Nonempty (Over X) :=
  ⟨Over.mk (𝟙 X)⟩

instance {C : Type*} [Category* C] (X : C) : Nonempty (Under X) :=
  ⟨Under.mk (𝟙 X)⟩

include hc hc' in
lemma exists_eq_isLimitMap_whisker (f : c.pt ⟶ c'.pt)
    (hf : ∀ (i : I) (i' : I'), c.π.app i ≫ t.app i = f ≫ c'.π.app i' ≫ t'.app i')
    [∀ i, LocallyOfFinitePresentation (t.app i)] [∀ i, LocallyOfFinitePresentation (t'.app i)] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g ∧
      (∀ j, g.app j ≫ t'.app _ = t.app _) := by
  obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
  obtain ⟨i, g, hi, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation _ t
    (t'.app i') _ hc (f ≫ c'.π.app i') (by ext; simp [hf _ i'])
  let p' : c'.pt ⟶ S :=
    c'.π.app i' ≫ t'.app i'
  have hp' (j' : Over i') : c'.π.app j'.left ≫ t'.app j'.left = p' := by
    simp only [p']
    rw [← c'.w j'.hom, Category.assoc, (Cocone.mk S t').w j'.hom]
  let p : c.pt ⟶ S :=
    f ≫ p'
  have hp (j : Over i) : c.π.app j.left ≫ t.app j.left = p := by
    simp only [p, p', hf _ i']
  have hc₀ : IsLimit (Cone.whisker (Over.forget i) c) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  have hc'₀ : IsLimit (Cone.whisker (Over.forget i') c') :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc'
  have : IsCofiltered (Over i) := inferInstance
  have (j' : Over i') :
      PreservesColimit (Over.lift (Over.forget i ⋙ D) ((Over.forget i).whiskerLeft t)).op
        (yoneda.obj ((Over.lift (Over.forget i' ⋙ D')
        ((Over.forget i').whiskerLeft t')).obj j')) := by
    apply +allowSynthFailures @Scheme.preservesColimit_yoneda
    · exact fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
    · exact fun a ↦ inferInstanceAs (CompactSpace (D.obj a.left))
    · exact fun a ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj a.left))
    · exact inferInstanceAs (LocallyOfFinitePresentation (t'.app j'.left))
  obtain ⟨J, _, _, G, G', _, _, g, hg⟩ := Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda
    (D := Over.lift (Over.forget i ⋙ D) (Functor.whiskerLeft _ t))
    (D' := Over.lift (Over.forget i' ⋙ D') (Functor.whiskerLeft _ t'))
    (c := Over.liftCone _ _ (c.whisker _) p hp)
    (c' := Over.liftCone _ _ (c'.whisker _) p' hp')
    (hc := Over.isLimitLiftCone _ _ _ _ _ hc₀)
    (hc' := Over.isLimitLiftCone _ _ _ _ _ hc'₀)
    (Over.homMk f rfl)
  use J, inferInstance, inferInstance, G ⋙ Over.forget _, G' ⋙ Over.forget _, inferInstance,
    inferInstance
  refine ⟨Functor.whiskerRight g (Over.forget S), ?_, ?_⟩
  · apply ((Functor.Initial.isLimitWhiskerEquiv (G' ⋙ Over.forget i') c').symm hc').hom_ext
    intro j
    rw [IsLimit.map_π]
    have := hg =≫ (Cone.whisker G'
      (Over.liftCone _ ((Over.forget i').whiskerLeft t') (Cone.whisker _ _) _ hp')).π.app j
    rw [IsLimit.map_π] at this
    exact congr($(this).left)
  · intro j
    exact Over.w (g.app j)

end AlgebraicGeometry
