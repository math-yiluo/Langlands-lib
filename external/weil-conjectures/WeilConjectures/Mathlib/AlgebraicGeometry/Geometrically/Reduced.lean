/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Morphisms with geometrically reduced fibres

Facts about morphisms whose geometric fibres are reduced.

A smooth morphism has geometrically reduced fibres: its geometric fibres are smooth varieties,
hence regular, hence reduced. Together with the instances `Smooth → Flat` and
`Smooth → LocallyOfFinitePresentation` of `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`,
this is what makes a smooth morphism satisfy the hypotheses of degree-zero flat base change.

Precomposing with an étale morphism preserves geometrically reduced fibres, an étale scheme
over a reduced scheme being reduced. It makes these hypotheses stable under passing to the
objects of the small étale site of the source.

The étale-local slicing of a flat morphism, locally of finite presentation, with geometrically
reduced fibres (Stacks `0EY5`) is `AlgebraicGeometry.exists_etaleCover_factorization` in
`WeilConjectures/AlgebraicGeometry/Morphisms/SlicingFlat.lean`.

## Main statements

- `AlgebraicGeometry.isReduced_of_smooth`: a scheme smooth over a field is reduced.
- `AlgebraicGeometry.Smooth.geometricallyReduced`: a smooth morphism has geometrically
  reduced fibres.
- `AlgebraicGeometry.GeometricallyReduced.comp_of_etale`: an étale morphism followed by a
  morphism with geometrically reduced fibres has geometrically reduced fibres.
- `AlgebraicGeometry.GeometricallyReduced.of_perfectField`: over a perfect field, every reduced
  scheme is geometrically reduced.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme `X` smooth over a field `K` is reduced: on an affine open cover, the rings of
sections are smooth `K`-algebras, which are reduced by `Algebra.Smooth.isReduced_of_field`. -/
theorem isReduced_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] : IsReduced X := by
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) := by
    have : Smooth (X.affineCover.f i ≫ f) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineCover.f i ≫ f)
    have : Smooth (Spec.map φ) := by rwa [hφ]
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at this
    algebraize [φ.hom]
    exact (affine_isReduced_iff _).mpr (Algebra.Smooth.isReduced_of_field K _)
  exact IsReduced.of_openCover X X.affineCover

/-- **Smooth morphisms have geometrically reduced fibres** (blueprint
`sbc-lem-smooth-geometrically-reduced`). For a field `K` and `Spec K ⟶ S`, the base change
`X ×_S Spec K` is smooth over `Spec K` (Stacks `01VB`), hence reduced (Stacks `056T`, here
`AlgebraicGeometry.isReduced_of_smooth`). -/
instance Smooth.geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  exact isReduced_of_smooth (Limits.pullback.snd f y)

/-- An étale morphism followed by a morphism with geometrically reduced fibres has
geometrically reduced fibres: for a field `K` and `Spec K ⟶ Z`, the scheme `X ×_Z Spec K` is
étale over the reduced scheme `Y ×_Z Spec K`, being its base change along `f`, and a scheme
étale over a reduced scheme is reduced (`AlgebraicGeometry.isReduced_of_etale`). -/
theorem GeometricallyReduced.comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale f] [GeometricallyReduced g] : GeometricallyReduced (f ≫ g) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : IsReduced (Limits.pullback g y) :=
    pullback_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := g)) K y
  let l : Limits.pullback (f ≫ g) y ⟶ Limits.pullback g y :=
    Limits.pullback.lift (Limits.pullback.fst _ _ ≫ f) (Limits.pullback.snd _ _)
      (by simp [Limits.pullback.condition])
  have hl : IsPullback (Limits.pullback.fst (f ≫ g) y) l f (Limits.pullback.fst g y) :=
    IsPullback.of_bot (by simpa [l] using IsPullback.of_hasPullback (f ≫ g) y)
      (by simp [l]) (IsPullback.of_hasPullback g y)
  have : Etale l := MorphismProperty.of_isPullback hl inferInstance
  exact isReduced_of_etale l

/-- Over a perfect field `k`, the fibre product of the spectra of two reduced `k`-algebras is
reduced: it is the spectrum of their tensor product, which is reduced by
`isReduced_tensorProduct_of_perfectField`. -/
theorem isReduced_pullback_spec_map_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {R S : CommRingCat.{u}} (φ : .of k ⟶ R) (ψ : .of k ⟶ S) [IsReduced (Spec R)]
    [IsReduced (Spec S)] : IsReduced (Limits.pullback (Spec.map φ) (Spec.map ψ)) := by
  algebraize [φ.hom, ψ.hom]
  have : _root_.IsReduced R := (affine_isReduced_iff R).1 ‹_›
  have : _root_.IsReduced S := (affine_isReduced_iff S).1 ‹_›
  have := isReduced_tensorProduct_of_perfectField k R S
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k R S).hom

/-- **Over a perfect field every reduced scheme is geometrically reduced.** For a field
extension `L / k`, the base change `X ×_k L` is covered by the spectra of the tensor products
`A ⊗[k] L` for affine opens `Spec A` of `X`, which are reduced as `k` is perfect
(`isReduced_tensorProduct_of_perfectField`). -/
theorem GeometricallyReduced.of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X] : GeometricallyReduced f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 fun L _ _ ↦ ?_⟩
  refine @IsReduced.of_openCover _ (X.affineCover.pullback₁ (Limits.pullback.fst f _))
    fun i ↦ ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineCover.f i ≫ f)
  have := @isReduced_pullback_spec_map_of_perfectField _ _ _ _ _ φ
    (CommRingCat.ofHom (algebraMap k L)) (isReduced_of_isOpenImmersion (X.affineCover.f i)) _
  exact isReduced_of_isOpenImmersion (Limits.pullbackSymmetry _ _ ≪≫
    Limits.pullbackRightPullbackFstIso f _ (X.affineCover.f i) ≪≫
    Limits.pullback.congrHom hφ.symm rfl).hom

end AlgebraicGeometry
