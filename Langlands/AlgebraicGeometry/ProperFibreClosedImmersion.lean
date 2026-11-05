import Langlands.AlgebraicGeometry.ProperFibreFiniteSpreading
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.LocalRing.Module

/-! # Closed immersion of proper maps detected on residue fibres -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

section Algebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- The scalar map of the actual algebra fibre at a prime. -/
def fibreScalarMap (p : PrimeSpectrum R) :
    p.asIdeal.ResidueField →+* p.asIdeal.Fiber B :=
  algebraMap _ _

/-- A finite algebra is a quotient of its base if the scalar maps of all its
actual residue-field fibres are surjective. -/
lemma algebraMap_surjective_of_fibreScalarMap_surjective [Module.Finite R B]
    (H : ∀ p : PrimeSpectrum R, Function.Surjective (fibreScalarMap (B := B) p)) :
    Function.Surjective (algebraMap R B) := by
  let N := B ⧸ LinearMap.range (Algebra.linearMap R B)
  let π : B →ₗ[R] N := (LinearMap.range (Algebra.linearMap R B)).mkQ
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hπ1 : π 1 = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨1, by simp⟩
  have hzero (p : PrimeSpectrum R) :
      Subsingleton (p.asIdeal.ResidueField ⊗[R] N) := by
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨t, rfl⟩ := π.lTensor_surjective p.asIdeal.ResidueField hπ z
    obtain ⟨c, rfl⟩ := H p t
    change (π.lTensor p.asIdeal.ResidueField) (c ⊗ₜ[R] (1 : B)) = 0
    simp [hπ1]
  have hsupport : Module.support R N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := (Module.mem_support_iff_nontrivial_residueField_tensorProduct
      (M := N) p).mp hp
    have := hzero p
    exact not_nontrivial _ ‹Nontrivial (p.asIdeal.ResidueField ⊗[R] N)›
  have : Subsingleton N := Module.support_eq_empty_iff.mp hsupport
  intro b
  have hb : π b = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hb

end Algebra

variable {X Y S X' Y' : Scheme.{u}}

/-- Closed immersion of all target residue fibres is preserved by actual
Cartesian base change. -/
lemma fibreClosedImmersion_of_isPullback {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback a f' f b)
    (H : ∀ y : Y, IsClosedImmersion (f.fiberToSpecResidueField y)) (y' : Y') :
    IsClosedImmersion (f'.fiberToSpecResidueField y') :=
  MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback h y') (H (b y'))

/-- A finite morphism whose target residue fibres are closed immersions is
itself a closed immersion. -/
lemma isClosedImmersion_of_isFinite_of_fibre
    (f : X ⟶ Y) [IsFinite f]
    (H : ∀ y : Y, IsClosedImmersion (f.fiberToSpecResidueField y)) :
    IsClosedImmersion f := by
  wlog hY : ∃ R, Y = Spec R
  · apply IsZariskiLocalAtTarget.of_openCover Y.affineCover
    intro i
    exact this (pullback.snd f (Y.affineCover.f i))
      (fibreClosedImmersion_of_isPullback
        (.of_hasPullback f (Y.affineCover.f i)) H) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B
  · have hAff : IsAffine X := isAffine_of_isAffineHom f
    have hpull : IsPullback (Scheme.isoSpec X).inv ((Scheme.isoSpec X).inv ≫ f)
        f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h := @this X Y _ R ((Scheme.isoSpec X).inv ≫ f) inferInstance
      (fibreClosedImmersion_of_isPullback hpull H) ⟨_, rfl⟩
    exact (MorphismProperty.cancel_left_of_respectsIso
      @IsClosedImmersion (Scheme.isoSpec X).inv f).mp h
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have : Module.Finite R B := (IsFinite.SpecMap_iff φ).mp ‹_›
  apply IsClosedImmersion.spec_of_surjective
  apply algebraMap_surjective_of_fibreScalarMap_surjective
  intro p
  have hp := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Spec.fiberToSpecResidueFieldIso R B p)).mp (H p)
  let ψ := CommRingCat.ofHom (fibreScalarMap (B := B) p)
  have hψ : IsClosedImmersion (Spec.map ψ) := hp
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
  have heq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
      (Scheme.ΓSpecIso _).hom := by simp
  change Function.Surjective ψ
  rw [heq]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp hsurj).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2

/-- For a proper morphism, closed immersion is equivalent to closed immersion
of every actual target residue fibre. -/
lemma isClosedImmersion_iff_fibre_of_isProper (f : X ⟶ Y) [IsProper f] :
    IsClosedImmersion f ↔
      ∀ y : Y, IsClosedImmersion (f.fiberToSpecResidueField y) := by
  constructor
  · intro hf y
    exact MorphismProperty.pullback_snd _ _ hf
  intro H
  have : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_fiberToSpecResidueField f fun y => by
      have := H y
      infer_instance
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  exact isClosedImmersion_of_isFinite_of_fibre f H

/-- The existing morphism between residue fibres over a common base. -/
abbrev relativeFibreMap (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    (f ≫ q).fiber s ⟶ q.fiber s :=
  baseFibreMap f q s

@[reassoc (attr := simp)]
lemma relativeFibreMap_toResidueField (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    relativeFibreMap f q s ≫ q.fiberToSpecResidueField s =
      (f ≫ q).fiberToSpecResidueField s := by
  simp [relativeFibreMap, baseFibreMap, Scheme.Hom.fiberToSpecResidueField]

/-- The relative fibre morphism is the actual base change along the inclusion
of the target fibre. -/
lemma isPullback_relativeFibreMap (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    IsPullback ((f ≫ q).fiberι s) (relativeFibreMap f q s) f (q.fiberι s) := by
  have ho : IsPullback
      (relativeFibreMap f q s ≫ q.fiberToSpecResidueField s)
      ((f ≫ q).fiberι s) (S.fromSpecResidueField s) (f ≫ q) := by
    rw [relativeFibreMap_toResidueField]
    exact (IsPullback.of_hasPullback (f ≫ q) (S.fromSpecResidueField s)).flip
  exact (ho.of_right (baseFibreMap_fiberι f q s)
    (IsPullback.of_hasPullback q (S.fromSpecResidueField s)).flip).flip

end Langlands.AlgebraicGeometry
