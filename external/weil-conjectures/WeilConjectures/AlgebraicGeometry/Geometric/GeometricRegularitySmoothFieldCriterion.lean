/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-!
# Geometric regularity and smoothness over a field

Source: Stacks Project, Varieties, Tags 038X (lemma-geometrically-regular-smooth)
and 038T (definition-geometrically-regular).
(blueprint: lem-weil-pbc-geometric-regularity-smooth-field-criterion)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/-- Algebraic separability gives the empty transcendence basis in each subextension. -/
private theorem separableExtension_of_separable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K] :
    Algebra.IsSeparableExtension k K := by
  intro F _
  refine ⟨∅, ?_, inferInstance⟩
  apply (algebraicIndependent_empty (K := k) (A := F)).isTranscendenceBasis_iff_isAlgebraic.mpr
  exact Algebra.IsAlgebraic.extendScalars (R := k) (RingHom.injective (algebraMap k _))

/-- Apply the separable-residue criterion at the rational point over the residue field. -/
private theorem smoothAt_of_regular_tensor
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hreg : ∀ (L : Type u) [Field L] [Algebra k L],
      (⊤ : IntermediateField k L).FG → ∀ q : PrimeSpectrum (TensorProduct k L A),
        IsRegularLocalRing (Localization.AtPrime q.asIdeal)) (p : PrimeSpectrum A) :
    Algebra.IsSmoothAtPrime k p := by
  let K := p.asIdeal.ResidueField
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k A K
  have hfg : (⊤ : IntermediateField k K).FG := IntermediateField.fg_top k K
  let ε : TensorProduct k K A →ₐ[K] K :=
    AlgHom.liftEquiv k K A K (IsScalarTower.toAlgHom k A K)
  let q : PrimeSpectrum (TensorProduct k K A) := ⟨RingHom.ker ε, RingHom.ker_isPrime ε⟩
  have : q.asIdeal.IsPrime := q.isPrime
  let τ : q.asIdeal.ResidueField →ₐ[K] K :=
    Ideal.ResidueField.liftₐ q.asIdeal ε le_rfl (by
      intro b hb
      exact isUnit_iff_ne_zero.mpr hb)
  have : Algebra.IsSeparable K q.asIdeal.ResidueField :=
    ⟨fun x ↦ IsSeparable.of_algHom K τ (Algebra.IsSeparable.isSeparable K (τ x))⟩
  have hsm : Algebra.IsSmoothAtPrime K q :=
    (Algebra.regularLocal_iff_smoothAtPrime K (TensorProduct k K A) q.asIdeal
      (separableExtension_of_separable K q.asIdeal.ResidueField)).mpr (hreg K hfg q)
  have hcontract : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k K A).toRingHom q = p := by
    apply PrimeSpectrum.ext
    ext a
    change ε (TensorProduct.tmul k 1 a) = 0 ↔ a ∈ p.asIdeal
    simp only [ε, AlgHom.liftEquiv_tmul, one_smul]
    change algebraMap A p.asIdeal.ResidueField a = 0 ↔ a ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  exact hcontract ▸ Algebra.isSmoothAtPrime_of_fieldExtension q hsm

namespace AlgebraicGeometry

/-- An open immersion induces isomorphisms on stalks. -/
private theorem regular_stalk_of_openImmersion
    {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsOpenImmersion i]
    (h : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (y : Y) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  have := h (i y)
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv

/-- Smoothness on an affine chart gives regularity of its localized coordinate ring. -/
private theorem regular_stalk_of_smooth_field
    (k : Type u) [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [Smooth f]
    (x : Y) : IsRegularLocalRing (Y.presheaf.stalk x) := by
  obtain ⟨R, i, hi, p, rfl⟩ := Scheme.exists_Spec_apply_eq x
  let : Algebra k R := (Spec.preimage (i ≫ f)).hom.toAlgebra
  have heq : Spec.map (CommRingCat.ofHom (algebraMap k R)) = i ≫ f :=
    Spec.map_preimage _
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
    rw [heq]
    infer_instance
  have : Algebra.Smooth k R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  have := Algebra.smooth_over_field_regular_local k R p.asIdeal
  have : IsRegularLocalRing ((Spec R).presheaf.stalk p) :=
    IsRegularLocalRing.of_ringEquiv (Spec.stalkIso R p).symm.commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (i.stalkMap p)).symm.commRingCatIsoToRingEquiv

/-- Transfer regularity to the tensor-product chart and descend smoothness pointwise. -/
private theorem smooth_affine_chart_of_regular_baseChange
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hreg : ∀ (L : Type u) [Field L] [Algebra k L],
      (⊤ : IntermediateField k L).FG →
      ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
        IsRegularLocalRing
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x))
    (A : CommRingCat.{u}) (i : Spec A ⟶ X) [IsOpenImmersion i] : Smooth (i ≫ f) := by
  let : Algebra k A := (Spec.preimage (i ≫ f)).hom.toAlgebra
  have heq : Spec.map (CommRingCat.ofHom (algebraMap k A)) = i ≫ f :=
    Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [heq]
    infer_instance
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have htensor : ∀ (L : Type u) [Field L] [Algebra k L],
      (⊤ : IntermediateField k L).FG → ∀ q : PrimeSpectrum (TensorProduct k L A),
        IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
    intro L _ _ hfg q
    let a := Spec.map (CommRingCat.ofHom (algebraMap k A))
    let l := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let e := pullbackSymmetry a l ≪≫ pullbackSpecIso k L A
    let j := pullback.map a l f l i (𝟙 _) (𝟙 _) (by simpa [a] using heq)
      (by simp)
    let m := e.inv ≫ j
    have : IsOpenImmersion j := inferInstance
    have : IsOpenImmersion m := inferInstance
    have := regular_stalk_of_openImmersion m (hreg L hfg) q
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of (TensorProduct k L A)) q).commRingCatIsoToRingEquiv
  have hformal : Algebra.FormallySmooth k A := by
    apply Algebra.smoothLocus_eq_univ_iff.mp
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨g, hg, hsm⟩ := smoothAt_of_regular_tensor k A htensor p
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm) hg
  have : Algebra.Smooth k A := ⟨hformal, inferInstance⟩
  rw [← heq]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- A morphism locally of finite type over a field is smooth precisely when every
finitely generated field base change has regular local rings at all points.
Finite generation is as a field, expressed by `IntermediateField.FG` for the top field.
Source: Stacks Project, Varieties, Tags 038X and 038T.
(blueprint: lem-weil-pbc-geometric-regularity-smooth-field-criterion)

Proof following the node:
1. If `f` is smooth, take a smooth affine chart around the image of a point after
   field extension. Use `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, identify its
   base change by `lem-weil-pbc-affine-chart-base-change-iso`, and apply
   `lem-weil-pbc-smooth-ring-map-base-change-composition`. Its localizations are regular
   by `lem-weil-pbc-smooth-over-field-regular-local`; identify the stalk using
   `lem-weil-pbc-affine-open-stalk-localization`.
2. Conversely, choose a finite type affine chart `Spec A` around any point, with prime `p`.
   Its residue field `K` is finitely generated over `k` by
   `lem-weil-pbc-finite-type-residue-field-extension-finitely-generated`.
3. In `B = TensorProduct k K A`, the multiplication map to `K` induced by the residue map has
   maximal kernel `q`, contracts to `p`, and has residue field `K`. Construct it using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`, and identify its localized
   residue field by `def-weil-pbc-localization-at-prime`.
4. The hypothesis and `lem-weil-pbc-affine-open-stalk-localization` make `B_q` regular.
   The algebra `B` is finite type over `K`, and its residue extension is the identity,
   separable by `def-weil-pbc-separable-field-extension`. Apply
   `lem-weil-pbc-regular-local-separable-residue-smooth` to obtain smoothness at `q`.
5. Descend smoothness to `p` with `lem-weil-pbc-smooth-at-prime-field-extension-descent`.
   Thus some principal localization `A_g`, with `g ∉ p`, is smooth over `k`.
6. By `lem-weil-pbc-principal-localization-open-immersion`, this is an open neighbourhood
   of the original point; `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` makes its
   structure morphism smooth. These opens cover `X`, so `def-sbc-smooth-morphisms`
   gives smoothness of `f`. For the empty scheme both conditions are vacuous. -/
theorem smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Smooth f ↔
      ∀ (L : Type u) [Field L] [Algebra k L], (⊤ : IntermediateField k L).FG →
        ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
          IsRegularLocalRing
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) := by
  constructor
  · intro hsm L _ _ _ x
    have : Smooth f := hsm
    exact regular_stalk_of_smooth_field L (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) x
  · intro hreg
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover).mpr
    intro a
    let Y := X.affineCover.X a
    let i : Spec Γ(Y, ⊤) ⟶ X := Y.isoSpec.inv ≫ X.affineCover.f a
    have : Smooth (i ≫ f) := smooth_affine_chart_of_regular_baseChange k f hreg _ i
    have : Smooth (Y.isoSpec.hom ≫ (i ≫ f)) := inferInstance
    simpa [i, Category.assoc] using this

end AlgebraicGeometry
