import Langlands.AlgebraicGeometry.NoetherianDvrSpecialization
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.GroupScheme.Dynamic.Uniqueness
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finiteness of schematic images in a family of residue-fibre sections -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry

variable {S T X : Scheme.{u}} (q : T ⟶ S) (p : X ⟶ T)

/-- Sections over each residue fibre of `T → S`, written as
preimmersions into `X`. -/
structure ResidueFibreSections where
  hom (s : S) : q.fiber s ⟶ X
  fac (s : S) : hom s ≫ p = q.fiberι s
  isPreimmersion (s : S) : IsPreimmersion (hom s)

namespace ResidueFibreSections

variable {q p} (F : ResidueFibreSections q p)

/-- The union of the ranges of the residue-fibre sections. -/
def range : Set X := ⋃ s : S, Set.range (F.hom s)

/-- Each DVR-valued point of `T` lifts to a map with range in the family. -/
def DvrExtension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ T),
    ∃ g : Spec (CommRingCat.of R) ⟶ X, g ≫ p = b ∧ Set.range g ⊆ F.range

private theorem image_to_base (s : S) (x : q.fiber s) : q (p (F.hom s x)) = s := by
  have hx : p (F.hom s x) = q.fiberι s x := by
    rw [← Scheme.Hom.comp_apply, F.fac]
  rw [hx]
  have h : q.fiberι s x ∈ q ⁻¹' {s} := by
    rw [← q.range_fiberι]
    exact Set.mem_range_self x
  exact h

private theorem injOn : Set.InjOn p F.range := by
  intro x hx y hy h
  obtain ⟨s, a, rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨t, b, rfl⟩ := Set.mem_iUnion.mp hy
  have hst : s = t := (F.image_to_base s a).symm.trans
    ((congrArg q h).trans (F.image_to_base t b))
  subst t
  apply congrArg (F.hom s)
  apply (q.fiberι s).isEmbedding.injective
  simpa only [← Scheme.Hom.comp_apply, F.fac] using h

private theorem exists_lift_of_preimmersion {Y W : Scheme.{u}} (i : Y ⟶ X)
    [IsPreimmersion i] (g : W ⟶ X) [IsReduced W]
    (h : Set.range g ⊆ Set.range i) :
    ∃ l : W ⟶ Y, l ≫ i = g := by
  have : Surjective (pullback.snd i g) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ := h (Set.mem_range_self y)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    exact ⟨z, hz⟩
  have : IsClosedImmersion (pullback.snd i g) :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Set.range_eq_univ.mpr (pullback.snd i g).surjective]
      exact isClosed_univ)
  have : IsIso (pullback.snd i g) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd i g) ≫ pullback.fst i g, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

private theorem field_hom_ext {K : Type u} [Field K] {f g : Spec (CommRingCat.of K) ⟶ X}
    (hf : Set.range f ⊆ F.range) (hg : Set.range g ⊆ F.range)
    (h : f ≫ p = g ≫ p) : f = g := by
  let k : ↥(Spec (CommRingCat.of K)) := closedPoint K
  have hx : f k = g k := F.injOn (hf (Set.mem_range_self k)) (hg (Set.mem_range_self k))
    (congrArg (fun m : Spec (CommRingCat.of K) ⟶ T => m k) h)
  obtain ⟨s, a, ha⟩ := Set.mem_iUnion.mp (hf (Set.mem_range_self k))
  have hr (v : Spec (CommRingCat.of K) ⟶ X) (hv : v k = f k) :
      Set.range v ⊆ Set.range (F.hom s) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨a, ha.trans (hv.symm.trans (congrArg v (Subsingleton.elim k z)))⟩
  let : IsPreimmersion (F.hom s) := F.isPreimmersion s
  obtain ⟨f', hf'⟩ := exists_lift_of_preimmersion (F.hom s) f (hr f rfl)
  obtain ⟨g', hg'⟩ := exists_lift_of_preimmersion (F.hom s) g (hr g hx.symm)
  have he : f' = g' := (cancel_mono (q.fiberι s)).mp (by
    rw [← F.fac, ← Category.assoc, ← Category.assoc, hf', hg', h])
  exact hf'.symm.trans (he ▸ hg')

private theorem fraction_closedPoint {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Spec.algebraMap R K (closedPoint K) =
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R K) (maximalIdeal K) = ⊥
  rw [maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

private theorem stableUnderSpecialization [IsLocallyNoetherian X] [IsSeparated p]
    (hD : F.DvrExtension) : StableUnderSpecialization F.range := by
  intro x y hxy hx
  by_cases e : x = y
  · exact e ▸ hx
  obtain ⟨D⟩ := nonempty_dvrSpecialization X x y hxy e
  let R := D.ring
  let j := Spec.algebraMap R (FractionRing R)
  obtain ⟨g, hg, hr⟩ := hD R (D.map ≫ p)
  have hl : Set.range (j ≫ D.map) ⊆ F.range := by
    rintro _ ⟨z, rfl⟩
    have hj : j z = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) :=
      (congrArg j (Subsingleton.elim z (closedPoint (FractionRing R)))).trans fraction_closedPoint
    have hz : (j ≫ D.map) z = x := (congrArg D.map hj).trans D.generic_image
    rw [hz]
    exact hx
  have he : j ≫ D.map = j ≫ g :=
    F.field_hom_ext hl ((Set.range_comp_subset_range j g).trans hr)
      (by simp only [Category.assoc, hg])
  let : IsSchemeTheoreticallyDominant j :=
    GroupScheme.isSchemeTheoreticallyDominant_specMap (IsFractionRing.injective R (FractionRing R))
  have h' : D.map = g :=
    GroupScheme.ext_of_isSchemeTheoreticallyDominant p hg.symm j he
  rw [← D.closed_image, h']
  exact hr (Set.mem_range_self _)

private theorem closure_range_subset {W : Scheme.{u}} [NoetherianSpace W]
    (a : W ⟶ X) (ha : Set.range a ⊆ F.range)
    (hs : StableUnderSpecialization F.range) : closure (Set.range a) ⊆ F.range := by
  let C := irreducibleComponents W
  let : Finite C := NoetherianSpace.finite_irreducibleComponents
  have hC : (⋃ c : C, (c : Set W)) = Set.univ := by
    rw [← Set.sUnion_eq_iUnion]
    exact sUnion_irreducibleComponents
  have hR : Set.range a = ⋃ c : C, a '' (c : Set W) := by
    rw [← Set.image_iUnion, hC, Set.image_univ]
  rw [hR, closure_iUnion_of_finite]
  intro y hy
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy
  let z := (genericPoints.ofComponent c).val
  have hz : closure {z} = (c : Set W) := genericPoints.isGenericPoint_ofComponent c
  rw [← hz, closure_image_closure a.continuous, Set.image_singleton] at hc
  exact hs (specializes_iff_mem_closure.mpr hc) (ha (Set.mem_range_self z))

variable {A : Type u} [CommRing A]
  {q : Spec (CommRingCat.of A) ⟶ S} {p : X ⟶ Spec (CommRingCat.of A)}

/-- A schematic image of a Noetherian scheme in the family is finite over
the affine target when the family extends along DVR-valued points. -/
def FiniteImages : Prop :=
  IsNoetherianRing A → IsLocallyNoetherian X → IsSeparated p →
    LocallyOfFiniteType p → QuasiCompact p →
    ∀ (F : ResidueFibreSections q p), F.DvrExtension →
    ∀ {W : Scheme.{u}} [NoetherianSpace W] (a : W ⟶ X),
      Set.range a ⊆ F.range → IsFinite (a.imageι ≫ p)

set_option maxHeartbeats 1000000 in
theorem finiteImage_of_dvrExtension : FiniteImages (q := q) (p := p) := by
  intro _ _ _ _ _ F hD W _ a ha
  let i := a.imageι
  let f := i ≫ p
  have hi : Set.range i ⊆ F.range := by
    change Set.range a.ker.subschemeι ⊆ _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
    exact F.closure_range_subset a ha (F.stableUnderSpecialization hD)
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_injective
    (fun _ _ h => i.isClosedEmbedding.injective (F.injOn
      (hi (Set.mem_range_self _)) (hi (Set.mem_range_self _)) h))
  let : UniversallyClosed f := by
    apply universallyClosed_of_forall_isDiscreteValuationRing_hasLift
    intro sq hR
    let : IsDiscreteValuationRing sq.R := hR
    let j := Spec.algebraMap sq.R sq.K
    obtain ⟨g, hg, hr⟩ := hD sq.R sq.i₂
    have he : j ≫ g = sq.i₁ ≫ i :=
      F.field_hom_ext ((Set.range_comp_subset_range j g).trans hr)
        ((Set.range_comp_subset_range sq.i₁ i).trans hi)
        (by rw [Category.assoc, hg, Category.assoc]; exact sq.commSq.w.symm)
    let : IsSchemeTheoreticallyDominant j :=
      GroupScheme.isSchemeTheoreticallyDominant_specMap (IsFractionRing.injective sq.R sq.K)
    have hk : i.ker ≤ g.ker := by
      rw [← show (j ≫ g).ker = g.ker from by
        rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot], he]
      exact sq.i₁.le_ker_comp i
    let l := IsClosedImmersion.lift i g hk
    have hl : l ≫ i = g := IsClosedImmersion.lift_fac _ _ _
    refine ⟨⟨⟨l, (cancel_mono i).mp ?_, ?_⟩⟩⟩
    · rw [Category.assoc, hl, he]
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) hl |>.trans hg)
  let : IsProper f := {}
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end ResidueFibreSections

end Langlands.AlgebraicGeometry
