/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Factor thickenings for a split reduction

Source: smooth purity blueprint, finite-algebra calculation.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The split reduced factor spectra thicken onto a disjoint open partition.

Source: smooth purity blueprint,
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation.
(blueprint: lem-weil-pbc-split-reduction-factor-thickenings).

Proof: Compose Mathlib's finite-product spectrum homeomorphism, the homeomorphism
induced by the supplied algebra equivalence, and the nilradical quotient's
homeomorphism. Each factor's image is open, and bijectivity gives a disjoint
cover, including the empty index set. The ring map from R to each factor is
surjective, so its spectrum map is a closed immersion. Lift this map to its
image open. The lift is surjective by construction and a preimmersion by
cancellation against the open inclusion; its whole image is closed, so it is
a closed immersion. Finally A-linearity of the supplied equivalence identifies
the composite to Spec A with the specified structural morphism. -/
theorem exists_split_reduction_factor_thickenings
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra A (D j)]
    (he : Nonempty ((R ⧸ _root_.nilradical R) ≃ₐ[A] (∀ j, D j))) :
    ∃ (W : Fin r → (Spec (.of R)).Opens),
      (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
      ∀ i, ∃ (a : Spec (.of (D i)) ⟶ (W i).toScheme),
        IsClosedImmersion a ∧ Surjective a ∧
          a ≫ (W i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) =
            Spec.map (CommRingCat.ofHom (algebraMap A (D i))) := by
  classical
  obtain ⟨e⟩ := he
  let π := Ideal.Quotient.mk (_root_.nilradical R)
  let q := Spec.map (CommRingCat.ofHom π)
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hq : IsHomeomorph q := by
    apply isHomeomorph_iff_isEmbedding_surjective.mpr
    exact ⟨q.isClosedEmbedding.isEmbedding,
      (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).surjective⟩
  let H : (Σ i, PrimeSpectrum (D i)) ≃ₜ PrimeSpectrum R :=
    (PrimeSpectrum.sigmaToPiHomeo D).trans
      ((PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm.trans hq.homeomorph)
  let k (i : Fin r) : R →+* D i :=
    (Pi.evalRingHom D i).comp (e.toRingHom.comp π)
  let g (i : Fin r) := Spec.map (CommRingCat.ofHom (k i))
  have hH (i : Fin r) (x : Spec (.of (D i))) : H ⟨i, x⟩ = g i x := rfl
  have hopen (i : Fin r) : IsOpen (Set.range (g i)) := by
    have hi := H.isOpenMap _ (isOpenMap_sigmaMk (i := i) _ isOpen_univ)
    have hr : H '' Set.range (Sigma.mk i) = Set.range (g i) := by
      rw [← Set.range_comp]
      rfl
    rw [Set.image_univ, hr] at hi
    exact hi
  let W (i : Fin r) : (Spec (.of R)).Opens := ⟨Set.range (g i), hopen i⟩
  have hsurj (i : Fin r) (a : Spec (.of (D i)) ⟶ (W i).toScheme)
      (ha : a ≫ (W i).ι = g i) : Function.Surjective a := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f => f x) ha).trans hx
  refine ⟨W, ?_, ?_, ?_⟩
  · apply top_unique
    intro y hy
    obtain ⟨⟨i, x⟩, hx⟩ := H.surjective y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, (hH i x).symm.trans hx⟩
  · intro i j hij
    apply disjoint_iff.mpr
    apply bot_unique
    rintro y ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
    have h := H.injective ((hH i x).trans (hx.trans (hz.symm.trans (hH j z).symm)))
    exact (hij (congrArg Sigma.fst h)).elim
  · intro i
    have hg : IsClosedImmersion (g i) :=
      IsClosedImmersion.spec_of_surjective _
        ((Function.surjective_eval i).comp (e.surjective.comp Ideal.Quotient.mk_surjective))
    let a := IsOpenImmersion.lift (W i).ι (g i) (by rw [Opens.range_ι]; rfl)
    have ha : a ≫ (W i).ι = g i := IsOpenImmersion.lift_fac _ _ _
    have hs : Surjective a := ⟨hsurj i a ha⟩
    have hpre : IsPreimmersion a := by
      have : IsPreimmersion (a ≫ (W i).ι) := ha.symm ▸ inferInstance
      exact IsPreimmersion.of_comp a (W i).ι
    refine ⟨a, IsClosedImmersion.of_isPreimmersion a ?_, hs, ?_⟩
    · rw [Set.range_eq_univ.mpr a.surjective]
      exact isClosed_univ
    · rw [← Category.assoc, ha, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext x
      change e (π (algebraMap A R x)) i = algebraMap A (D i) x
      rw [show π (algebraMap A R x) = algebraMap A (R ⧸ _root_.nilradical R) x from rfl,
        e.commutes]
      rfl

end AlgebraicGeometry.Scheme
