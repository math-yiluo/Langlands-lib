/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure


public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# A section on a punctured root cover over the strict henselization

## References

* Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, strictly henselian case
* Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, proof through the finite etale extension C
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Adjoining the group-order root over the strict henselization gives a section. -/
theorem GaloisCover.strict_hensel_root_section
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ s : V.toScheme ⟶ W.P,
      s ≫ W.π ≫ i = V.ι ≫ q ≫ Spec.map b ≫ φ := by
  classical
  dsimp only
  let H := strictHenselization barY
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  obtain ⟨E, p, _, hp, hsurj, δ, hδ⟩ :=
    W.strict_hensel_root_finite_etale_model i G R φ f hG hf β hβ barY b hb
  let : Etale p := hp
  obtain ⟨hlocal, hstrict⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  let : IsLocalRing H := hlocal
  let : IsStrictlyHenselianLocalRing H := hstrict
  have hm : ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g).Monic := by
    exact Polynomial.monic_X_pow_sub_C g (Nat.card_pos.ne')
  let : Module.Finite H A := hm.finite_adjoinRoot
  obtain ⟨σ, hσ⟩ := finite_strict_henselian_algebra_etale_section H A p hsurj
  let l : V.toScheme ⟶ pullback p V.ι :=
    pullback.lift (V.ι ≫ σ) (𝟙 _) (by
      rw [Category.assoc, hσ]
      change V.ι ≫ 𝟙 N = 𝟙 V.toScheme ≫ V.ι
      simp only [Category.comp_id, Category.id_comp])
  change δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
    pullback.snd p V.ι at hδ
  refine ⟨l ≫ δ.hom ≫ pullback.fst (W.π ≫ i)
    (V.ι ≫ q ≫ Spec.map b ≫ φ), ?_⟩
  calc
    (l ≫ δ.hom ≫ pullback.fst (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)) ≫
        W.π ≫ i =
        l ≫ δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) ≫
          (V.ι ≫ q ≫ Spec.map b ≫ φ) := by
      simp only [Category.assoc, pullback.condition]
    _ = V.ι ≫ q ≫ Spec.map b ≫ φ := by
      rw [← Category.assoc δ.hom, hδ]
      change l ≫ pullback.snd p V.ι ≫ (V.ι ≫ q ≫ Spec.map b ≫ φ) = _
      rw [← Category.assoc, show l ≫ pullback.snd p V.ι = 𝟙 _ from
        pullback.lift_snd _ _ _, Category.id_comp]

end AlgebraicGeometry.Scheme
