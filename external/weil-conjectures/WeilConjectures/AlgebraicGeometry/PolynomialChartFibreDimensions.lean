/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Dimension formulas for the canonical polynomial fibre chart

Source: Stacks Project, Tags 00RE and 00P1.
(blueprint: lem-sbc-polynomial-chart-fibre-dimensions)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem polynomial_dim {k : Type u} [Field k] (n : ℕ)
    (p : Spec (.of (MvPolynomial (ULift.{u} (Fin n)) k))) :
    topologicalKrullDimAt p = (n : WithBot ℕ∞) := by
  let f := Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin n)) (R := k)))
  have : SmoothOfRelativeDimension n f := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr
      (by
        simpa using (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension
          (Nat.card (ULift.{u} (Fin n))) k (MvPolynomial (ULift.{u} (Fin n)) k)))
  exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension f n p

private theorem ring_dimensions {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (n : ℕ)
    (φ : MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] B) (hφ : φ.toRingHom.QuasiFinite)
    (q : PrimeSpectrum B) :
    ∃ d r t : ℕ,
      ringKrullDim (Localization.AtPrime (q.asIdeal.comap φ.toRingHom)) =
        (d : WithBot ℕ∞) ∧
      ringKrullDim (Localization.AtPrime q.asIdeal) = (r : WithBot ℕ∞) ∧
      topologicalKrullDimAt (X := Spec (.of B)) q = ((r + t : ℕ) : WithBot ℕ∞) ∧
      n = d + t := by
  let P := MvPolynomial (ULift.{u} (Fin n)) k
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower k P B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.QuasiFinite P B := hφ
  let p := q.asIdeal.under P
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have htrdeg : Algebra.trdeg k p.ResidueField = Algebra.trdeg k q.asIdeal.ResidueField := by
    have : Module.Finite p.ResidueField q.asIdeal.ResidueField := inferInstance
    have he := trdeg_add_eq k p.ResidueField (A := q.asIdeal.ResidueField)
    simpa only [trdeg_eq_zero, add_zero] using he
  obtain ⟨r, t, hr, ht, hq⟩ := topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q.asIdeal
  obtain ⟨d, t', hd, ht', hp⟩ := topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) p
  have htt : t' = t := by
    rw [ht, ht'] at htrdeg
    exact_mod_cast htrdeg
  have hpoly := polynomial_dim n (⟨p, inferInstance⟩ : Spec (.of P))
  have hdt : n = d + t := by
    rw [htt] at hp
    exact_mod_cast (hpoly.symm.trans hp)
  exact ⟨d, r, t, hd, hr, hq, hdt⟩

private theorem localDim_homeomorph_le {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (i : Y ≃ₜ Z) (y : Y) :
    topologicalKrullDimAt y ≤ topologicalKrullDimAt (i y) := by
  refine le_iInf₂ fun O hy ↦ ?_
  let V : TopologicalSpace.Opens Y := ⟨i ⁻¹' O, O.isOpen.preimage i.continuous⟩
  let iV : V ≃ₜ O := i.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hy).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq iV iV.isHomeomorph)

private theorem localDim_homeomorph {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (i : Y ≃ₜ Z) (y : Y) :
    topologicalKrullDimAt y = topologicalKrullDimAt (i y) := by
  exact le_antisymm (localDim_homeomorph_le i y)
    (by simpa using localDim_homeomorph_le i.symm (i y))

private theorem localDim_openImmersion {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (y : Y) : topologicalKrullDimAt y = topologicalKrullDimAt (j y) := by
  exact (localDim_homeomorph j.isOpenEmbedding.toHomeomorph y).trans
    (j.isOpenEmbedding.isOpen_range.topologicalKrullDimAt_eq ⟨y, rfl⟩)

/-- The fibre and its polynomial chart have the same residue transcendence degree.

Source: Stacks Project, Tag 00RE, first paragraph of its proof, and Tag 00P1.
Proof: set p = f(U.ι x), k = kappa(p), and V = (U.ι ≫ f).fiber p.
The base-changed chart maps V quasi-finitely into polynomial n-space over k.
The finite type k-algebra of the affine scheme V and the polynomial algebra
are Noetherian. The dimension formula of Tag 00P1 gives finite local dimensions
r and d and finite residue transcendence degrees at the point and its image.
Quasi-finiteness makes the residue extension finite, so the two transcendence
degrees coincide; write their common natural-number value as t. Polynomial
n-space has local topological dimension n at every point. Applying the dimension
formula there gives n = d + t. At the point of V it gives r + t. The open
immersion of V into f.fiber p identifies their stalks and preserves local
topological dimension, giving the displayed identities for the actual fibre.
No flatness hypothesis is needed for these dimension formulas.
(blueprint: lem-sbc-polynomial-chart-fibre-dimensions) -/
theorem polynomial_chart_fibre_dimensions
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e] [LocallyQuasiFinite e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    let S := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))
    ∃ d r t : ℕ,
      ringKrullDim (PolynomialChart.sourceStalk f U n e he x) = (d : WithBot ℕ∞) ∧
      ringKrullDim S = (r : WithBot ℕ∞) ∧
      topologicalKrullDimAt (f.asFiber (U.ι x)) = ((r + t : ℕ) : WithBot ℕ∞) ∧
      n = d + t := by
  let p := f (U.ι x)
  let k := T.residueField p
  let P := CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) k)
  let V := (U.ι ≫ f).fiber p
  have : IsAffine V := by dsimp [V]; infer_instance
  let y := PolynomialChart.fibrePoint f U x
  let W := (AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiber p
  let c := PolynomialChart.fibreMap f U n e he p
  let i : W ≅ Spec P :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin n))
      (T.fromSpecResidueField p)).isoPullback.symm ≪≫
      AffineSpace.SpecIso (ULift.{u} (Fin n)) (T.residueField p)
  let B := Γ(V, ⊤)
  let b := V.isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (b.inv ≫ c ≫ i.hom)
  have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have hqf : φ.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp inferInstance
  have hft : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let := (φ.hom.comp (MvPolynomial.C (σ := ULift.{u} (Fin n)) (R := k))).toAlgebra
  have : Algebra.FiniteType k B := by
    rw [← RingHom.finiteType_algebraMap]
    exact hft.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  let φa : MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] B :=
    { φ.hom with commutes' := fun _ ↦ rfl }
  let q := b.hom y
  obtain ⟨d, r, t, hd, hr, htop, hn⟩ := ring_dimensions n φa hqf q
  have hpoint : Spec.map φ q = i.hom (c y) := by
    change (b.hom ≫ Spec.map φ) y = i.hom (c y)
    rw [hφ, ← Category.assoc b.hom b.inv _, b.hom_inv_id, Category.id_comp]
    exact Scheme.Hom.comp_apply c i.hom y
  have hR : ringKrullDim (PolynomialChart.sourceStalk f U n e he x) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.comap φ.hom)) := by
    let j := (asIso (i.hom.stalkMap (c y))).symm ≪≫ Spec.stalkIso P (i.hom (c y))
    have hj := ringKrullDim_eq_of_ringEquiv j.commRingCatIsoToRingEquiv
    rw [← hpoint] at hj
    exact hj
  have hV : ringKrullDim (V.presheaf.stalk y) =
      ringKrullDim (Localization.AtPrime q.asIdeal) :=
    ringKrullDim_eq_of_ringEquiv
      ((asIso (b.hom.stalkMap y)).symm ≪≫ Spec.stalkIso B q).commRingCatIsoToRingEquiv
  let j := PolynomialChart.fibreInclusion f U p
  let a : V.presheaf.stalk y ≅
      (f.fiber p).presheaf.stalk (f.asFiber (U.ι x)) :=
    (asIso (j.stalkMap y)).symm ≪≫
      eqToIso (congrArg (f.fiber p).presheaf.stalk
        (PolynomialChart.fibreInclusion_asFiber f U x))
  have hS : ringKrullDim ((f.fiber p).presheaf.stalk (f.asFiber (U.ι x))) =
      ringKrullDim (Localization.AtPrime q.asIdeal) :=
    (ringKrullDim_eq_of_ringEquiv a.commRingCatIsoToRingEquiv).symm.trans hV
  have htopV : topologicalKrullDimAt y = topologicalKrullDimAt q :=
    localDim_homeomorph (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso b)) y
  have htopS : topologicalKrullDimAt y = topologicalKrullDimAt (f.asFiber (U.ι x)) := by
    rw [← PolynomialChart.fibreInclusion_asFiber f U x]
    exact localDim_openImmersion j y
  exact ⟨d, r, t, hR.trans hd, hS.trans hr, htopS.symm.trans (htopV.trans htop), hn⟩

end AlgebraicGeometry
