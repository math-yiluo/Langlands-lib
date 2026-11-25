/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrGenericGaloisNormalization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Principality of the maximal ideal of a normalized Galois component stalk

## References

* Stacks Project, Tags 09EV, 09E8, 00PD and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The maximal ideal of a normalized finite Galois component stalk is principal. -/
theorem dvr_galois_components_normalization_maximalIdeal_isPrincipal
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      Submodule.IsPrincipal (IsLocalRing.maximalIdeal C) := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  let a := pullback.snd (p ≫ j) q
  obtain ⟨hdomA, hdvrA, hmaxA⟩ := dvr_uniformizer_root_algebra B pi hpi n hnpos
  let := hdomA
  let := hdvrA
  obtain ⟨hfinite, hnormal⟩ := dvr_generic_galois_normalization
    B (CommRingCat.of A) q r E hE X p e he hqc hqs
  let := hfinite
  have : IsLocallyNoetherian a.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian a.fromNormalization
  intro x hx
  let s := a.fromNormalization x
  let R := (Spec (CommRingCat.of A)).presheaf.stalk s
  let C := a.normalization.presheaf.stalk x
  obtain ⟨hdomC, hclosedC⟩ := hnormal x
  let := hdomC
  let := hclosedC
  let eR : Localization.AtPrime s.asIdeal ≃+* R :=
    (StructureSheaf.stalkIso A s).toRingEquiv
  let : IsDomain (Localization.AtPrime s.asIdeal) := inferInstance
  have hs : s.asIdeal ≠ ⊥ := by
    rw [hx, ← hmaxA]
    exact Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal A) (IsDiscreteValuationRing.not_isField A)
  let : IsDiscreteValuationRing (Localization.AtPrime s.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hs _
  let : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eR
  let φ := (a.fromNormalization.stalkMap x).hom
  have hqf : φ.QuasiFinite := a.fromNormalization.quasiFiniteAt x
  have hdim : ringKrullDim C ≤ ringKrullDim R := by
    let : Algebra R C := φ.toAlgebra
    have : Algebra.QuasiFinite R C := hqf
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap φ)
    intro v w hvw
    refine lt_of_le_of_ne (Ideal.comap_mono hvw.le) ?_
    intro heq
    have h := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
      v.asIdeal w.asIdeal hvw.le (congrArg PrimeSpectrum.asIdeal heq)
    exact hvw.ne (PrimeSpectrum.ext h)
  have hdimC : ringKrullDim C ≤ 1 :=
    hdim.trans_eq (IsDiscreteValuationRing.ringKrullDim_eq_one R)
  let : Ring.DimensionLEOne C := ⟨fun {I} hI hi ↦
    (Ring.krullDimLE_one_iff_of_isPrime_bot.mp
      (Ring.krullDimLE_iff.mpr (by simpa using hdimC))) I hI hi⟩
  let : IsDedekindDomain C :=
    { (inferInstance : IsNoetherianRing C), (inferInstance : Ring.DimensionLEOne C),
      hdomC, hclosedC with }
  exact maximalIdeal_isPrincipal_of_isDedekindDomain C

end AlgebraicGeometry.Scheme
