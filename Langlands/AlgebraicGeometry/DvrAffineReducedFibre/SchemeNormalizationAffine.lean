import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.AffineNormalization
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalLocalizations
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreStatement
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.TotalFractions
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Comparing scheme and affine normalization -/

open AlgebraicGeometry CategoryTheory Limits TensorProduct Topology

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- A homeomorphism carries generic points of irreducible components to generic points. -/
theorem mem_genericPoints_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} (hx : x ∈ genericPoints X) :
    e x ∈ genericPoints Y := by
  change closure {e x} ∈ irreducibleComponents Y
  rw [← Set.image_singleton, ← e.image_closure, ← e.preimage_symm]
  exact preimage_mem_irreducibleComponents hx e.symm.isOpenEmbedding
    ⟨x, subset_closure (Set.mem_singleton x), ⟨e x, e.symm_apply_apply x⟩⟩

private def genericPointsEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    genericPoints X ≃ genericPoints Y :=
  (Scheme.homeoOfIso e).toEquiv.subtypeEquiv fun x =>
    ⟨mem_genericPoints_of_homeomorph (Scheme.homeoOfIso e), fun h => by
      change Scheme.homeoOfIso e x ∈ genericPoints Y at h
      simpa only [Homeomorph.symm_apply_apply] using
        mem_genericPoints_of_homeomorph (Scheme.homeoOfIso e).symm h⟩

section RelativeNormalization

variable {V W X Y : Scheme.{u}} (f : V ⟶ X) (g : W ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (i : V ≅ W) (e : X ≅ Y) (h : i.hom ≫ g = f ≫ e.hom)

private def normalizationMapOfSquare : f.normalization ⟶ g.normalization :=
  f.normalizationDesc (i.hom ≫ g.toNormalization) (g.fromNormalization ≫ e.inv) (by
    simp [reassoc_of% h])

@[reassoc (attr := simp)]
private lemma normalizationMapOfSquare_comp :
    normalizationMapOfSquare f g i e h ≫ g.fromNormalization =
      f.fromNormalization ≫ e.hom := by
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id,
    normalizationMapOfSquare, f.normalizationDesc_comp]

@[reassoc (attr := simp)]
private lemma toNormalization_normalizationMapOfSquare :
    f.toNormalization ≫ normalizationMapOfSquare f g i e h = i.hom ≫ g.toNormalization :=
  f.toNormalization_normalizationDesc _ _ _

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in
include h in
private lemma inverseSquare : i.inv ≫ f = g ≫ e.inv := by
  rw [← cancel_mono e.hom, Category.assoc, ← h, ← Category.assoc, i.inv_hom_id,
    Category.id_comp, Category.assoc, e.inv_hom_id, Category.comp_id]

private lemma normalizationMapOfSquare_comp_inverse :
    normalizationMapOfSquare f g i e h ≫
      normalizationMapOfSquare g f i.symm e.symm (inverseSquare f g i e h) =
        𝟙 f.normalization := by
  apply Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization
  · simp
  · simp
  · simp

private def normalizationIsoOfSquare : f.normalization ≅ g.normalization where
  hom := normalizationMapOfSquare f g i e h
  inv := normalizationMapOfSquare g f i.symm e.symm (inverseSquare f g i e h)
  hom_inv_id := normalizationMapOfSquare_comp_inverse f g i e h
  inv_hom_id := normalizationMapOfSquare_comp_inverse g f i.symm e.symm
    (inverseSquare f g i e h)

end RelativeNormalization

section TotalFractions

variable (D : Type u) [CommRing D]

local notation "K" => FractionRing D
local notation "X₀" => Spec (CommRingCat.of D)

private theorem mem_genericPoints_spec_iff (x : PrimeSpectrum D) :
    x ∈ genericPoints X₀ ↔ x.asIdeal ∈ minimalPrimes D := by
  change closure ({x} : Set (PrimeSpectrum D)) ∈ irreducibleComponents (PrimeSpectrum D) ↔ _
  simpa only [PrimeSpectrum.vanishingIdeal_singleton] using
    (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes (s := {x})).symm

private theorem under_minimalPrime [IsArtinianRing K] (q : MaximalSpectrum K) :
    q.asIdeal.under D ∈ minimalPrimes D := by
  change q.asIdeal ∈ Ideal.under D ⁻¹' minimalPrimes D
  have h := IsLocalization.minimalPrimes_map (nonZeroDivisors D) K (⊥ : Ideal D)
  rw [Ideal.map_bot] at h
  rw [← h]
  refine ⟨⟨q.isMaximal.isPrime, bot_le⟩, fun J hJ hle => ?_⟩
  exact ((IsArtinianRing.isPrime_iff_isMaximal J).mp hJ.1).eq_of_le q.isMaximal.ne_top hle |>.ge

private def genericPointMaximalEquiv [IsArtinianRing K] :
    genericPoints X₀ ≃ MaximalSpectrum K where
  toFun x :=
    let hp := (mem_genericPoints_spec_iff D x.1).mp x.2
    let I := x.1.asIdeal.map (algebraMap D K)
    ⟨I, (IsArtinianRing.isPrime_iff_isMaximal I).mp <|
      IsLocalization.isPrime_of_isPrime_disjoint (nonZeroDivisors D) K _ hp.isPrime
        (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp).symm⟩
  invFun q :=
    ⟨⟨q.asIdeal.under D, q.isMaximal.isPrime.comap _⟩,
      (mem_genericPoints_spec_iff D _).mpr (under_minimalPrime D q)⟩
  left_inv x := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint (nonZeroDivisors D) K x.1.isPrime
      (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes
        ((mem_genericPoints_spec_iff D x.1).mp x.2)).symm
  right_inv q := MaximalSpectrum.ext (IsLocalization.map_under (nonZeroDivisors D) K q.asIdeal)

private def fractionQuotientResidueEquiv (p : PrimeSpectrum D) (q : MaximalSpectrum K)
    (hp : p.asIdeal = q.asIdeal.under D) : (K ⧸ q.asIdeal) ≃+* (X₀).residueField p :=
  (RingEquiv.ofBijective _ q.asIdeal.bijective_algebraMap_quotient_residueField).trans <|
    (RingEquiv.ofBijective (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap D K) hp)
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors D) K)
        p.asIdeal q.asIdeal hp)).symm.trans
          (Scheme.Spec.residueFieldIso (.of D) p).symm.commRingCatIsoToRingEquiv

private lemma fractionQuotientResidueEquiv_apply (p : PrimeSpectrum D) (q : MaximalSpectrum K)
    (hp : p.asIdeal = q.asIdeal.under D) (d : D) :
    fractionQuotientResidueEquiv D p q hp (Ideal.Quotient.mk _ (algebraMap D K d)) =
      (Scheme.Spec.residueFieldIso (.of D) p).inv (algebraMap D p.asIdeal.ResidueField d) := by
  let r := RingEquiv.ofBijective (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap D K) hp)
    (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors D) K)
      p.asIdeal q.asIdeal hp)
  change (Scheme.Spec.residueFieldIso (.of D) p).inv
    (r.symm (algebraMap (K ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk _ (algebraMap D K d)))) = _
  congr 1
  apply r.injective
  rw [r.apply_symm_apply]
  exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap D K) hp d).symm

variable {X : Scheme.{u}} (e : X ≅ Spec (CommRingCat.of D))

include e

private def fractionRingResidueProductEquiv [IsReduced K] [IsArtinianRing K] :
    K ≃+* ∀ x : genericPoints X, X.residueField x.1 := by
  let q := (genericPointsEquivOfIso e).trans (genericPointMaximalEquiv D)
  let eq (x : genericPoints X) : (e.hom x.1).asIdeal = (q x).asIdeal.under D :=
    congrArg (fun y : genericPoints X₀ => y.1.asIdeal)
      ((genericPointMaximalEquiv D).symm_apply_apply (genericPointsEquivOfIso e x)).symm
  exact (IsArtinianRing.equivPi K).toRingEquiv.trans <|
    (RingEquiv.piCongrLeft (fun m : MaximalSpectrum K => K ⧸ m.asIdeal) q).symm.trans <|
    RingEquiv.piCongrRight fun x => (fractionQuotientResidueEquiv D _ (q x) (eq x)).trans
      (asIso (e.hom.residueFieldMap x.1)).commRingCatIsoToRingEquiv

private lemma fractionRingResidueProductEquiv_algebraMap [IsReduced K] [IsArtinianRing K]
    (d : D) (x : genericPoints X) : let p : PrimeSpectrum D := e.hom x.1
    fractionRingResidueProductEquiv D e (algebraMap D K d) x =
      e.hom.residueFieldMap x.1 ((Scheme.Spec.residueFieldIso (.of D) p).inv
        (algebraMap D p.asIdeal.ResidueField d)) := by
  dsimp only
  change e.hom.residueFieldMap x.1
    (fractionQuotientResidueEquiv D _ _ _ (Ideal.Quotient.mk _ (algebraMap D K d))) = _
  apply congrArg (e.hom.residueFieldMap x.1)
  exact fractionQuotientResidueEquiv_apply D (e.hom x.1) _ _ d

variable [IsReduced D] [IsNoetherianRing D]

local instance : IsReduced K := isReduced_localizationPreserves (nonZeroDivisors D) K inferInstance

local instance : IsArtinianRing K := isArtinianRing_fractionRing D

private def genericPointResidueFractionIso :
    (∐ fun x : genericPoints X => Spec (X.residueField x.1)) ≅ Spec (.of K) := by
  let q := (genericPointsEquivOfIso e).trans (genericPointMaximalEquiv D)
  letI : Finite (genericPoints X) := Finite.of_injective q q.injective
  exact asIso (sigmaSpec fun x : genericPoints X => X.residueField x.1) ≪≫
    Scheme.Spec.mapIso (fractionRingResidueProductEquiv D e).toCommRingCatIso.op

@[reassoc]
private lemma genericPointResidueFractionIso_hom_comp :
    (genericPointResidueFractionIso D e).hom ≫ Spec.algebraMap D K =
      genericPointResidueMorphism X ≫ e.hom := by
  apply Sigma.hom_ext
  intro x
  simp only [genericPointResidueFractionIso, Iso.trans_hom, asIso_hom, Category.assoc,
    ι_sigmaSpec_assoc, genericPointResidueMorphism, Sigma.ι_comp_desc_assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  change Spec.map _ ≫ Spec.map (fractionRingResidueProductEquiv D e).toCommRingCatIso.hom ≫
    Spec.algebraMap D K = _
  simp only [← Spec.map_comp, Spec.algebraMap]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact fun d => fractionRingResidueProductEquiv_algebraMap D e d x

/-- Over an affine presentation of a reduced Noetherian scheme, normalization in
the generic residue fields is the spectrum of the total-fraction integral closure. -/
def schemeNormalizationAffineIso
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    schemeNormalization X hX ≅ Spec (.of (integralClosure D K)) := by
  let f := genericPointResidueMorphism X
  let g := Spec.algebraMap D K
  let i := genericPointResidueFractionIso D e
  have h : i.hom ≫ g = f ≫ e.hom := genericPointResidueFractionIso_hom_comp D e
  have hf : f = i.hom ≫ g ≫ e.inv := by simp [reassoc_of% h]
  have : QuasiCompact f := by rw [hf]; infer_instance
  have : QuasiSeparated f := by rw [hf]; infer_instance
  exact normalizationIsoOfSquare f g i e h ≪≫ affineNormalizationIso D K

@[reassoc]
lemma schemeNormalizationAffineIso_hom_comp
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (schemeNormalizationAffineIso D e hX).hom ≫ Spec.algebraMap D (integralClosure D K) =
      schemeNormalizationHom X hX ≫ e.hom := by
  simp only [schemeNormalizationAffineIso, Iso.trans_hom, Category.assoc,
    affineNormalizationIso_hom_comp, normalizationIsoOfSquare, normalizationMapOfSquare_comp]

end TotalFractions

section GenericFibre

variable (S D : Type u) [CommRing S] [CommRing D] [Algebra S D] [Module.Flat S D]
    [IsReduced D] [IsNoetherianRing D] [IsIntegrallyClosed (D ⊗[S] FractionRing S)]
    {X : Scheme.{u}} (e : X ≅ Spec (CommRingCat.of D))
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)

local notation "N" => integralClosure D (D ⊗[S] FractionRing S)

/-- With integrally closed generic localization, the scheme normalization on an
affine chart is also the spectrum of the integral closure in that localization. -/
def schemeNormalizationGenericFibreIso :
    schemeNormalization X hX ≅ Spec (.of N) :=
  schemeNormalizationAffineIso D e hX ≪≫ Scheme.Spec.mapIso
    (integralClosureGenericFibreEquivTotalFractions S D).toRingEquiv.toCommRingCatIso.op

@[reassoc]
lemma schemeNormalizationGenericFibreIso_hom_comp :
    (schemeNormalizationGenericFibreIso S D e hX).hom ≫ Spec.algebraMap D N =
      schemeNormalizationHom X hX ≫ e.hom := by
  rw [schemeNormalizationGenericFibreIso, Iso.trans_hom, Category.assoc,
    ← schemeNormalizationAffineIso_hom_comp D e hX]
  congr 1
  change Spec.map
    (integralClosureGenericFibreEquivTotalFractions S D).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.algebraMap D N = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (integralClosureGenericFibreEquivTotalFractions S D).commutes

end GenericFibre

section BaseChange

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

/-- The affine pullback chart with the new base ring on the left of the tensor. -/
def affineBaseChangeIso :
    pullback (Spec.algebraMap R A) (Spec.algebraMap R S) ≅ Spec (.of (S ⊗[R] A)) :=
  pullbackSpecIso R A S ≪≫
    Scheme.Spec.mapIso (Algebra.TensorProduct.comm R S A).toRingEquiv.toCommRingCatIso.op

@[reassoc]
lemma affineBaseChangeIso_hom_comp :
    (affineBaseChangeIso R S A).hom ≫ Spec.algebraMap S (S ⊗[R] A) =
      pullback.snd (Spec.algebraMap R A) (Spec.algebraMap R S) := by
  rw [affineBaseChangeIso, Iso.trans_hom, Category.assoc, ← pullbackSpecIso_hom_snd R A S]
  congr 1
  change Spec.map (Algebra.TensorProduct.comm R S A).toRingEquiv.toCommRingCatIso.hom ≫
    Spec.algebraMap S (S ⊗[R] A) = _
  rw [← Spec.map_comp]
  congr 1

end BaseChange

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
