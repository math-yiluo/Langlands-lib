import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement
import Langlands.Cohomology.FibreDimension
import Langlands.AlgebraicGeometry.Modules.NoetherianCechPerfectRepresentativeProof
import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Modules.GeometricFibreDirectImage
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.Cohomology.DerivedPlus

/-! # Semicontinuity of fibre cohomology for proper flat morphisms: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.FibreDimension

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

attribute [local instance] HasDerivedCategory.standard

namespace FibreSemicontinuity

/-- For a proper flat morphism to the spectrum of a noetherian ring and an invertible module,
one strictly perfect complex computes the derived sections after every base change. -/
theorem exists_perfectModel {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [Flat f] (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    ∃ K : CochainComplex (ModuleCat.{u} R) ℤ, ModuleComplex.IsStrictlyPerfect K ∧
      ∀ (S : CommRingCat.{u}) (φ : R ⟶ S),
        Nonempty (DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K) ≅
          DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex
            (relativeGlobalSections (pullback.snd f (Spec.map φ)))).obj
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj M))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  have hloc : Picard.IsLocallyFreeRankOne M := fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩⟩
  obtain ⟨K, hK, -, hScalar⟩ :=
    noetherianCechPerfectRepresentative R X f M hM.exists_trivialization 𝒰
  refine ⟨K, hK, fun S φ => ?_⟩
  let := φ.hom.toAlgebra
  obtain ⟨αS⟩ := hScalar S φ.hom
  let a := pullback.fst f (Spec.map φ)
  let g := pullback.snd f (Spec.map φ)
  have : ((Scheme.Modules.pullback a).obj M).IsQuasicoherent := hloc.isQuasicoherent_pullback a
  obtain ⟨βS⟩ := CechResolution.nonempty_cechCochainComplex_iso S _ g
    (𝒰.baseChange f S) ((Scheme.Modules.pullback a).obj M)
  exact ⟨αS ≪≫ βS⟩

/-- The point `Spec κ(t) ⟶ T` factors through `Spec Γ(T, V)` by evaluation at `t`. -/
lemma SpecMap_evaluation_fromSpec {T : Scheme.{u}} {V : T.Opens} (hV : IsAffineOpen V) (t : T)
    (ht : t ∈ V) : Spec.map (T.evaluation V t ht) ≫ hV.fromSpec = T.fromSpecResidueField t := by
  rw [← Scheme.germ_residue, Spec.map_comp, Category.assoc]
  change Spec.map (T.residue t) ≫ hV.fromSpecStalk ht = _
  rw [hV.fromSpecStalk_eq_fromSpecStalk ht]
  rfl

/-- The kernel of evaluation at the image `t` of a point `q` of `Spec Γ(T, V)` is `q`. -/
lemma kerPrime_evaluation {T : Scheme.{u}} {V : T.Opens} (hV : IsAffineOpen V)
    (q : Spec Γ(T, V)) (hq : hV.fromSpec q ∈ V) :
    kerPrime (T.evaluation V (hV.fromSpec q) hq).hom = q := by
  apply hV.fromSpec.isOpenEmbedding.injective
  let pt : Spec (T.residueField (hV.fromSpec q)) :=
    IsLocalRing.closedPoint (T.residueField (hV.fromSpec q))
  have h1 : (Spec.map (T.evaluation V (hV.fromSpec q) hq)) pt =
      kerPrime (T.evaluation V (hV.fromSpec q) hq).hom := by
    apply PrimeSpectrum.ext
    ext x
    change x ∈ Ideal.comap (T.evaluation V (hV.fromSpec q) hq).hom
      (IsLocalRing.maximalIdeal _) ↔ x ∈ RingHom.ker (T.evaluation V (hV.fromSpec q) hq).hom
    rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
  have hcomp := congrArg (fun h : Spec (T.residueField (hV.fromSpec q)) ⟶ T => h pt)
    (SpecMap_evaluation_fromSpec hV _ hq)
  simp only [Scheme.fromSpecResidueField_apply] at hcomp
  rw [← h1]
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans hcomp

/-- **Fibre model.** Let `g : Y ⟶ T` be proper and flat, `F` invertible on `Y` and `V` an affine
open of `T` with noetherian ring of sections. There is a strictly perfect complex `K` of
`Γ(T, V)`-modules such that for every `t ∈ V` the fibre cohomology `Hⁿ(Y_t, F_t)` is the homology
of `K ⊗ κ(t)` in degree `n ≥ 0`, and `K ⊗ κ(t)` has no homology in negative degrees. -/
theorem exists_fibreModel {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] [Flat g] (F : Y.Modules)
    (hF : Scheme.Modules.IsInvertible F) {V : T.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(T, V)] :
    ∃ K : CochainComplex (ModuleCat.{u} Γ(T, V)) ℤ, ModuleComplex.IsStrictlyPerfect K ∧
      ∀ (t : T) (ht : t ∈ V),
        (∀ n : ℕ, Nonempty (fibreCohomology g t F n ≅
          ((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n)) ∧
        (∀ n : ℤ, n < 0 → IsZero
          (((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n)) := by
  have : Flat (affineRestrict g hV) := by
    delta affineRestrict
    infer_instance
  obtain ⟨K, hK, hmod⟩ := exists_perfectModel (affineRestrict g hV)
    ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj F) (hF.pullback _)
  refine ⟨K, hK, fun t ht => ?_⟩
  obtain ⟨e⟩ := hmod (T.residueField t) (T.evaluation V t ht)
  have hsq : IsPullback (pullback.fst (affineRestrict g hV) (Spec.map (T.evaluation V t ht)) ≫
      (g ⁻¹ᵁ V).ι) (pullback.snd (affineRestrict g hV) (Spec.map (T.evaluation V t ht))) g
      (T.fromSpecResidueField t) := by
    have := (IsPullback.of_hasPullback (affineRestrict g hV)
      (Spec.map (T.evaluation V t ht))).paste_horiz (isPullback_affineRestrict g hV)
    rwa [SpecMap_evaluation_fromSpec hV t ht] at this
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · obtain ⟨e'⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq F n
    exact ⟨e'.symm ≪≫ (relativeCohomology _ n).mapIso
      ((Scheme.Modules.pullbackComp _ _).app F).symm ≪≫
      (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e n).symm⟩
  · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _).symm
    exact IsZero.of_iso (DerivedPlus.isZero_homology_of_neg _ _ hn)
      ((DerivedCategory.homologyFunctor _ n).mapIso e)

section Algebra

variable {R : Type u} [CommRing R] {k : Type u} [Field k]
  (K : CochainComplex (ModuleCat.{u} R) ℤ) [∀ i, Module.Finite R (K.X i)] (φ : R →+* k)

/-- The homology of the base change of a complex of finite modules to a field is finite. -/
lemma finite_homology_baseChange (n : ℤ) :
    Module.Finite k (((ModuleComplex.baseChange φ).obj K).homology n) := by
  have : Module.Finite k (((ModuleComplex.baseChange φ).obj K).cycles n) :=
    Module.Finite.of_injective (((ModuleComplex.baseChange φ).obj K).iCycles n).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (((ModuleComplex.baseChange φ).obj K).homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

omit [∀ i, Module.Finite R (K.X i)] in
/-- Where `K` vanishes, its base change has no homology. -/
lemma isZero_homology_baseChange_of_isZero {n : ℤ} (h : IsZero (K.X n)) :
    IsZero (((ModuleComplex.baseChange φ).obj K).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ ((ModuleCat.extendScalars φ).map_isZero h)

/-- The alternating sum of the dimensions `d p = dim_k Hᵖ(K ⊗ k)`, `p ≥ 0`, of a base change
without negative homology, up to the sign `(-1)ᵐ`, is the alternating sum of the fibre dimensions
of the terms of `K` over a window `[-m, b]` outside of which `K` vanishes. -/
lemma negOnePow_mul_finsum_eq (m b : ℕ) (hlo : IsZero (K.X (-(m : ℤ) - 1)))
    (hhi : ∀ n : ℤ, (b : ℤ) < n → IsZero (K.X n))
    (hneg : ∀ n : ℤ, n < 0 → IsZero (((ModuleComplex.baseChange φ).obj K).homology n))
    (d : ℕ → ℕ)
    (hd : ∀ p : ℕ, d p = Module.finrank k (((ModuleComplex.baseChange φ).obj K).homology p)) :
    (-1 : ℤ) ^ m * ∑ᶠ p : ℕ, (-1 : ℤ) ^ p * (d p : ℤ) =
      ∑ i ∈ Finset.range (m + (b + 1)),
        (-1 : ℤ) ^ i * fibreDim (K.X (-(m : ℤ) + i)) (kerPrime φ) := by
  have hfin : ∑ᶠ p : ℕ, (-1 : ℤ) ^ p * (d p : ℤ) = ∑ p ∈ Finset.range (b + 1),
      (-1 : ℤ) ^ p *
        (Module.finrank k (((ModuleComplex.baseChange φ).obj K).homology p) : ℤ) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (b + 1)) ?_]
    · exact Finset.sum_congr rfl fun p _ => by rw [hd]
    · intro p hp
      rw [Function.mem_support] at hp
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hpb
      apply hp
      have hz := isZero_homology_baseChange_of_isZero K φ (hhi p (by omega))
      have : Subsingleton (((ModuleComplex.baseChange φ).obj K).homology p) :=
        ModuleCat.isZero_iff_subsingleton.1 hz
      rw [hd, Module.finrank_zero_of_subsingleton]
      simp
  rw [hfin, ← sum_negOnePow_finrank_homology_baseChange K φ (-(m : ℤ)) (m + (b + 1)) hlo
    (hhi _ (by push_cast; omega)), Finset.sum_range_add _ m (b + 1)]
  have h1 : ∑ i ∈ Finset.range m, (-1 : ℤ) ^ i *
      (Module.finrank k (((ModuleComplex.baseChange φ).obj K).homology (-(m : ℤ) + i)) : ℤ) =
        0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : Subsingleton (((ModuleComplex.baseChange φ).obj K).homology (-(m : ℤ) + i)) :=
      ModuleCat.isZero_iff_subsingleton.1 (hneg _ (by omega))
    rw [Module.finrank_zero_of_subsingleton]
    simp
  rw [h1, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show -(m : ℤ) + ((m + j : ℕ) : ℤ) = (j : ℤ) by push_cast; ring, pow_add]
  ring

end Algebra

/-- Every point of a locally noetherian base has an affine neighbourhood with a fibre model. -/
theorem exists_localFibreModel {Y T : Scheme.{u}} [IsLocallyNoetherian T] (g : Y ⟶ T)
    [IsProper g] [Flat g] (F : Y.Modules) (hF : Scheme.Modules.IsInvertible F) (t₀ : T) :
    ∃ (V : T.Opens) (_ : IsAffineOpen V), t₀ ∈ V ∧
      ∃ K : CochainComplex (ModuleCat.{u} Γ(T, V)) ℤ, ModuleComplex.IsStrictlyPerfect K ∧
        ∀ (t : T) (ht : t ∈ V),
          (∀ n : ℕ, Nonempty (fibreCohomology g t F n ≅
            ((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n)) ∧
          (∀ n : ℤ, n < 0 → IsZero
            (((ModuleComplex.baseChange (T.evaluation V t ht).hom).obj K).homology n)) := by
  obtain ⟨V, hV, ht₀, -⟩ := exists_isAffineOpen_mem_and_subset (show t₀ ∈ (⊤ : T.Opens) from trivial)
  have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  exact ⟨V, hV, ht₀, exists_fibreModel g F hF hV⟩

end FibreSemicontinuity

open FibreSemicontinuity in
/-- **Semicontinuity of fibre cohomology** for a proper flat morphism to a locally noetherian
scheme and an invertible module. -/
theorem properFlatFibreCohomologySemicontinuity :
    ProperFlatFibreCohomologySemicontinuityStatement.{u} := by
  intro T Y _ g hgp hgf F hF
  refine ⟨fun t p => ?_, fun t => ?_, fun p r => ?_, fun t₀ => ?_⟩
  · -- finiteness
    obtain ⟨V, hV, ht, K, hK, hmodel⟩ := exists_localFibreModel g F hF t
    have : ∀ i, Module.Finite Γ(T, V) (K.X i) := fun i => (hK.2 i).1
    obtain ⟨e⟩ := (hmodel t ht).1 p
    have := finite_homology_baseChange K (T.evaluation V t ht).hom p
    exact Module.Finite.equiv e.toLinearEquiv.symm
  · -- locally bounded vanishing
    obtain ⟨V, hV, ht, K, hK, hmodel⟩ := exists_localFibreModel g F hF t
    obtain ⟨⟨a, b, -, hb⟩, -⟩ := hK
    refine ⟨V, ht, b.toNat + 1, fun t' ht' p hp => ?_⟩
    obtain ⟨e⟩ := (hmodel t' ht').1 p
    exact IsZero.of_iso (isZero_homology_baseChange_of_isZero K _
      (CochainComplex.isZero_of_isStrictlyLE K b _ (by omega))) e
  · -- upper semicontinuity
    rw [isOpen_iff_forall_mem_open]
    intro t₀ ht₀
    obtain ⟨V, hV, ht₀V, K, hK, hmodel⟩ := exists_localFibreModel g F hF t₀
    have : ∀ i, Module.Finite Γ(T, V) (K.X i) := fun i => (hK.2 i).1
    have : ∀ i, Module.Projective Γ(T, V) (K.X i) := fun i => (hK.2 i).2
    have hdim : ∀ (t : T) (ht : t ∈ V), (fibreCohomologyDim g t F p : ℤ) =
        homologyDim K p (kerPrime (T.evaluation V t ht).hom) := by
      intro t ht
      obtain ⟨e⟩ := (hmodel t ht).1 p
      rw [fibreCohomologyDim, e.toLinearEquiv.finrank_eq]
      exact finrank_homology_baseChange_eq K _ p
    have hset : {t : T | fibreCohomologyDim g t F p < r} ∩ (V : Set T) =
        hV.fromSpec '' {q | homologyDim K p q < r} := by
      ext t
      constructor
      · rintro ⟨h1, h2⟩
        have : t ∈ Set.range hV.fromSpec := by
          rw [hV.range_fromSpec]
          exact h2
        obtain ⟨q, rfl⟩ := this
        refine ⟨q, ?_, rfl⟩
        have := hdim _ h2
        rw [kerPrime_evaluation hV q h2] at this
        change homologyDim K p q < r
        have h1' : (fibreCohomologyDim g (hV.fromSpec q) F p : ℤ) < r := by exact_mod_cast h1
        omega
      · rintro ⟨q, hq, rfl⟩
        have hmem : hV.fromSpec q ∈ V := by
          rw [← SetLike.mem_coe, ← hV.range_fromSpec]
          exact Set.mem_range_self q
        refine ⟨?_, hmem⟩
        have := hdim _ hmem
        rw [kerPrime_evaluation hV q hmem] at this
        change homologyDim K p q < r at hq
        change fibreCohomologyDim g (hV.fromSpec q) F p < r
        omega
    refine ⟨{t : T | fibreCohomologyDim g t F p < r} ∩ (V : Set T), Set.inter_subset_left,
      ?_, ht₀, ht₀V⟩
    rw [hset]
    exact hV.fromSpec.isOpenEmbedding.isOpenMap _
      (isOpen_setOf_homologyDim_lt (n := (p : ℤ)) K (r : ℤ))
  · -- local constancy of the Euler characteristic
    obtain ⟨V, hV, ht₀V, K, hK, hmodel⟩ := exists_localFibreModel g F hF t₀
    have : ∀ i, Module.Finite Γ(T, V) (K.X i) := fun i => (hK.2 i).1
    have : ∀ i, Module.Projective Γ(T, V) (K.X i) := fun i => (hK.2 i).2
    obtain ⟨⟨a, b, ha, hb⟩, -⟩ := hK
    let m := (-a).toNat
    let E : Spec Γ(T, V) → ℤ := fun q => ∑ i ∈ Finset.range (m + (b.toNat + 1)),
      (-1 : ℤ) ^ i * fibreDim (K.X (-(m : ℤ) + i)) q
    have hχ : ∀ q : Spec Γ(T, V), ∀ hq : hV.fromSpec q ∈ V,
        (-1 : ℤ) ^ m * fibreEulerCharacteristic g (hV.fromSpec q) F = E q := by
      intro q hq
      rw [fibreEulerCharacteristic]
      have := negOnePow_mul_finsum_eq K (T.evaluation V (hV.fromSpec q) hq).hom m b.toNat
        (CochainComplex.isZero_of_isStrictlyGE K a _ (by omega))
        (fun n hn => CochainComplex.isZero_of_isStrictlyLE K b _ (by omega))
        ((hmodel _ hq).2) (fun p => fibreCohomologyDim g (hV.fromSpec q) F p) fun p => by
          obtain ⟨e⟩ := (hmodel _ hq).1 p
          exact e.toLinearEquiv.finrank_eq
      rw [kerPrime_evaluation hV q hq] at this
      exact this
    have hmem : ∀ q : Spec Γ(T, V), hV.fromSpec q ∈ V := fun q => by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self q
    have : t₀ ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact ht₀V
    obtain ⟨q₀, rfl⟩ := this
    have hE : IsLocallyConstant E := isLocallyConstant_sum_fibreDim K (-(m : ℤ)) _
    refine ⟨⟨hV.fromSpec '' {q | E q = E q₀},
      hV.fromSpec.isOpenEmbedding.isOpenMap _ (hE.isOpen_fiber _)⟩, ⟨q₀, rfl, rfl⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have h1 := hχ q (hmem q)
    have h2 := hχ q₀ (hmem q₀)
    change E q = E q₀ at hq
    have hsq : ((-1 : ℤ) ^ m) * ((-1 : ℤ) ^ m) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc fibreEulerCharacteristic g (hV.fromSpec q) F
        = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * fibreEulerCharacteristic g (hV.fromSpec q) F := by
          rw [hsq, one_mul]
      _ = (-1 : ℤ) ^ m * E q := by rw [mul_assoc, h1]
      _ = (-1 : ℤ) ^ m * E q₀ := by rw [hq]
      _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * fibreEulerCharacteristic g (hV.fromSpec q₀) F := by
          rw [mul_assoc, h2]
      _ = fibreEulerCharacteristic g (hV.fromSpec q₀) F := by rw [hsq, one_mul]

end Langlands.AlgebraicGeometry.Modules
