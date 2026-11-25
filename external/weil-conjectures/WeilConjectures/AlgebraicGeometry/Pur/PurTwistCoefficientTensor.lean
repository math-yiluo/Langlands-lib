/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Finite coefficient extension and sheafwise completion

## References

* Bhatt--Scholze, Definition 6.8.1 and Lemma 4.2.12
* Stacks Project, Tags 03EK and 03P5
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u v w
open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Continuous-function fpqc descent, restricted to the pro-etale site. -/
private theorem coefficientContinuousPresheaf_isSheaf (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (ProEtale.lisseContinuousCommRingPresheafUniverses X T) := by
  let : CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1}
      CommRingCat.{max (u + 1) v} :=
    CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u + 1, max (u + 1) v,
      max (u + 1) v} _
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (ProEtale.lisseContinuousCommRingPresheafUniverses X T)
      (CategoryTheory.forget CommRingCat.{max (u + 1) v})]
  let e : ProEtale.lisseContinuousCommRingPresheafUniverses X T ⋙
      CategoryTheory.forget CommRingCat.{max (u + 1) v} ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙
        continuousMapPresheaf T ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  rw [Presheaf.isSheaf_of_iso_iff e]
  refine Functor.op_comp_isSheaf_of_isSheaf
    (F := Scheme.ProEt.forget X ⋙ Over.forget X)
    (J := Scheme.ProEt.topology X) (K := Scheme.proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le
    Scheme.proetaleTopology_le_fpqcTopology

/-- The existing continuous-function presheaf with its proved sheaf condition. -/
private noncomputable def coefficientContinuousSheaf (X : Scheme.{t})
    (T : Type (max u (t + 1))) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} :=
  ⟨ProEtale.lisseContinuousCommRingPresheafUniverses X T,
    coefficientContinuousPresheaf_isSheaf X T⟩

/-- The coefficient valuation ring is finite free over `ℤ_[l]`. -/
private theorem integral_basis (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E))) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let : Algebra ℤ_[l] O := (purTwistIntegersMap l E).toAlgebra
  let : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have hmap (z : ℤ_[l]) : (purTwistIntegersMap l E z : E) =
      algebraMap ℚ_[l] E (z : ℚ_[l]) :=
    (purTwistIntegersMap_existsUnique l E).exists.choose_spec z
  let : IsScalarTower ℤ_[l] O E := IsScalarTower.of_algebraMap_eq fun z ↦ (hmap z).symm
  have hO := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsFractionRing O E := hO.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hO.2.2.2.2.2.2.2.2.1
  have : IsIntegrallyClosedIn O E :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mp inferInstance
  have hInt (x : E) : x ∈ O ↔ _root_.IsIntegral ℤ_[l] x := by
    constructor
    · intro hx
      have hmon := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x)
      have hcoeff := (spectralValue_le_one_iff hmon).mp ((hO.1 x).mp hx)
      have hlift : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨(minpoly ℚ_[l] x).coeff n, hcoeff n⟩, rfl⟩
      obtain ⟨q, hq, _, hqmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
      refine ⟨q, hqmon, ?_⟩
      change q.eval₂ ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])) x = 0
      rw [← Polynomial.eval₂_map, hq]
      exact minpoly.aeval ℚ_[l] x
    · intro hx
      have hx' : _root_.IsIntegral O x := hx.tower_top
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := O) (R := O)).mp hx'
      exact hy ▸ y.property
  let : IsIntegralClosure O ℤ_[l] E :=
    ⟨Subtype.val_injective, fun {x} ↦ by
      rw [← hInt]
      exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩⟩
  have : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite ℤ_[l] O := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E O
  have : Module.IsTorsionFree ℤ_[l] E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap ℚ_[l] E).injective.comp
        (show Function.Injective (algebraMap ℤ_[l] ℚ_[l]) from Subtype.val_injective))
  have : Module.Free ℤ_[l] O := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E O
  exact ⟨Module.finrank ℤ_[l] O, ⟨Module.finBasis ℤ_[l] O⟩⟩

/-- The finite integral basis gives bases on the actual constant coefficient
section rings, including sections which are only locally constant. -/
private theorem coefficient_section_basis (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (n : ℕ) (b : ∀ U : S.ProEtᵒᵖ,
      @Module.Basis (Fin n) ((purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U)
        ((purTwistIntegralConstant S l E).obj.obj U) _ _
        (Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app U).hom)),
      ∀ (U V : S.ProEtᵒᵖ) (f : U ⟶ V)
        (s : (purTwistIntegralConstant S l E).obj.obj U) (i : Fin n),
        letI : Module ((purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U)
            ((purTwistIntegralConstant S l E).obj.obj U) :=
          Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app U).hom
        letI : Module ((purTwistZlConstantOfUniverses.{t, u} S l).obj.obj V)
            ((purTwistIntegralConstant S l E).obj.obj V) :=
          Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app V).hom
        (b V).equivFun ((purTwistIntegralConstant S l E).obj.map f s) i =
          (purTwistZlConstantOfUniverses.{t, u} S l).obj.map f ((b U).equivFun s i) := by
  let := WeilConjectures.integralCoefficientRingSheafify.{t, u} S
  let := WeilConjectures.integralCoefficientAbSheafify.{t, u} S
  obtain ⟨k, ⟨b⟩⟩ := integral_basis l E
  let O := Padic.coefficientExtensionIntegers l E
  let : Module ℤ_[l] O := Module.compHom O (purTwistIntegersMap l E)
  let φ : ULift.{max u (t + 1)} ℤ_[l] →+* ULift.{t + 1} O :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((purTwistIntegersMap l E).comp ULift.ringEquiv.toRingHom)
  let : Algebra (ULift.{max u (t + 1)} ℤ_[l]) (ULift.{t + 1} O) := φ.toAlgebra
  let b' : Module.Basis (Fin k) (ULift.{max u (t + 1)} ℤ_[l]) (ULift.{t + 1} O) :=
    (b.map ULift.moduleEquiv.symm).mapCoeffs ULift.ringEquiv.symm (fun _ _ ↦ rfl)
  have : Module.Free (ULift.{max u (t + 1)} ℤ_[l]) (ULift.{t + 1} O) :=
    Module.Free.of_basis b'
  have : Module.Finite (ULift.{max u (t + 1)} ℤ_[l]) (ULift.{t + 1} O) :=
    Module.Finite.of_basis b'
  exact @CategoryTheory.constantFiniteFree_sectionBasis.{t + 1, t, u}
    S.ProEt inferInstance (ProEt.topology S)
    (WeilConjectures.integralCoefficientRingSheafify.{t, u} S)
    (inferInstanceAs ((ProEt.topology S).HasSheafCompose
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})))
    (WeilConjectures.integralCoefficientAbSheafify.{t, u} S)
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, u} S)
    (CommRingCat.of (ULift.{max u (t + 1)} ℤ_[l])) (CommRingCat.of (ULift.{t + 1} O))
    inferInstance inferInstance inferInstance

/-- Finite freeness suffices for the tensor/completion map over any ring,
including the possibly non-Noetherian section rings used here. -/
private theorem finiteFreeCompletionTensor {R : Type v} [CommRing R] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.ofTensorProduct I M) := by
  classical
  let n := Fintype.card (Module.Free.ChooseBasisIndex R M)
  let b := (Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)
  let e := b.equivFun
  let eT := LinearEquiv.baseChange R (AdicCompletion I R) M (Fin n → R) e
  let eC := AdicCompletion.congr I e
  have hnat (x : AdicCompletion I R ⊗[R] M) :
      eC (AdicCompletion.ofTensorProduct I M x) =
        AdicCompletion.ofTensorProduct I (Fin n → R) (eT x) :=
    LinearMap.congr_fun (AdicCompletion.ofTensorProduct_naturality I e.toLinearMap) x
  have hpi := AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype I
    (Fin n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eT.injective
    apply hpi.injective
    exact (hnat x).symm.trans ((congrArg eC hxy).trans (hnat y))
  · intro y
    obtain ⟨z, hz⟩ := hpi.surjective (eC y)
    refine ⟨eT.symm z, eC.injective ?_⟩
    rw [hnat, LinearEquiv.apply_symm_apply]
    exact hz

/-- The l-adic and uniformizer-adic filtrations are cofinal: l itself is
associated to a positive power of the recorded uniformizer. -/
private theorem prime_uniformizer_power (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ e : ℕ, 0 < e ∧ ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
      (l : Padic.coefficientExtensionIntegers l E) =
        v * Padic.coefficientExtensionUniformizer l E ^ e := by
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsLocalRing O := h.2.2.2.1
  have : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = m :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = m :=
    h.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  have : CharZero E := charZero_of_injective_algebraMap
    (algebraMap ℚ_[l] E).injective
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hsmall : abv (l : E) < 1 := by
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  have hnonunit : ¬IsUnit (l : O) := by
    intro hu
    exact (ne_of_lt hsmall) ((h.2.2.1 (l : O)).mp hu)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hirr
  refine ⟨e, Nat.pos_of_ne_zero ?_, v, hv⟩
  rintro rfl
  apply hnonunit
  rw [hv, pow_zero, mul_one]
  exact v.isUnit

/-- The two coefficient filtrations agree on a cofinal subsequence, with the
inclusion needed to reduce a later cofinal entry to an arbitrary exponent. -/
private theorem coefficient_filtrations (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ e : ℕ, 0 < e ∧
      (∀ r : ℕ,
        (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r =
          Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ (e * r)) ∧
      ∀ n : ℕ, ∃ r : ℕ, n ≤ e * r ∧
        (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r ≤
          Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ n := by
  obtain ⟨e, he, v, hv⟩ := prime_uniformizer_power l E
  have hI : Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) =
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ e := by
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow]
  have hpow (r : ℕ) :
      (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r =
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ (e * r) := by
    rw [hI, pow_mul]
  refine ⟨e, he, hpow, fun n ↦ ⟨n, ?_, ?_⟩⟩
  · exact Nat.le_mul_of_pos_left n he
  · rw [hpow]
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def continuousCoefficientConstants (S : Scheme.{t})
    (R : Type (max u (t + 1))) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R) ⟶
      (coefficientContinuousSheaf S R).obj where
  app _ := CommRingCat.ofHom
    { toFun := fun r ↦ ULift.up (ContinuousMap.const _ r)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The constant pro-étale ring sheaf on a discrete ring is the sheaf of continuous
(locally constant) coefficient functions, compatibly with the constants. -/
private theorem discreteCoefficientComparisonOfUniverses (S : Scheme.{t})
    (R : Type (max u (t + 1))) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] :
    letI := WeilConjectures.integralCoefficientRingSheafify.{t, u} S
    ∃ e : (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj (CommRingCat.of R) ≅
        coefficientContinuousSheaf S R,
      toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
        (CommRingCat.of R)) ≫ e.hom.hom = continuousCoefficientConstants S R := by
  classical
  let := WeilConjectures.integralCoefficientRingSheafify.{t, u} S
  let : EssentiallySmall.{max u (t + 1)} S.ProEt := essentiallySmallSelf _
  let : (ProEt.topology S).WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let P := (Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R)
  let H := coefficientContinuousSheaf S R
  let c := continuousCoefficientConstants S R
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology S) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (ProEt.topology S).superset_covering (fun _ _ _ ↦ rfl)
        ((ProEt.topology S).top_mem _)
    · have hempty : IsEmpty W.unop.left := ⟨fun x ↦ h (by
        exact congrArg (fun z ↦ z.down x) hab)⟩
      let j : ∀ i : PEmpty.{t + 1}, (i.elim : Scheme.{t}) ⟶ W.unop.left :=
        fun i ↦ i.elim
      let : ∀ i, IsOpenImmersion (j i) := fun i ↦ i.elim
      apply ProEt.mem_topology_of_openImmersion _ j
      · intro x
        exact isEmptyElim x
      · intro i
        exact i.elim
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology S) c := by
    constructor
    intro W s
    let f : C(W.left, R) := s.down
    let V (x : W.left) : W.left.Opens :=
      ⟨f ⁻¹' {f x}, f.continuous.isOpen_preimage _ (isOpen_discrete _)⟩
    apply ProEt.mem_topology_of_openImmersion _ (fun x ↦ (V x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro y
      exact y.property.symm
  let φ : (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of R) ⟶ H :=
    ⟨sheafifyLift (ProEt.topology S) c H.property⟩
  have hφ : toSheafify (ProEt.topology S) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (ProEt.topology S) c H.property
  have : IsIso φ := by
    apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
    constructor
    · change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (ProEt.topology S) P), hφ]
      exact hinj
    · change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (ProEt.topology S) P), hφ]
      exact hsurj
  exact ⟨asIso φ, hφ⟩

/-- The comparison of sheafified discrete constants at the tied universes, as used by
`import all` importers. -/
private theorem discreteCoefficientComparison (S : Scheme.{t})
    (R : Type (t + 1)) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] :
    letI := WeilConjectures.integralCoefficientRingSheafify.{t, t} S
    ∃ e : (constantSheaf (ProEt.topology S) CommRingCat.{t + 1}).obj (CommRingCat.of R) ≅
        coefficientContinuousSheaf.{t, t} S R,
      toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
        (CommRingCat.of R)) ≫ e.hom.hom = continuousCoefficientConstants.{t, t} S R :=
  discreteCoefficientComparisonOfUniverses.{t, t} S R

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def continuousCoefficientMap (S : Scheme.{t})
    {R T : Type (max u (t + 1))} [CommRing R] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace T] [IsTopologicalRing R] [IsTopologicalRing T]
    (f : R →+* T) (hf : Continuous f) :
    coefficientContinuousSheaf S R ⟶
      coefficientContinuousSheaf S T :=
  ⟨{ app := fun U ↦ CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((f.compLeftContinuous U.unop.left hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem discreteComparison_naturality (S : Scheme.{t})
    {R T : Type (max u (t + 1))} [CommRing R] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace T] [IsTopologicalRing R] [IsTopologicalRing T]
    [DiscreteTopology R] [DiscreteTopology T] (f : R →+* T)
    (eR : (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of R) ≅ coefficientContinuousSheaf S R)
    (eT : (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of T) ≅ coefficientContinuousSheaf S T)
    (hR : toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
      (CommRingCat.of R)) ≫ eR.hom.hom = continuousCoefficientConstants S R)
    (hT : toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
      (CommRingCat.of T)) ≫ eT.hom.hom = continuousCoefficientConstants S T) :
    (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
        (CommRingCat.ofHom f) ≫ eT.hom =
      eR.hom ≫ continuousCoefficientMap S f continuous_of_discreteTopology := by
  let := WeilConjectures.integralCoefficientRingSheafify.{t, u} S
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (D := CommRingCat.{max u (t + 1)})
    (ProEt.topology S) _ _ (coefficientContinuousSheaf S T).property
  change toSheafify _ _ ≫ (_ ≫ eT.hom.hom) = toSheafify _ _ ≫ (eR.hom.hom ≫ _)
  rw [← Category.assoc, ← Category.assoc, hR]
  change (toSheafify _ _ ≫ sheafifyMap (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).map (CommRingCat.ofHom f))) ≫ eT.hom.hom = _
  rw [← toSheafify_naturality, Category.assoc, hT]
  rfl

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A section of a surjective map of discrete rings lifts pointwise. For a principal
kernel, choose the pointwise quotient by its generator. Both choices are continuous
because their source rings are discrete. -/
private theorem continuous_principal_quotient {X R T : Type*} [TopologicalSpace X]
    [CommRing R] [CommRing T] [TopologicalSpace R] [TopologicalSpace T]
    [IsTopologicalRing R] [IsTopologicalRing T] [DiscreteTopology R] [DiscreteTopology T]
    (f : R →+* T) (a : R) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {a}) :
    Function.Surjective (f.compLeftContinuous X continuous_of_discreteTopology) ∧
      ∀ s : C(X, R), f.compLeftContinuous X continuous_of_discreteTopology s = 0 ↔
        ∃ t : C(X, R), ContinuousMap.const X a * t = s := by
  classical
  constructor
  · intro s
    let g := Function.surjInv hs
    refine ⟨⟨g ∘ s, continuous_of_discreteTopology.comp s.continuous⟩, ?_⟩
    ext x
    exact Function.surjInv_eq hs (s x)
  · intro s
    constructor
    · intro h
      have hdiv (r : R) (hr : f r = 0) : ∃ t : R, a * t = r := by
        have hm : r ∈ Ideal.span {a} := hk ▸ hr
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hm
        exact ⟨t, ht.symm⟩
      let g : R → R := fun r ↦ if h : f r = 0 then (hdiv r h).choose else 0
      have hg (r : R) (hr : f r = 0) : a * g r = r := by
        dsimp only [g]
        rw [dite_eq_left hr]
        exact (hdiv r hr).choose_spec
      refine ⟨⟨g ∘ s, continuous_of_discreteTopology.comp s.continuous⟩, ?_⟩
      ext x
      exact hg (s x) (congrArg (fun t : C(X, T) ↦ t x) h)
    · rintro ⟨t, rfl⟩
      ext x
      change f (a * t x) = 0
      rw [map_mul, show f a = 0 from by
        change a ∈ RingHom.ker f
        rw [hk]
        exact Ideal.subset_span (Set.mem_singleton a), zero_mul]

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem constantSection_principal_quotientOfUniverses (S : Scheme.{t})
    {R T : Type (max u (t + 1))} [CommRing R] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace T] [IsTopologicalRing R] [IsTopologicalRing T]
    [DiscreteTopology R] [DiscreteTopology T]
    (f : R →+* T) (a : R) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {a}) (U : S.ProEtᵒᵖ) :
    let F := constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}
    let q := ((F.map (CommRingCat.ofHom f)).hom.app U).hom
    let c := (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).app U a
    Function.Surjective q ∧ ∀ s, q s = 0 ↔ ∃ t, c * t = s := by
  let := WeilConjectures.integralCoefficientRingSheafify.{t, u} S
  dsimp only
  obtain ⟨eR, hR⟩ := discreteCoefficientComparisonOfUniverses S R
  obtain ⟨eT, hT⟩ := discreteCoefficientComparisonOfUniverses S T
  let er := (((sheafToPresheaf _ CommRingCat.{max u (t + 1)}) ⋙
    (CategoryTheory.evaluation _ _).obj U).mapIso eR).commRingCatIsoToRingEquiv
  let et := (((sheafToPresheaf _ CommRingCat.{max u (t + 1)}) ⋙
    (CategoryTheory.evaluation _ _).obj U).mapIso eT).commRingCatIsoToRingEquiv
  let q := (((constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom f)).hom.app U).hom
  let c := (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).app U a
  have hn (s) : (et (q s)).down =
      f.compLeftContinuous U.unop.left continuous_of_discreteTopology (er s).down := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun g ↦ g.hom.app U) (discreteComparison_naturality S f eR eT hR hT)) s
    exact congrArg ULift.down h
  have hc : er c = ULift.up (ContinuousMap.const U.unop.left a) :=
    congrArg (fun g ↦ g.app U a) hR
  obtain ⟨hqs, hqk⟩ := continuous_principal_quotient (X := U.unop.left) f a hs hk
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hqs (et y).down
    refine ⟨er.symm (ULift.up z), et.injective ?_⟩
    apply ULift.ext
    rw [hn, er.apply_symm_apply]
    exact hz
  · intro s
    constructor
    · intro h
      obtain ⟨t, ht⟩ := (hqk (er s).down).mp (by rw [← hn, h, map_zero]; rfl)
      refine ⟨er.symm (ULift.up t), er.injective ?_⟩
      rw [map_mul, hc, er.apply_symm_apply]
      apply ULift.ext
      exact ht
    · rintro ⟨t, rfl⟩
      apply et.injective
      apply ULift.ext
      rw [hn, map_zero, map_mul, hc]
      exact (hqk _).mpr ⟨(er t).down, rfl⟩

/-- The principal-quotient section formula at the tied universes, as used by
`import all` importers. -/
private theorem constantSection_principal_quotient (S : Scheme.{t})
    {R T : Type (t + 1)} [CommRing R] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace T] [IsTopologicalRing R] [IsTopologicalRing T]
    [DiscreteTopology R] [DiscreteTopology T]
    (f : R →+* T) (a : R) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {a}) (U : S.ProEtᵒᵖ) :
    let F := constantSheaf (ProEt.topology S) CommRingCat.{t + 1}
    let q := ((F.map (CommRingCat.ofHom f)).hom.app U).hom
    let c := (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).app U a
    Function.Surjective q ∧ ∀ s, q s = 0 ↔ ∃ t, c * t = s :=
  constantSection_principal_quotientOfUniverses.{t, t} S f a hs hk U

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem completion_factor_eval {A : Type v} [CommRing A]
    (I : Ideal A) {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn s

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def quotientFromKernel {A B : Type v} [CommRing A] [Ring B]
    (f : A →+* B) (I : Ideal A) (hs : Function.Surjective f) (hk : RingHom.ker f = I) :
    A ⧸ I ≃+* B :=
  (Ideal.quotEquivOfEq hk.symm).trans (f.quotientKerEquivOfSurjective hs)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem quotientFromKernel_mk {A B : Type v} [CommRing A] [Ring B]
    (f : A →+* B) (I : Ideal A) (hs : Function.Surjective f) (hk : RingHom.ker f = I)
    (a : A) : quotientFromKernel f I hs hk (Ideal.Quotient.mk I a) = f a := by
  simp [quotientFromKernel]

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The positive quotient tower has the usual algebraic completion as its limit.
Insert the unique zero-th coordinate to recover Mathlib's compatible-sequence model. -/
private theorem completion_positive_cone {A : Type v} [CommRing A]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ RingCat.{v})
    (q : (Functor.const ℕᵒᵖ).obj (RingCat.of A) ⟶ F)
    (hs : ∀ n : ℕ, Function.Surjective (q.app (op n)))
    (hk : ∀ n : ℕ, RingHom.ker (q.app (op n)).hom = I ^ (n + 1)) :
    ∃ π : (Functor.const ℕᵒᵖ).obj (RingCat.of (AdicCompletion I A)) ⟶ F,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Cone.mk _ π)) ∧
      ∀ (n : ℕ) (x : AdicCompletion I A), π.app (op n) x =
        quotientFromKernel (A := A) (q.app (op n)).hom (I ^ (n + 1)) (hs n) (hk n)
          (AdicCompletion.evalₐ I (n + 1) x) := by
  classical
  let e (n : ℕ) : A ⧸ I ^ (n + 1) ≃+* F.obj (op n) :=
    quotientFromKernel (A := A) (q.app (op n)).hom (I ^ (n + 1)) (hs n) (hk n)
  have he (n : ℕ) (a : A) : e n (Ideal.Quotient.mk _ a) = q.app (op n) a :=
    quotientFromKernel_mk (A := A) _ _ _ _ a
  have hetrans {m n : ℕ} (h : m ≤ n) (z : A ⧸ I ^ (n + 1)) :
      F.map (homOfLE h).op (e n z) =
        e m (Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1) z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.factor_mk, he, he]
    exact (ConcreteCategory.congr_hom (q.naturality (homOfLE h).op) a).symm
  let c : CategoryTheory.Limits.Cone F :=
    { pt := RingCat.of (AdicCompletion I A)
      π :=
        { app := fun n ↦ RingCat.ofHom
            ((e n.unop).toRingHom.comp (AdicCompletion.evalₐ I (n.unop + 1)).toRingHom)
          naturality := fun n m f ↦ by
            apply RingCat.hom_ext
            apply RingHom.ext
            intro x
            dsimp only [Functor.const_obj_map, Category.id_comp]
            change e m.unop (AdicCompletion.evalₐ I (m.unop + 1) x) =
              F.map f (e n.unop (AdicCompletion.evalₐ I (n.unop + 1) x))
            rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _,
              hetrans, completion_factor_eval] } }
  refine ⟨c.π, ?_, ?_⟩
  · let : CategoryTheory.Limits.ReflectsLimitsOfShape ℕᵒᵖ
        (CategoryTheory.forget RingCat.{v}) :=
      CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms
    refine ⟨CategoryTheory.Limits.isLimitOfReflects (CategoryTheory.forget RingCat.{v})
      (Classical.choice ((CategoryTheory.Limits.Types.isLimit_iff _).mpr ?_))⟩
    intro s hs'
    change ∀ ⦃i j⦄ (f : i ⟶ j), F.map f (s i) = s j at hs'
    let z : ∀ n : ℕ, A ⧸ I ^ (n + 1) := fun n ↦ (e n).symm (s (op n))
    have hz {m n : ℕ} (h : m ≤ n) :
        Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1) (z n) = z m := by
      apply (e m).injective
      rw [← hetrans h]
      simpa only [z, RingEquiv.apply_symm_apply] using hs' (homOfLE h).op
    let f : ∀ n : ℕ, A ⧸ I ^ n := fun n ↦ match n with
      | 0 => 0
      | n + 1 => z n
    have hf {m n : ℕ} (h : m ≤ n) : Ideal.Quotient.factorPow I h (f n) = f m := by
      cases m with
      | zero =>
        have : Subsingleton (A ⧸ I ^ 0) := by
          rw [pow_zero, Ideal.one_eq_top]
          infer_instance
        exact Subsingleton.elim _ _
      | succ m =>
        cases n with
        | zero => omega
        | succ n => exact hz (Nat.le_of_succ_le_succ h)
    let t : AdicCompletion I A :=
      ⟨fun n ↦ Ideal.Quotient.factor (by simp : I ^ n ≤ I ^ n • ⊤) (f n), by
        intro m n h
        change Submodule.factorPow I A h _ = _
        have hh := congrArg
          (Ideal.Quotient.factor (by simp : I ^ m ≤ I ^ m • ⊤)) (hf h)
        have hchange (z : A ⧸ I ^ n) :
            Submodule.factorPow I A h
                (Ideal.Quotient.factor (by simp : I ^ n ≤ I ^ n • ⊤) z) =
              Ideal.Quotient.factor (by simp : I ^ m ≤ I ^ m • ⊤)
                (Ideal.Quotient.factorPow I h z) := by
          induction z using Submodule.Quotient.induction_on
          rfl
        exact (hchange (f n)).trans hh⟩
    have ht (n : ℕ) : AdicCompletion.evalₐ I n t = f n := by
      simp only [AdicCompletion.evalₐ, AlgHom.comp_apply,
        Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ]
      change Ideal.Quotient.factor (by simp : I ^ n • ⊤ ≤ I ^ n)
        (Ideal.Quotient.factor (by simp : I ^ n ≤ I ^ n • ⊤) (f n)) = f n
      induction f n using Submodule.Quotient.induction_on
      rfl
    refine ⟨t, ?_, ?_⟩
    · intro n
      change e n.unop (AdicCompletion.evalₐ I (n.unop + 1) t) = s n
      rw [ht]
      exact (e n.unop).apply_symm_apply _
    · intro t' ht'
      apply AdicCompletion.ext_evalₐ
      intro n
      cases n with
      | zero =>
        have : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
        exact Subsingleton.elim _ _
      | succ n =>
        rw [ht]
        apply (e n).injective
        have hn := ht' (op n)
        change e n (AdicCompletion.evalₐ I (n + 1) t') = s (op n) at hn
        simpa only [f, z, RingEquiv.apply_symm_apply] using hn
  · intro n x
    rfl

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem constantSection_power_kernel (S : Scheme.{t})
    {R T : Type (max u (t + 1))} [CommRing R] [CommRing T]
    (f : R →+* T) (l n : ℕ) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {(l : R) ^ n}) (U : S.ProEtᵒᵖ) :
    let F := constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}
    let q := ((F.map (CommRingCat.ofHom f)).hom.app U).hom
    Function.Surjective q ∧
      RingHom.ker q = (Ideal.span {(l : (F.obj (CommRingCat.of R)).obj.obj U)}) ^ n := by
  let : TopologicalSpace R := ⊥
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : DiscreteTopology T := ⟨rfl⟩
  obtain ⟨hs', hk'⟩ := constantSection_principal_quotientOfUniverses S f ((l : R) ^ n) hs hk U
  refine ⟨hs', ?_⟩
  ext s
  rw [RingHom.mem_ker, hk', Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simp only [map_pow, map_natCast]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩, fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem completion_positive_iso {A : Type v} [CommRing A]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ RingCat.{v})
    (c : CategoryTheory.Limits.Cone F) (hc : CategoryTheory.Limits.IsLimit c)
    (q : (Functor.const ℕᵒᵖ).obj (RingCat.of A) ⟶ F)
    (hs : ∀ n : ℕ, Function.Surjective (q.app (op n)))
    (hk : ∀ n : ℕ, RingHom.ker (q.app (op n)).hom = I ^ (n + 1)) :
    ∃ e : AdicCompletion I A ≃+* c.pt,
      ∀ (n : ℕ) (x : AdicCompletion I A), c.π.app (op n) (e x) =
        quotientFromKernel (A := A) (q.app (op n)).hom (I ^ (n + 1)) (hs n) (hk n)
          (AdicCompletion.evalₐ I (n + 1) x) := by
  obtain ⟨π, ⟨hπ⟩, hnorm⟩ := completion_positive_cone I F q hs hk
  let i := hπ.conePointUniqueUpToIso hc
  refine ⟨i.ringCatIsoToRingEquiv, ?_⟩
  intro n x
  exact (ConcreteCategory.congr_hom (hπ.conePointUniqueUpToIso_hom_comp hc (op n)) x).trans
    (hnorm n x)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem lifted_power_kernel {R T : Type v} [CommRing R] [CommRing T]
    (f : R →+* T) (l n : ℕ) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {(l : R) ^ n}) :
    let g : ULift.{w} R →+* ULift.{w} T :=
      ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)
    Function.Surjective g ∧ RingHom.ker g = Ideal.span {(l : ULift.{w} R) ^ n} := by
  dsimp only
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hs y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  · ext x
    rw [RingHom.mem_ker]
    change ULift.up (f x.down) = ULift.up (0 : T) ↔
      x ∈ Ideal.span {(l : ULift.{w} R) ^ n}
    rw [ULift.up_inj]
    have hh : f x.down = 0 ↔ x.down ∈ Ideal.span {(l : R) ^ n} := by
      change x.down ∈ RingHom.ker f ↔ _
      rw [hk]
    rw [hh, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨ULift.up y, ULift.ext hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.down, congrArg ULift.down hy⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem completion_positive_iso_normalized {A : Type v} [CommRing A]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ RingCat.{v})
    (c : CategoryTheory.Limits.Cone F) (hc : CategoryTheory.Limits.IsLimit c)
    (q : (Functor.const ℕᵒᵖ).obj (RingCat.of A) ⟶ F)
    (hs : ∀ n : ℕ, Function.Surjective (q.app (op n)))
    (hk : ∀ n : ℕ, RingHom.ker (q.app (op n)).hom = I ^ (n + 1)) :
    ∃ e : AdicCompletion I A ≃+* c.pt,
      ∀ n : ℕ, ∃ r : A ⧸ I ^ (n + 1) ≃+* F.obj (op n),
        (∀ a : A, r (Ideal.Quotient.mk _ a) = q.app (op n) a) ∧
        ∀ x, c.π.app (op n) (e x) = r (AdicCompletion.evalₐ I (n + 1) x) := by
  obtain ⟨e, he⟩ := completion_positive_iso I F c hc q hs hk
  exact ⟨e, fun n ↦ ⟨quotientFromKernel (A := A) _ _ (hs n) (hk n),
    quotientFromKernel_mk (A := A) _ _ _ _, he n⟩⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Quotients commute with sections of constant rings, so the recorded sheaf limit
is the algebraic completion of its actual constant-section ring. -/
private theorem zl_section_completion (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEtᵒᵖ) :
    let A := (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U
    let I : Ideal A := Ideal.span {(l : A)}
    ∃ e : AdicCompletion I A ≃+* (purTwistZlCompletionOfUniverses.{t, u} S l).obj.obj U,
      (∀ a : A, e (AdicCompletion.of I A a) =
        (purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U a) ∧
      ∀ n : ℕ, ∃ r : A ⧸ I ^ (n + 1) ≃+* (purTwistFiniteRingOfUniverses.{t, u} S l n).obj.obj U,
        (∀ a : A, r (Ideal.Quotient.mk _ a) =
          (purTwistZlReductionOfUniverses.{t, u} S l n).hom.app U a) ∧
        ∀ x, (purTwistZlProjectionOfUniverses.{t, u} S l n).hom.app U (e x) =
          r (AdicCompletion.evalₐ I (n + 1) x) := by
  let A := (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U
  let I : Ideal A := Ideal.span {(l : A)}
  let ev := sheafToPresheaf (ProEt.topology S) CommRingCat.{max u (t + 1)} ⋙
    (CategoryTheory.evaluation _ _).obj U ⋙ forget₂ CommRingCat RingCat
  let D := purTwistZlTowerOfUniverses.{t, u} S l ⋙ ev
  let c := ev.mapCone (CategoryTheory.Limits.limit.cone (purTwistZlTowerOfUniverses.{t, u} S l))
  have hc : CategoryTheory.Limits.IsLimit c :=
    CategoryTheory.Limits.isLimitOfPreserves ev (CategoryTheory.Limits.limit.isLimit _)
  let q : (Functor.const ℕᵒᵖ).obj (RingCat.of A) ⟶ D :=
    (Functor.const ℕᵒᵖ).map (ev.map (purTwistZlCompletionMapOfUniverses.{t, u} S l)) ≫ c.π
  have hq (n : ℕ) : (q.app (op n)).hom =
      ((purTwistZlReductionOfUniverses.{t, u} S l n).hom.app U).hom := by
    exact congrArg (fun g ↦ (g.hom.app U).hom)
      ((purTwistZlCompletionMap_existsUniqueOfUniverses.{t, u} S l).exists.choose_spec n)
  have hdata (n : ℕ) : Function.Surjective (q.app (op n)) ∧
      RingHom.ker (q.app (op n)).hom = I ^ (n + 1) := by
    change Function.Surjective (q.app (op n)).hom ∧ _
    rw [hq]
    obtain ⟨hs, hk⟩ := lifted_power_kernel.{0, max u (t + 1)}
      (PadicInt.toZModPow (p := l) (n + 1)) l (n + 1)
      (ZMod.ringHom_surjective _) (PadicInt.ker_toZModPow (n + 1))
    exact constantSection_power_kernel.{t, u} S _ l (n + 1) hs hk U
  obtain ⟨e, he⟩ := completion_positive_iso_normalized I D c hc q
    (fun n ↦ (hdata n).1) (fun n ↦ (hdata n).2)
  refine ⟨e, ?_, ?_⟩
  · intro a
    apply Concrete.isLimit_ext D hc
    intro n
    obtain ⟨r, hr, hp⟩ := he n.unop
    change c.π.app n (e (AdicCompletion.of I A a)) =
      c.π.app n ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U a)
    rw [hp, AdicCompletion.evalₐ_of, hr]
    rfl
  · intro n
    obtain ⟨r, hr, hp⟩ := he n
    refine ⟨r, ?_, hp⟩
    intro a
    change r (Ideal.Quotient.mk (I ^ (n + 1)) a) = _
    exact (hr a).trans (RingHom.congr_fun (hq n) a)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- On the cofinal exponents e(n+1), uniformizer quotients are l-power quotients.
Evaluate the recorded limit and identify it with the completion of constant sections. -/
private theorem integral_section_completion (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (e : ℕ) (he : 0 < e)
    (hpow : ∀ r : ℕ, Padic.coefficientExtensionIdeal l E (e * r) =
      (Ideal.span {(l : Padic.coefficientExtensionIntegers l E)}) ^ r)
    (U : S.ProEtᵒᵖ) :
    let B := (purTwistIntegralConstant S l E).obj.obj U
    let J : Ideal B := Ideal.span {(l : B)}
    ∃ i : AdicCompletion J B ≃+*
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U,
      (∀ b : B, i (AdicCompletion.of J B b) =
        (purTwistIntegralCompletionMap S l E).hom.app U b) ∧
      ∀ n : ℕ, ∃ r : B ⧸ J ^ (n + 1) ≃+*
          (WeilConjectures.integralCoefficientCommRingSheaf l E S
            (e * (n + 1) - 1)).obj.obj U,
        (∀ b : B, r (Ideal.Quotient.mk _ b) =
          (purTwistIntegralQuotient S l E (e * (n + 1) - 1)).hom.app U b) ∧
        ∀ x, (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S
          (e * (n + 1) - 1)).hom.app U (i x) =
            r (AdicCompletion.evalₐ J (n + 1) x) := by
  let B := (purTwistIntegralConstant S l E).obj.obj U
  let J : Ideal B := Ideal.span {(l : B)}
  let f : ℕ →o ℕ :=
    ⟨fun n ↦ e * (n + 1) - 1, fun _ _ h ↦
      Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1⟩
  have hf (n : ℕ) : f n + 1 = e * (n + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n))
  have : f.monotone.functor.Final := f.monotone.final_functor_iff.mpr fun n ↦
    ⟨n, by
      change n ≤ e * (n + 1) - 1
      have h := Nat.le_mul_of_pos_left (n + 1) he
      omega⟩
  let ev := sheafToPresheaf (ProEt.topology S) RingCat.{max u (t + 1)} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let evc := sheafToPresheaf (ProEt.topology S) CommRingCat.{max u (t + 1)} ⋙
    (CategoryTheory.evaluation _ _).obj U ⋙ forget₂ CommRingCat RingCat
  let D0 := WeilConjectures.integralCoefficientSheafSystem l E S ⋙ ev
  let c0 := ev.mapCone (limit.cone (WeilConjectures.integralCoefficientSheafSystem l E S))
  have hc0 : IsLimit c0 := isLimitOfPreserves ev (limit.isLimit _)
  let D := f.monotone.functor.op ⋙ D0
  let c := c0.whisker f.monotone.functor.op
  have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv _ c0).symm hc0
  let q : (Functor.const ℕᵒᵖ).obj (RingCat.of B) ⟶ D :=
    (Functor.const ℕᵒᵖ).map (evc.map (purTwistIntegralCompletionMap S l E)) ≫ c.π
  have hq (n : ℕ) : (q.app (op n)).hom =
      ((purTwistIntegralQuotient S l E (f n)).hom.app U).hom := by
    exact congrArg (fun g ↦ (g.hom.app U).hom)
      ((purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec (f n))
  have hdata (n : ℕ) : Function.Surjective (q.app (op n)) ∧
      RingHom.ker (q.app (op n)).hom = J ^ (n + 1) := by
    change Function.Surjective (q.app (op n)).hom ∧ _
    rw [hq]
    let K := Padic.coefficientExtensionIdeal l E (f n + 1)
    have hK : RingHom.ker (Ideal.Quotient.mk K) =
        Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)} := by
      have hker : RingHom.ker (Ideal.Quotient.mk K) = K := by
        ext x
        exact Ideal.Quotient.eq_zero_iff_mem
      rw [hker]
      dsimp only [K]
      rw [hf, hpow, Ideal.span_singleton_pow]
    obtain ⟨hs, hk⟩ := lifted_power_kernel.{u, t + 1}
      (Ideal.Quotient.mk K) l (n + 1) Ideal.Quotient.mk_surjective hK
    exact constantSection_power_kernel.{t, u} S _ l (n + 1) hs hk U
  obtain ⟨i, hi⟩ := completion_positive_iso_normalized J D c hc q
    (fun n ↦ (hdata n).1) (fun n ↦ (hdata n).2)
  refine ⟨i, ?_, ?_⟩
  · intro b
    apply Concrete.isLimit_ext D hc
    intro n
    obtain ⟨r, hr, hp⟩ := hi n.unop
    change c.π.app n (i (AdicCompletion.of J B b)) =
      c.π.app n ((purTwistIntegralCompletionMap S l E).hom.app U b)
    rw [hp, AdicCompletion.evalₐ_of, hr]
    rfl
  · intro n
    obtain ⟨r, hr, hp⟩ := hi n
    refine ⟨r, ?_, hp⟩
    intro b
    change r (Ideal.Quotient.mk (J ^ (n + 1)) b) = _
    exact (hr b).trans (RingHom.congr_fun (hq n) b)

/- The quotient and scalar-restriction constructions in this section follow the
proved private helpers of WeilConjectures.RingTheory.CompletionFiniteExtensionTensorBijective.
They preserve the actual quotient projections and the completed scalar action. -/
section CompletionScalarTransport

open AdicCompletion in
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private def completionQuotientEquiv
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    (B ⧸ (I ^ n • ⊤ : Submodule A B)) ≃ₗ[A]
      B ⧸ ((I.map (algebraMap A B)) ^ n • ⊤ : Ideal B) :=
  (Submodule.quotEquivOfEq _ _ (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, Ideal.smul_top_eq_map])).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

open AdicCompletion in
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem completionQuotientEquiv_mk
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (b : B) :
    completionQuotientEquiv A B I n (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk b := by
  simp [completionQuotientEquiv]
  rfl

open AdicCompletion in
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem completionQuotientEquiv_transition
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {i j : ℕ} (h : i ≤ j)
    (x : B ⧸ (I ^ j • ⊤ : Submodule A B)) :
    transitionMap (I.map (algebraMap A B)) B h (completionQuotientEquiv A B I j x) =
      completionQuotientEquiv A B I i (transitionMap I B h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ b => simp only [completionQuotientEquiv_mk]; rfl

open AdicCompletion in
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private def mapCompletionEquiv
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : AdicCompletion I B ≃ₗ[A] AdicCompletion (I.map (algebraMap A B)) B where
  toFun x := ⟨fun n ↦ completionQuotientEquiv A B I n (x.val n), by
    intro i j h
    rw [completionQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n ↦ (completionQuotientEquiv A B I n).symm (x.val n), by
    intro i j h
    apply (completionQuotientEquiv A B I i).injective
    rw [← completionQuotientEquiv_transition]
    simp only [LinearEquiv.apply_symm_apply, x.property h]⟩
  left_inv x := by ext n; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by ext n; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' a x := by
    ext n
    exact (completionQuotientEquiv A B I n).map_smul a (x.val n)

open AdicCompletion in
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem mapCompletionEquiv_eval_smul_of
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (c : AdicCompletion I A) (b : B) :
    evalₐ (I.map (algebraMap A B)) n (mapCompletionEquiv A B I (c • of I B b)) =
      Ideal.quotientMapₐ ((I.map (algebraMap A B)) ^ n) (Algebra.ofId A B)
        (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
        (evalₐ I n c) * Ideal.Quotient.mk _ b := by
  change (Ideal.quotientEquivAlgOfEq B (by simp)) (completionQuotientEquiv A B I n
      ((c • of I B b).val n)) =
    Ideal.quotientMapₐ _ (Algebra.ofId A B)
      (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
      ((Ideal.quotientEquivAlgOfEq A (by simp)) (c.val n)) * Ideal.Quotient.mk _ b
  rw [smul_eval, of_apply]
  generalize c.val n = z
  induction z using Submodule.Quotient.induction_on with
  | _ a =>
    change (Ideal.quotientEquivAlgOfEq B (by simp)) (completionQuotientEquiv A B I n
      (Submodule.Quotient.mk (a • b))) = _
    rw [completionQuotientEquiv_mk]
    simp [Algebra.smul_def]
    congr 1

end CompletionScalarTransport

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a finite free `A`-algebra `B`, a ring map `B ⊗[A] R →+* T` compatible with the
given models `R` of the `I`-adic completion of `A` and `T` of that of `B` is bijective. -/
private theorem tensor_completion_comparison
    {A B R T : Type v} [CommRing A] [CommRing B] [CommRing R] [CommRing T]
    [Algebra A B] [Algebra A R] [Module.Free A B] [Module.Finite A B]
    (I : Ideal A) (c : R →+* T) (d : B →+* T)
    (hsquare : c.comp (algebraMap A R) = d.comp (algebraMap A B))
    (eA : AdicCompletion I A ≃ₐ[A] R)
    (eB : AdicCompletion (I.map (algebraMap A B)) B ≃+* T)
    (heB : ∀ b, eB (AdicCompletion.of _ B b) = d b)
    (Q P : ℕ → CommRingCat.{v})
    (pA : ∀ n, R →+* Q n) (pB : ∀ n, T →+* P n)
    (rA : ∀ n, A ⧸ I ^ (n + 1) ≃+* Q n)
    (rB : ∀ n, B ⧸ (I.map (algebraMap A B)) ^ (n + 1) ≃+* P n)
    (hpA : ∀ n x, pA n (eA x) = rA n (AdicCompletion.evalₐ I (n + 1) x))
    (hpB : ∀ n x, pB n (eB x) =
      rB n (AdicCompletion.evalₐ (I.map (algebraMap A B)) (n + 1) x))
    (hsep : ∀ x y : T, (∀ n, pB n x = pB n y) → x = y)
    (hfinite : ∀ n, ∃ (k : ℕ) (q : Q k →+* P n), (pB n).comp c = q.comp (pA k))
    (f : B ⊗[A] R →+* T) (hf : ∀ b r, f (b ⊗ₜ[A] r) = d b * c r) :
    Function.Bijective f := by
  classical
  let t := (TensorProduct.comm A B R).trans
    (TensorProduct.congr eA.symm.toLinearEquiv (LinearEquiv.refl A B))
  let ec := mapCompletionEquiv A B I
  let g : B ⊗[A] R → T := fun x ↦ eB (ec (AdicCompletion.ofTensorProduct I B (t x)))
  have hg : Function.Bijective g :=
    eB.bijective.comp (ec.bijective.comp ((finiteFreeCompletionTensor I B).comp t.bijective))
  have heA (a : A) : eA (AdicCompletion.of I A a) = algebraMap A R a := eA.commutes a
  have hmap (b : B) (r : R) : f (b ⊗ₜ[A] r) = g (b ⊗ₜ[A] r) := by
    rw [hf]
    change d b * c r = eB (ec (eA.symm r • AdicCompletion.of I B b))
    apply hsep
    intro n
    obtain ⟨k, q, hq⟩ := hfinite n
    let z := eA.symm r
    let m := max (k + 1) (n + 1)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I m z)
    have hrep (j : ℕ) (hj : j ≤ m) :
        AdicCompletion.evalₐ I j z = Ideal.Quotient.mk (I ^ j) a := by
      rw [← completion_factor_eval I hj z, ← ha]
      rfl
    have hpa : pA k r = pA k (algebraMap A R a) := by
      calc
        _ = rA k (AdicCompletion.evalₐ I (k + 1) z) := by
          rw [← hpA]
          exact congrArg (pA k) (eA.apply_symm_apply r).symm
        _ = rA k (Ideal.Quotient.mk _ a) := congrArg (rA k) (hrep _ (le_max_left _ _))
        _ = pA k (algebraMap A R a) := by rw [← AdicCompletion.evalₐ_of, ← hpA, heA]
    have hcr : pB n (c r) = pB n (d (algebraMap A B a)) := by
      calc
        _ = q (pA k r) := RingHom.congr_fun hq r
        _ = q (pA k (algebraMap A R a)) := congrArg q hpa
        _ = pB n (c (algebraMap A R a)) := (RingHom.congr_fun hq _).symm
        _ = _ := congrArg (pB n) (RingHom.congr_fun hsquare a)
    have hright : pB n (eB (ec (z • AdicCompletion.of I B b))) =
        pB n (d (algebraMap A B a * b)) := by
      rw [hpB]
      change rB n (AdicCompletion.evalₐ _ (n + 1)
        (mapCompletionEquiv A B I (z • AdicCompletion.of I B b))) = _
      rw [mapCompletionEquiv_eval_smul_of, hrep _ (le_max_right _ _)]
      change rB n (Ideal.Quotient.mk _ (algebraMap A B a) * Ideal.Quotient.mk _ b) = _
      rw [← map_mul]
      rw [← AdicCompletion.evalₐ_of, ← hpB, heB]
    rw [map_mul, hcr, ← map_mul, ← map_mul, mul_comm b]
    exact hright.symm
  have hfg : (f : B ⊗[A] R → T) = g := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul b r => exact hmap b r
    | add x y hx hy => simp only [map_add, hx, hy, g]
  exact hfg ▸ hg

/-- The canonical balanced coefficient map, constructed from the two actual scalar
inclusions. Its pure-tensor formula is definitional. -/
noncomputable def purTwistCoefficientTensorMap (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) :
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U).hom.toAlgebra
    ((purTwistIntegralConstant S l E).obj.obj U ⊗[
        (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U]
          (purTwistZlCompletionOfUniverses.{t, u} S l).obj.obj U) →+*
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
  let a := ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U).hom
  let b := ((purTwistConstantIntegersMap S l E).hom.app U).hom
  let c := ((purTwistCompletedScalarMap S l E).hom.app U).hom
  let d := ((purTwistIntegralCompletionMap S l E).hom.app U).hom
  letI := b.toAlgebra
  letI := a.toAlgebra
  letI := (c.comp a).toAlgebra
  let f : (purTwistIntegralConstant S l E).obj.obj U →ₐ[
      (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U]
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
    { __ := d
      commutes' := fun z ↦ (ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.hom.app U) (purTwistCoefficientSquare S l E)) z).symm }
  let g : (purTwistZlCompletionOfUniverses.{t, u} S l).obj.obj U →ₐ[
      (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U]
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
    { __ := c
      commutes' := fun _ ↦ rfl }
  (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in

/-- Completion of the finite integral extension is the sectionwise scalar tensor. -/
theorem purTwistCoefficientTensor (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) :
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U).hom.toAlgebra
    Function.Bijective (purTwistCoefficientTensorMap S l E U) := by
  classical
  let A := (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U
  let B := (purTwistIntegralConstant S l E).obj.obj U
  let R := (purTwistZlCompletionOfUniverses.{t, u} S l).obj.obj U
  let T := (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U
  let a : A →+* R := ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U).hom
  let b : A →+* B := ((purTwistConstantIntegersMap S l E).hom.app U).hom
  let c : R →+* T := ((purTwistCompletedScalarMap S l E).hom.app U).hom
  let d : B →+* T := ((purTwistIntegralCompletionMap S l E).hom.app U).hom
  let := b.toAlgebra
  let := a.toAlgebra
  let I : Ideal A := Ideal.span {(l : A)}
  obtain ⟨rank, basis, _⟩ := coefficient_section_basis S l E
  let : Module.Free A B := Module.Free.of_basis (basis U)
  let : Module.Finite A B := Module.Finite.of_basis (basis U)
  obtain ⟨eA0, heA0, hA⟩ := zl_section_completion S l U
  let eA : AdicCompletion I A ≃ₐ[A] R :=
    { __ := eA0
      commutes' := heA0 }
  choose rA hrA hpA using hA
  obtain ⟨e, he, hpow, _⟩ := coefficient_filtrations l E
  have hpow' (n : ℕ) : Padic.coefficientExtensionIdeal l E (e * n) =
      (Ideal.span {(l : Padic.coefficientExtensionIntegers l E)}) ^ n :=
    (hpow n).symm
  have hJ : (Ideal.span {(l : B)}) = I.map (algebraMap A B) := by
    simp only [I, Ideal.map_span, Set.image_singleton, map_natCast]
  have hB := integral_section_completion S l E e he hpow' U
  dsimp only at hB
  rw [hJ] at hB
  obtain ⟨eB, heB, hB⟩ := hB
  choose rB hrB hpB using hB
  let Q (n : ℕ) : CommRingCat.{max u (t + 1)} :=
    (purTwistFiniteRingOfUniverses.{t, u} S l n).obj.obj U
  let P (n : ℕ) : CommRingCat.{max u (t + 1)} :=
    (WeilConjectures.integralCoefficientCommRingSheaf l E S (e * (n + 1) - 1)).obj.obj U
  let pA (n : ℕ) : R →+* Q n := ((purTwistZlProjectionOfUniverses.{t, u} S l n).hom.app U).hom
  let pB (n : ℕ) : T →+* P n :=
    ((WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S
      (e * (n + 1) - 1)).hom.app U).hom
  have hsquare : c.comp (algebraMap A R) = d.comp (algebraMap A B) :=
    congrArg (fun g ↦ (g.hom.app U).hom) (purTwistCoefficientSquare S l E)
  have hsep : ∀ x y : T, (∀ n, pB n x = pB n y) → x = y := by
    intro x y h
    apply eB.symm.injective
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
      have : Subsingleton (B ⧸ (I.map (algebraMap A B)) ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      exact Subsingleton.elim _ _
    | succ n =>
      apply (rB n).injective
      rw [← hpB, ← hpB]
      simpa only [RingEquiv.apply_symm_apply] using h n
  have hfinite : ∀ n, ∃ (k : ℕ) (q : Q k →+* P n), (pB n).comp c = q.comp (pA k) := by
    intro n
    have hscalar := (purTwistCompletedScalarMap_existsUnique S l E).exists.choose_spec
    change IsPurTwistCompletedScalarMap S l E (purTwistCompletedScalarMap S l E) at hscalar
    obtain ⟨k, q, _, hq⟩ := hscalar (e * (n + 1) - 1)
    let qU : Q k →+* P n :=
      (((constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (q.comp ULift.ringEquiv.toRingHom)))).hom.app U).hom
    refine ⟨k, qU, ?_⟩
    exact congrArg (fun g ↦ (g.hom.app U).hom) hq
  exact tensor_completion_comparison I c d hsquare eA eB heB Q P pA pB rA rB hpA hpB
    hsep hfinite (purTwistCoefficientTensorMap S l E U) (fun _ _ ↦ rfl)

end AlgebraicGeometry.Scheme
