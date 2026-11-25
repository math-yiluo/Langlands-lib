/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Localization.Module
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.MonoidalFiniteFreeTransport
import all WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.FiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedSubfieldBasis
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Finite free integral and rational pro-etale coefficients

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-prop-sfb-cartesian-coefficients-finite-free.md
(blueprint: lemma-inverse-image-coefficient-sheaves).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The integral inclusion for finite subfields, using the existing integers map.
Source: blueprint finite-free coefficient detail, integral inclusion
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientIntegersMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicAlgCl.integers ℓ E.1 →+* PadicAlgCl.integers ℓ F.1 :=
  letI := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower E.1 F.1 (PadicAlgCl ℓ) :=
    Subalgebra.inclusion.isScalarTower_right
      (show E.1.toSubalgebra ≤ F.1.toSubalgebra from h) (PadicAlgCl ℓ)
  PadicAlgCl.integersMap ℓ E.1 F.1

/-- The degree of the indicated inclusion, with its actual scalar action.
Source: blueprint finite-free coefficient detail, d = [F:E]
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientDegree
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) : ℕ :=
  @Module.finrank E.1 F.1 inferInstance inferInstance
    (Module.compHom F.1 (IntermediateField.inclusion h).toRingHom)

/-- The type of integral bases for the actual inclusion of integer rings.
Source: blueprint finite-free coefficient detail, choice of b_1,...,b_d
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientIntegralBasis
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :=
  @Module.Basis (Fin (finiteCoefficientDegree ℓ h))
    (PadicAlgCl.integers ℓ E.1) (PadicAlgCl.integers ℓ F.1)
    inferInstance inferInstance
    (Module.compHom (PadicAlgCl.integers ℓ F.1) (finiteCoefficientIntegersMap ℓ h))

/-- The condensed integral inclusion, by postcomposition on continuous functions.
Source: blueprint finite-free coefficient detail, integral coefficient inclusion
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable def finiteCoefficientIntegersPointMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Profinite.padicIntegersRingObj ℓ F.1 :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))

/-- The integral coefficient inclusion is a ring-object map.
Source: blueprint finite-free coefficient detail, integral coefficient inclusion
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable instance isMonHom_finiteCoefficientIntegersPointMap
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (finiteCoefficientIntegersPointMap.{u} ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))))

/-- The basis summand on the point: postcompose a continuous function with a ↦ φ(a)t.
Source: blueprint finite-free coefficient detail, displayed sum formula
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable def finiteCoefficientPointSummand
    {R T : Type} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (φ : R →+* T) (hφ : Continuous φ) (t : T) :
    Profinite.continuousMapRingObj.{u} R ⟶ Profinite.continuousMapRingObj T :=
  ⟨{ app S := AddCommGrpCat.ofHom
        (ULift.ringEquiv.symm.toAddMonoidHom.comp
          ((((AddMonoidHom.mulRight t).comp φ.toAddMonoidHom).compLeftContinuous S.unop
            (hφ.mul_const t)).comp ULift.ringEquiv.toAddMonoidHom))
     naturality _ _ _ := rfl }⟩

/-- The integral summand on X, with exactly the multiplication-by-b formula.
Source: blueprint finite-free coefficient detail, apply p_X^*
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientIntegralSummand (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : PadicAlgCl.integers ℓ F.1) :=
  (upperStarFromPoint X).map (finiteCoefficientPointSummand
    (finiteCoefficientIntegersMap ℓ h)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _) b)

/-- The rational summand on X, using the same integral basis vector in F.
Source: blueprint finite-free coefficient detail, rational displayed sum formula
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientRationalSummand (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : PadicAlgCl.integers ℓ F.1) :=
  (upperStarFromPoint X).map (finiteCoefficientPointSummand
    (IntermediateField.inclusion h).toRingHom
    (continuous_subtype_val.subtype_mk _) (b : F.1))

/-- The i-th integral free-module summand, on underlying abelian sheaves.
Source: blueprint finite-free coefficient detail, integral direct power
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientIntegralLeg (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (i : Fin (finiteCoefficientDegree ℓ h)) :=
  (biproduct.ι (fun _ : Fin (finiteCoefficientDegree ℓ h) =>
    Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) i).hom

/-- The i-th rational free-module summand, on underlying abelian sheaves.
Source: blueprint finite-free coefficient detail, rational direct power
(blueprint: lemma-inverse-image-coefficient-sheaves). -/
noncomputable abbrev finiteCoefficientRationalLeg (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (i : Fin (finiteCoefficientDegree ℓ h)) :=
  (biproduct.ι (fun _ : Fin (finiteCoefficientDegree ℓ h) =>
    Mod.regular (padicSubfieldRingObj X ℓ E)) i).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem continuous_basis_iso
    {R S : Type} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [Algebra R S]
    (hι : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    ∃ e : Mod.finiteFree (Profinite.continuousMapRingObj.{u} R) n ≅
        (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap (algebraMap R S) hι))).obj
          (Mod.regular (Profinite.continuousMapRingObj S)),
      ∀ i, (biproduct.ι (fun _ : Fin n ↦
        Mod.regular (Profinite.continuousMapRingObj R)) i).hom ≫ e.hom.hom =
          finiteCoefficientPointSummand (algebraMap R S) hι (b i) := by
  classical
  let φ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (algebraMap R S) hι)
  let M := (Mod.comap φ).obj (Mod.regular (Profinite.continuousMapRingObj S))
  let N := Mod.regular (Profinite.continuousMapRingObj.{u} R)
  let q (i : Fin n) : M ⟶ N :=
    Mod.homMk (Profinite.continuousAddHom (b.coord i).toAddMonoidHom (hc i)) (by
      change (MonoidalCategory.whiskerRight φ (Profinite.continuousMapRingObj S) ≫
        (MonObj.mul (X := Profinite.continuousMapRingObj S))) ≫ _ =
          _ ≫ (MonObj.mul (X := Profinite.continuousMapRingObj R))
      simpa only [Profinite.coefficientMap_self, MonoidalCategory.id_whiskerRight,
        Category.id_comp, Category.assoc] using
        Profinite.continuousLinearAction R S R hι continuous_id (b.coord i) (hc i))
  have hv (i : Fin n) : Continuous (LinearMap.toSpanSingleton R S (b i)) := by
    change Continuous (fun a : R ↦ a • b i)
    simpa only [Algebra.smul_def] using hι.mul_const (b i)
  let v (i : Fin n) : N ⟶ M :=
    Mod.homMk (Profinite.continuousAddHom
      (LinearMap.toSpanSingleton R S (b i)).toAddMonoidHom (hv i)) (by
      change (MonObj.mul (X := Profinite.continuousMapRingObj R)) ≫ _ =
        _ ≫ MonoidalCategory.whiskerRight φ (Profinite.continuousMapRingObj S) ≫
          (MonObj.mul (X := Profinite.continuousMapRingObj S))
      simpa only [Profinite.coefficientMap_self, MonoidalCategory.id_whiskerRight,
        Category.id_comp, Category.assoc] using
        Profinite.continuousLinearAction R R S continuous_id hι
          (LinearMap.toSpanSingleton R S (b i)) (hv i))
  let e : M ≅ Mod.finiteFree (Profinite.continuousMapRingObj R) n :=
    { hom := biproduct.lift q
      inv := biproduct.desc v
      hom_inv_id := by
        rw [biproduct.lift_desc]
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        ext T a
        rw [Profinite.module_sum_app]
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        rw [Profinite.sum_down_apply]
        change (∑ i, b.coord i (a.down x) • b i) = a.down x
        exact b.sum_repr (a.down x)
      inv_hom_id := by
        apply biproduct.hom_ext'
        intro i
        apply biproduct.hom_ext
        intro j
        simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π,
          Category.id_comp]
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        ext T a
        by_cases h : i = j
        · subst j
          simp only [biproduct.ι_π_self]
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change b.coord i (a.down x • b i) = a.down x
          simp
        · simp only [biproduct.ι_π_ne _ h]
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change b.coord j (a.down x • b i) = 0
          simp [h] }
  refine ⟨e.symm, ?_⟩
  intro i
  change ((biproduct.ι (fun _ : Fin n ↦ N) i) ≫ biproduct.desc v).hom = _
  rw [biproduct.ι_desc]
  apply Sheaf.hom_ext
  ext T a
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact Algebra.smul_def _ _

private theorem pullback_basis_iso
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] (n : ℕ)
    (θ : Mod.finiteFree R n ≅ (Mod.comap φ).obj (Mod.regular S))
    (X : Scheme.{u}) :
    ∃ e : Mod.finiteFree (condensedRingObj R X) n ≅
        (Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj S X)),
      ∀ i : Fin n,
        (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj R X)) i).hom ≫
          e.hom.hom = (upperStarFromPoint X).map
            ((biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i).hom ≫ θ.hom.hom) := by
  let P := upperStarFromPoint X
  let : HasFiniteBiproducts (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasFiniteBiproducts (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasBinaryBiproducts (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    hasBinaryBiproducts_of_finite_biproducts _
  let : HasBinaryBiproducts (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : PreservesBinaryBiproducts P :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts P
  have : P.Additive := Functor.additive_of_preservesBinaryBiproducts P
  obtain ⟨α, hα, _⟩ := P.monoidalFiniteFreeTransport R _ n θ
  let es : (P.mapMod S).obj (Mod.regular S) ≅ Mod.regular (P.obj S) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id,
        MonoidalCategory.whiskerLeft_id, Category.id_comp])
  let k := (P.mapModComapIso φ).app (Mod.regular S) ≪≫
    (Mod.comap (P.map φ)).mapIso es
  refine ⟨α ≪≫ k, ?_⟩
  intro i
  change (biproduct.ι (fun _ : Fin n ↦ Mod.regular (P.obj R)) i).hom ≫
    α.hom.hom ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact hα i

private theorem integral_coordinates_continuous
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : finiteCoefficientIntegralBasis ℓ h) :
    letI := (finiteCoefficientIntegersMap ℓ h).toAlgebra
    ∀ i, Continuous (b.coord i) := by
  let : Algebra (PadicAlgCl.integers ℓ E.1) (PadicAlgCl.integers ℓ F.1) :=
    (finiteCoefficientIntegersMap ℓ h).toAlgebra
  have : CompactSpace (PadicAlgCl.integers ℓ E.1) :=
    PadicAlgCl.compactSpace_integers ℓ E.1
  have hc : Continuous (b.equivFun.symm :
      (Fin (finiteCoefficientDegree ℓ h) → PadicAlgCl.integers ℓ E.1) →
        PadicAlgCl.integers ℓ F.1) := by
    have heq : (b.equivFun.symm :
        (Fin (finiteCoefficientDegree ℓ h) → PadicAlgCl.integers ℓ E.1) →
          PadicAlgCl.integers ℓ F.1) = fun a ↦ ∑ i, a i • b i := by
      funext a
      exact b.equivFun_symm_apply a
    rw [heq]
    apply continuous_finsetSum
    intro i _
    change Continuous (fun a : Fin (finiteCoefficientDegree ℓ h) →
      PadicAlgCl.integers ℓ E.1 ↦ finiteCoefficientIntegersMap ℓ h (a i) * b i)
    have hmap : Continuous (finiteCoefficientIntegersMap ℓ h) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _
    exact (hmap.comp (continuous_apply i)).mul_const (b i)
  let e := b.equivFun.symm.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  intro i
  exact (continuous_apply i).comp e.symm.continuous

private theorem integral_basis_exists
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Nonempty (finiteCoefficientIntegralBasis ℓ h) := by
  classical
  let : Algebra E.1 F.1 := (IntermediateField.inclusion h).toAlgebra
  let : Module E.1 F.1 := Algebra.toModule
  let : IsScalarTower E.1 F.1 (PadicAlgCl ℓ) :=
    Subalgebra.inclusion.isScalarTower_right
      (show E.1.toSubalgebra ≤ F.1.toSubalgebra from h) (PadicAlgCl ℓ)
  let A := PadicAlgCl.integers ℓ E.1
  let B := PadicAlgCl.integers ℓ F.1
  let : Algebra A B := (PadicAlgCl.integersMap ℓ E.1 F.1).toAlgebra
  let : Module A B := Algebra.toModule
  let : Algebra A F.1 := ((algebraMap E.1 F.1).comp A.subtype).toAlgebra
  let : Module A F.1 := Algebra.toModule
  have : IsScalarTower A E.1 F.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B F.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite A B := PadicAlgCl.finite_integersMap ℓ E.1 F.1
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsIntegralClosure B A F.1 :=
    IsIntegralClosure.of_isIntegrallyClosed B A F.1
  have : IsScalarTower ℚ_[ℓ] E.1 F.1 :=
    PadicAlgCl.isScalarTower_of_algebra ℓ E.1 F.1
  have : FiniteDimensional E.1 F.1 := Module.Finite.right ℚ_[ℓ] E.1 F.1
  have : Module.IsTorsionFree A F.1 := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap E.1 F.1).injective.comp Subtype.val_injective
  have : Module.Free A B := IsIntegralClosure.module_free A E.1 F.1 B
  have hr : Module.finrank A B = finiteCoefficientDegree ℓ h :=
    IsIntegralClosure.rank A E.1 F.1 B
  exact ⟨Module.finBasisOfFinrankEq A B hr⟩

private theorem rational_basis
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : finiteCoefficientIntegralBasis ℓ h) :
    ∃ c : @Module.Basis (Fin (finiteCoefficientDegree ℓ h)) E.1 F.1
      inferInstance inferInstance
      (Module.compHom F.1 (IntermediateField.inclusion h).toRingHom),
      ∀ i, c i = (b i : F.1) := by
  classical
  let : Algebra E.1 F.1 := (IntermediateField.inclusion h).toAlgebra
  let : Module E.1 F.1 := Algebra.toModule
  let : IsScalarTower E.1 F.1 (PadicAlgCl ℓ) :=
    Subalgebra.inclusion.isScalarTower_right
      (show E.1.toSubalgebra ≤ F.1.toSubalgebra from h) (PadicAlgCl ℓ)
  let A := PadicAlgCl.integers ℓ E.1
  let B := PadicAlgCl.integers ℓ F.1
  let : Algebra A B := (finiteCoefficientIntegersMap ℓ h).toAlgebra
  let : Module A B := Algebra.toModule
  let : Algebra A F.1 := ((algebraMap E.1 F.1).comp A.subtype).toAlgebra
  let : Module A F.1 := Algebra.toModule
  have : IsScalarTower A E.1 F.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B F.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite A B := PadicAlgCl.finite_integersMap ℓ E.1 F.1
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsIntegralClosure B A F.1 :=
    IsIntegralClosure.of_isIntegrallyClosed B A F.1
  have : IsScalarTower ℚ_[ℓ] E.1 F.1 :=
    PadicAlgCl.isScalarTower_of_algebra ℓ E.1 F.1
  have : FiniteDimensional E.1 F.1 := Module.Finite.right ℚ_[ℓ] E.1 F.1
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) F.1 :=
    IsIntegralClosure.isLocalization A E.1 F.1 B
  exact ⟨b.localizationLocalization E.1 (nonZeroDivisors A) F.1,
    fun i ↦ b.localizationLocalization_apply E.1 (nonZeroDivisors A) F.1 i⟩

private theorem finite_free_flat
    (X : Scheme.{u}) (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (n : ℕ)
    (e : Mod.finiteFree R n ≅ (Mod.comap φ).obj (Mod.regular S)) :
    PreservesFiniteLimits (Mod.extendScalars φ) := by
  let α : Mod.extendScalars φ ⋙ Mod.comap φ ≅
      Functor.const (Discrete (Fin n)) ⋙ lim :=
    NatIso.ofComponents (Mod.finiteCoordinateIso e)
      (fun f ↦ Mod.finiteCoordinateIso_naturality e f)
  have : PreservesFiniteLimits (Mod.extendScalars φ ⋙ Mod.comap φ) :=
    preservesFiniteLimits_of_natIso α.symm
  have : PreservesFiniteLimits
      (Mod.forget R : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤ _) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (Mod.extendScalars φ ⋙ Mod.forget S) :=
    inferInstanceAs (PreservesFiniteLimits
      ((Mod.extendScalars φ ⋙ Mod.comap φ) ⋙ Mod.forget R))
  have : ReflectsFiniteLimits
      (Mod.forget S : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤ _) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves (Mod.extendScalars φ) (Mod.forget S)

attribute [local irreducible] upperStarFromPoint Mod.extendScalars

private theorem integral_sheaf_basis
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : finiteCoefficientIntegralBasis ℓ h) :
    ∃ e : ∀ X : Scheme.{u},
      Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
          (finiteCoefficientDegree ℓ h) ≅
        (Mod.comap (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)).obj
          (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)),
      ∀ X i, finiteCoefficientIntegralLeg ℓ X h i ≫ (e X).hom.hom =
        finiteCoefficientIntegralSummand ℓ X h (b i) := by
  classical
  let : Algebra (PadicAlgCl.integers ℓ E.1) (PadicAlgCl.integers ℓ F.1) :=
    (finiteCoefficientIntegersMap ℓ h).toAlgebra
  obtain ⟨θ, hθ⟩ := continuous_basis_iso
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _)
    (finiteCoefficientDegree ℓ h) b (integral_coordinates_continuous ℓ h b)
  have he (X : Scheme.{u}) := pullback_basis_iso
    (Profinite.padicIntegersRingObj ℓ E.1) (Profinite.padicIntegersRingObj ℓ F.1)
    (finiteCoefficientIntegersPointMap ℓ h) (finiteCoefficientDegree ℓ h) θ X
  refine ⟨fun X ↦ (he X).choose, ?_⟩
  intro X i
  exact ((he X).choose_spec i).trans
    (congrArg (upperStarFromPoint X).map (hθ i))

private theorem rational_sheaf_basis
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : finiteCoefficientIntegralBasis ℓ h) :
    ∃ e : ∀ X : Scheme.{u},
      Mod.finiteFree (padicSubfieldRingObj X ℓ E) (finiteCoefficientDegree ℓ h) ≅
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj X ℓ F)),
      ∀ X i, finiteCoefficientRationalLeg ℓ X h i ≫ (e X).hom.hom =
        finiteCoefficientRationalSummand ℓ X h (b i) := by
  classical
  let : Algebra E.1 F.1 := (IntermediateField.inclusion h).toAlgebra
  let : Module E.1 F.1 := Algebra.toModule
  have : IsScalarTower ℚ_[ℓ] E.1 F.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨c, hc⟩ := rational_basis ℓ h b
  have hcoord (i : Fin (finiteCoefficientDegree ℓ h)) : Continuous (c.coord i) :=
    ((c.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  obtain ⟨θ, hθ⟩ := continuous_basis_iso
    (continuous_subtype_val.subtype_mk _) _ c hcoord
  have he (X : Scheme.{u}) := pullback_basis_iso
    (Profinite.continuousMapRingObj E.1) (Profinite.continuousMapRingObj F.1)
    (Profinite.padicSubfieldRingObjMap ℓ h) (finiteCoefficientDegree ℓ h) θ X
  refine ⟨fun X ↦ (he X).choose, ?_⟩
  intro X i
  exact ((he X).choose_spec i).trans
    (congrArg (upperStarFromPoint X).map ((hθ i).trans (congrArg
      (finiteCoefficientPointSummand (algebraMap E.1 F.1)
        (continuous_subtype_val.subtype_mk _)) (hc i))))

private theorem integral_rational_summand_square
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (b : PadicAlgCl.integers ℓ F.1) (X : Scheme.{u}) :
    finiteCoefficientIntegralSummand ℓ X h b ≫ padicIntegersToPadicSubfield X ℓ F =
      padicIntegersToPadicSubfield X ℓ E ≫ finiteCoefficientRationalSummand ℓ X h b := by
  change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ =
    (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem point_summand_naturality
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[Ab.{u + 1}].map ((upperStarFromPoint Y).map a) ≫
        condensedPullbackHom S f =
      condensedPullbackHom R f ≫ (upperStarFromPoint X).map a :=
  (upperStarFromPointComp f).hom.naturality a

private theorem square_of_summand_formulas
    {C : Type*} [Category C] {A B D G H I : C}
    (l₀ : A ⟶ B) (e₀ : B ⟶ D) (l₁ : G ⟶ H)
    (e₁ : H ⟶ I) (v : D ⟶ I) (w : A ⟶ G)
    (a : A ⟶ D) (b : G ⟶ I)
    (h₀ : l₀ ≫ e₀ = a) (h₁ : l₁ ≫ e₁ = b) (h : a ≫ v = w ≫ b) :
    l₀ ≫ e₀ ≫ v = w ≫ l₁ ≫ e₁ := by
  rw [← Category.assoc l₀ e₀ v, h₀, h₁]
  exact h

private theorem point_basis_naturality
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : condensedRingObj R X ⟶ condensedRingObj S X)
    (gY : condensedRingObj R Y ⟶ condensedRingObj S Y)
    (hX : gX = (upperStarFromPoint X).map a)
    (hY : gY = (upperStarFromPoint Y).map a) :
    (f)^*[Ab.{u + 1}].map gY ≫ condensedPullbackHom S f =
      condensedPullbackHom R f ≫ gX := by
  rw [hX, hY]
  exact point_summand_naturality a f

/-- Integral and rational coefficient sheaves are finite free, by the specified basis maps.
All squares are stated on coproduct injections, which jointly determine the full square.

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-prop-sfb-cartesian-coefficients-finite-free.md
(blueprint: lemma-inverse-image-coefficient-sheaves).

Proof:
1. The integer rings are DVRs by lemma-inverse-image-coefficient-sheaves--3. The lower
   ring is a Noetherian normal PID by lemma-inverse-image-coefficient-sheaves--3. The upper
   ring is its integral closure by lemma-inverse-image-coefficient-sheaves--3.
   Characteristic zero gives separability; apply
   lemma-inverse-image-coefficient-sheaves--3 and then
   lemma-inverse-image-coefficient-sheaves--3 to get a finite integral basis.
2. Multiplying an element of F, or all coefficients in a relation, by a sufficiently
   large power of ell puts it in the integral ring. Thus this basis is an E-basis
   of F, and its rank is d. This also applies to every chosen integral basis.
3. The rational basis map is a homeomorphism by lemma-inverse-image-coefficient-sheaves--3
   and lemma-inverse-image-coefficient-sheaves--3. Restricting it to the
   integral lattices gives the integral homeomorphism, with the subspace topologies
   of prose-02-50.
4. Applying continuous functions on each profinite S gives mutually inverse linear
   maps; their formulas commute with precomposition (lemma-inverse-image-coefficient-sheaves--3).
5. Apply p_X^* (lemma-inverse-image-coefficient-sheaves--3). It preserves finite coproducts and
   transports module structures (lemma-inverse-image-coefficient-sheaves--3), giving the integral
   iso on the rings of lemma-inverse-image-coefficient-sheaves--3, with the specified summands.
6. Invert ell using lemma-comparison-completed-coefficients--2. Restriction of scalars
   preserves colimits by lemma-inverse-image-coefficient-sheaves--3. Finite sums commute with
   these colimits, so this gives the rational iso. The condensed inclusion square
   commutes sectionwise; applying p_X^* and the localization universal property
   identifies the rational action with prose-07-03. Term zero
   gives the square with lemma-comparison-completed-coefficients--2.
7. Naturality of lemma-inverse-image-coefficient-sheaves--3 on multiplication by each b_i
   gives both inverse-image squares with the lemma-inverse-image-coefficient-sheaves--3 maps.
8. The balanced coequalizer of lemma-inverse-image-coefficient-sheaves--3 identifies extension
   by either finite free ring with the d-fold sum of the underlying module:
   (sum a_i b_i) tensor m maps to (a_i m), with inverse sum b_i tensor m_i.
9. Finite limits of abelian sheaves and module objects are computed on underlying
   sheaves, and commute with finite powers. Thus both scalar extensions preserve
   finite limits, which is the asserted flatness (lemma-inverse-image-coefficient-sheaves--3).
-/
theorem cartesianCoefficients_finiteFree
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Nonempty (finiteCoefficientIntegralBasis ℓ h) ∧
    (∀ b : finiteCoefficientIntegralBasis ℓ h,
      ∃ e₀ : ∀ X : Scheme.{u},
        Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
            (finiteCoefficientDegree ℓ h) ≅
          (Mod.comap (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)).obj
            (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)),
      ∃ e₁ : ∀ X : Scheme.{u},
        Mod.finiteFree (padicSubfieldRingObj X ℓ E) (finiteCoefficientDegree ℓ h) ≅
          (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
            (Mod.regular (padicSubfieldRingObj X ℓ F)),
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom =
          finiteCoefficientIntegralSummand ℓ X h (b i)) ∧
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom =
          finiteCoefficientRationalSummand ℓ X h (b i)) ∧
      (∀ (X : Scheme.{u}) (i : Fin (finiteCoefficientDegree ℓ h)),
        finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom ≫
            padicIntegersToPadicSubfield X ℓ F =
          padicIntegersToPadicSubfield X ℓ E ≫
            finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (i : Fin (finiteCoefficientDegree ℓ h)),
        (f)^*[AddCommGrpCat.{u + 1}].map
            (finiteCoefficientIntegralLeg ℓ Y h i ≫ (e₀ Y).hom.hom) ≫
              condensedPullbackHom (Profinite.padicIntegersRingObj ℓ F.1) f =
          condensedPullbackHom (Profinite.padicIntegersRingObj ℓ E.1) f ≫
            finiteCoefficientIntegralLeg ℓ X h i ≫ (e₀ X).hom.hom) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (i : Fin (finiteCoefficientDegree ℓ h)),
        (f)^*[AddCommGrpCat.{u + 1}].map
            (finiteCoefficientRationalLeg ℓ Y h i ≫ (e₁ Y).hom.hom) ≫
              condensedPullbackHom (Profinite.continuousMapRingObj F.1) f =
          condensedPullbackHom (Profinite.continuousMapRingObj E.1) f ≫
            finiteCoefficientRationalLeg ℓ X h i ≫ (e₁ X).hom.hom)) ∧
    (∀ X : Scheme.{u},
      PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)) ∧
        PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))) := by
  classical
  refine ⟨integral_basis_exists ℓ h, ?_, ?_⟩
  · intro b
    refine (integral_sheaf_basis.{u} ℓ h b).elim fun e₀ h₀ ↦ ?_
    refine (rational_sheaf_basis.{u} ℓ h b).elim fun e₁ h₁ ↦ ?_
    refine ⟨e₀, e₁, h₀, h₁, ?_, ?_, ?_⟩
    · intro X i
      exact square_of_summand_formulas
        (finiteCoefficientIntegralLeg ℓ X h i) (e₀ X).hom.hom
        (finiteCoefficientRationalLeg ℓ X h i) (e₁ X).hom.hom
        (padicIntegersToPadicSubfield X ℓ F) (padicIntegersToPadicSubfield X ℓ E)
        (finiteCoefficientIntegralSummand ℓ X h (b i))
        (finiteCoefficientRationalSummand ℓ X h (b i)) (h₀ X i) (h₁ X i)
        (integral_rational_summand_square ℓ h (b i) X)
    · intro X Y f i
      exact point_basis_naturality
        (R := Profinite.padicIntegersRingObj ℓ E.1)
        (S := Profinite.padicIntegersRingObj ℓ F.1)
        (finiteCoefficientPointSummand (finiteCoefficientIntegersMap ℓ h)
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
            |>.subtype_mk _) (b i)) f _ _ (h₀ X i) (h₀ Y i)
    · intro X Y f i
      exact point_basis_naturality
        (R := Profinite.continuousMapRingObj E.1)
        (S := Profinite.continuousMapRingObj F.1)
        (finiteCoefficientPointSummand (IntermediateField.inclusion h).toRingHom
          (continuous_subtype_val.subtype_mk _) (b i : F.1)) f _ _ (h₁ X i) (h₁ Y i)
  · intro X
    obtain ⟨b⟩ := integral_basis_exists ℓ h
    obtain ⟨e₀, _⟩ := integral_sheaf_basis.{u} ℓ h b
    exact ⟨finite_free_flat X
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)
      (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)
      (finiteCoefficientDegree ℓ h) (e₀ X), inferInstance⟩

end AlgebraicGeometry.ProEtale
