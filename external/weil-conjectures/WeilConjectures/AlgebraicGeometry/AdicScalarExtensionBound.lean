/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Cohomological bounds after scalar extension

Source: Stacks Project, Tags 08G0, 08G1, 06YQ and 06YY, bounded flat models.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- Scalar extension of a complex of Tor amplitude [a,b] has cohomology in [a,b].
Source: Stacks Project, Cohomology on Sites, Tags 08G0, 08G1, 06YQ and 06YY; the scalar-extension
boundedness part of lem-sfb-adic-finite-etale-transitions, proof step 2.
(auxiliary; not a blueprint node).

Proof: the coefficient-model flat-model criterion supplies a representative P
supported in [a,b] with flat terms. It is K-flat by the bounded-above flat
criterion. The universal scalar computation identifies the extended derived
object with the localization of change(f)(P). Scalar extension is additive,
so it preserves the zero terms outside [a,b]. Consequently that localization
has cohomology only in [a,b]. Apply cohomology to the computation and the
representative isomorphism to transport the bounds to the extended object.
This works for every ring map, including the identity and maps to the zero
ring; it uses no constructibility or Noetherian assumption. -/
theorem adicScalarExtension_bound {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) {A B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (K : ConstantCompletion.D (constant T A)) (a b : ℤ)
    (hK : HasCoefficientModelTorAmplitude (constant T A) K a b) :
    ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology (constant T B) q).obj
        ((adicFiniteExtension T f).obj K)) := by
  let R := constant T A
  let S := constant T B
  let φ := adicFiniteConstantMap f T
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨P, hPa, hPb, hflat, ⟨eP⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R K a b hK.1).mp hK
  have : (change φ).Additive := change_additive φ
  let L : Cx S := ((change φ).mapHomologicalComplex (.up ℤ)).obj P
  have hLa : L.IsStrictlyGE a := (L.isStrictlyGE_iff a).mpr (fun i hi ↦
    (change φ).map_isZero (P.isZero_of_isStrictlyGE a i hi))
  have hLb : L.IsStrictlyLE b := (L.isStrictlyLE_iff b).mpr (fun i hi ↦
    (change φ).map_isZero (P.isZero_of_isStrictlyLE b i hi))
  have hk : P.IsKFlatTensor := CochainComplex.isKFlat_of_boundedAbove_flat P
    ⟨b, fun i hi ↦ P.isZero_of_isStrictlyLE b i hi⟩ hflat
  have : IsIso ((extendComparison φ).app P) := (derivedExtension φ).computation P hk
  let e : (Q S).obj L ≅ (adicFiniteExtension T f).obj K :=
    (asIso ((extendComparison φ).app P)).symm ≪≫ (extend φ).mapIso eP
  have hge : ((Q S).obj L).IsGE a := inferInstance
  have hle : ((Q S).obj L).IsLE b := inferInstance
  intro q hq
  have hz : IsZero ((coefficientModelCohomology S q).obj ((Q S).obj L)) := by
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).mp hge q hq
    · exact (DerivedCategory.isLE_iff _ b).mp hle q hq
  exact hz.of_iso ((coefficientModelCohomology S q).mapIso e.symm)

end AlgebraicGeometry.Scheme
