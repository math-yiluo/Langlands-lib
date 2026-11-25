/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.NoetherianComponents

/-!
# Extending finite étale covers by normalization

Let `X` be an integral scheme of finite type over a field `k`.

- `AlgebraicGeometry.Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk`: `X` has a
  nonempty (hence dense) open subscheme all of whose local rings are integrally closed.
- `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_apply_genericPoint`: the
  normalization of `X` in an integral scheme `P` mapping quasi-finitely and dominantly to `X`
  is finite over `X`.
- `AlgebraicGeometry.Scheme.Hom.isOpenImmersion_toNormalization_comp`: if `P ⟶ X` factors as an
  integral morphism `P ⟶ V` followed by an open immersion `V ⟶ X`, then `P` is the part of the
  normalization of `X` in `P` lying over `V`.
- `AlgebraicGeometry.Scheme.normalization_comp_of_finite_etale`: for a nonempty normal open
  `V ⊆ X` and a connected finite étale cover `P ⟶ V`, the normalization of `X` in `P` is a
  finite normal integral scheme over `X` which restricts over `V` to `P ⟶ V`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-fin-dense-normal-open`: A dense normal open in an integral finite-type scheme.

Every integral scheme `X` locally of finite type over a field `k` has a nonempty (hence dense)
open subscheme all of whose local rings are integrally closed. Over a nonempty affine open
`Spec A`, the integral closure of the finitely generated `k`-domain `A` in its fraction field is
a finite `A`-module (E. Noether), hence has a common denominator `b ≠ 0`, and `A[1/b]` is
integrally closed. -/
theorem Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk {k : Type u} [Field k]
    (X : Scheme.{u}) [IsIntegral X] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] :
    ∃ V : X.Opens, (V : Set X).Nonempty ∧
      ∀ x ∈ V, IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let := ((q.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, V) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := Algebra.FiniteType.finite_integralClosure k (A := Γ(X, V)) X.functionField
    X.functionField
  obtain ⟨b, hb, hbint⟩ := exists_isInteger_smul_of_finite_integralClosure (A := Γ(X, V))
    (K := X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hηW : genericPoint X ∈ X.basicOpen b := by
    rw [X.mem_basicOpen b _ hηV]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb0)
  have hW : IsAffineOpen (X.basicOpen b) := hV.basicOpen b
  have : Nonempty (X.basicOpen b) := ⟨⟨_, hηW⟩⟩
  have := hV.isLocalization_basicOpen b
  have := functionField_isFractionRing_of_isAffineOpen X _ hW
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen b) X.functionField :=
    .of_algebraMap_eq fun a ↦ (X.presheaf.germ_res_apply _ _ _ a).symm
  have : IsIntegrallyClosed Γ(X, X.basicOpen b) :=
    isIntegrallyClosed_of_isLocalization_away hb0 hbint
  refine ⟨X.basicOpen b, ⟨_, hηW⟩, fun y hy ↦ ?_⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : X.basicOpen b)
  have := hW.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl_le_nonZeroDivisors

namespace Scheme.Hom

variable {P X : Scheme.{u}}

/-- For a locally quasi-finite morphism `f : P ⟶ X` and `z = f x`, the map of stalks
`𝒪_{X, z} ⟶ 𝒪_{P, x}` is quasi-finite. -/
lemma quasiFinite_stalkSpecializes_comp_stalkMap (f : P ⟶ X) [LocallyQuasiFinite f] (x : P)
    (z : X) (hz : f x = z) :
    (X.presheaf.stalkSpecializes (specializes_of_eq hz) ≫ f.stalkMap x).hom.QuasiFinite := by
  subst hz
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact f.quasiFiniteAt x

/-- A locally quasi-finite morphism `f : P ⟶ X` of integral schemes mapping the generic point
to the generic point induces a finite extension of function fields `k(X) ⟶ k(P)`. -/
theorem finiteDimensional_functionField [IsIntegral P] [IsIntegral X] (f : P ⟶ X)
    [LocallyQuasiFinite f] (hf : f (genericPoint P) = genericPoint X) :
    letI := (X.presheaf.stalkSpecializes (specializes_of_eq hf) ≫
      f.stalkMap (genericPoint P)).hom.toAlgebra
    FiniteDimensional X.functionField P.functionField := by
  let := (X.presheaf.stalkSpecializes (specializes_of_eq hf) ≫
    f.stalkMap (genericPoint P)).hom.toAlgebra
  have : Algebra.QuasiFinite X.functionField P.functionField :=
    f.quasiFinite_stalkSpecializes_comp_stalkMap _ _ hf
  exact Module.Finite.of_quasiFinite

/-- Blueprint `lem-fin-normalization-extends-cover` (finiteness): the normalization of a scheme
`X` locally of finite type over a field `k` in an integral scheme `P`, along a locally
quasi-finite morphism `f : P ⟶ X` mapping the generic point of `P` to the generic point of
`X`, is finite over `X`.

Over a nonempty affine open `Spec A` of `X`, the ring `B = Γ(P, f⁻¹ Spec A)` embeds into the
function field `L = k(P)`, a finite extension of `K = Frac A = k(X)`; the integral closure of
`A` in `B` thus embeds into the integral closure of `A` in `L`, a finite `A`-module by
E. Noether's finiteness theorem, and `A` is Noetherian. -/
theorem isFinite_fromNormalization_of_apply_genericPoint {k : Type u} [Field k] [IsIntegral P]
    [IsIntegral X] (f : P ⟶ X) [QuasiCompact f] [QuasiSeparated f] [LocallyQuasiFinite f]
    (hf : f (genericPoint P) = genericPoint X) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] : IsFinite f.fromNormalization := by
  refine f.isFinite_fromNormalization_of_finite fun U hU hne ↦ ?_
  let := (f.app U).hom.toAlgebra
  let := ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hηP : genericPoint P ∈ f ⁻¹ᵁ U := show f (genericPoint P) ∈ U by rwa [hf]
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hηP⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ := X.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint P)
  let := φ.hom.toAlgebra
  have : FiniteDimensional X.functionField P.functionField := f.finiteDimensional_functionField hf
  let : Algebra Γ(X, U) P.functionField :=
    (f.app U ≫ P.germToFunctionField (f ⁻¹ᵁ U)).hom.toAlgebra
  have hφ : f.app U ≫ P.germToFunctionField (f ⁻¹ᵁ U) = X.germToFunctionField U ≫ φ := by
    simp only [φ, germToFunctionField, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      Scheme.Hom.germ_stalkMap]
  have : IsScalarTower Γ(X, U) X.functionField P.functionField :=
    .of_algebraMap_eq' congr(($hφ).hom)
  have := Algebra.FiniteType.finite_integralClosure k (A := Γ(X, U)) X.functionField
    P.functionField
  let e : Γ(P, f ⁻¹ᵁ U) →ₐ[Γ(X, U)] P.functionField :=
    { (P.germToFunctionField (f ⁻¹ᵁ U)).hom with commutes' _ := rfl }
  let ψ : integralClosure Γ(X, U) Γ(P, f ⁻¹ᵁ U) →ₗ[Γ(X, U)]
      integralClosure Γ(X, U) P.functionField :=
    { toFun x := ⟨e x, x.2.map e⟩
      map_add' x y := Subtype.ext (map_add e x.1 y.1)
      map_smul' a x := Subtype.ext (map_smul e a x.1) }
  refine Module.Finite.of_injective ψ fun x y h ↦ ?_
  exact Subtype.ext (P.germToFunctionField_injective (f ⁻¹ᵁ U) congr($h.1))

/-- Blueprint `lem-fin-normalization-extends-cover` (restriction over `V`): let
`f = p ≫ kV : P ⟶ X` be an integral morphism `p : P ⟶ V` followed by an open immersion
`kV : V ⟶ X`. Then `f.toNormalization : P ⟶ f.normalization` is an open immersion whose image
is the preimage of `V` in the normalization of `X` in `P`.

Normalization commutes with the smooth base change `kV`, and the normalization of `V` in
`P ×_X V ≅ P` is trivial since `P ⟶ V` is integral. -/
theorem isOpenImmersion_toNormalization_comp {V : Scheme.{u}} (p : P ⟶ V) (kV : V ⟶ X)
    [IsIntegralHom p] [IsOpenImmersion kV] [QuasiCompact (p ≫ kV)] [QuasiSeparated (p ≫ kV)] :
    IsOpenImmersion (p ≫ kV).toNormalization ∧ Set.range (p ≫ kV).toNormalization.base =
      (p ≫ kV).fromNormalization.base ⁻¹' Set.range kV.base := by
  have hsnd : pullback.snd (p ≫ kV) kV = pullback.fst (p ≫ kV) kV ≫ p := by
    rw [← cancel_mono kV, ← pullback.condition, Category.assoc]
  have : IsIntegralHom (pullback.snd (p ≫ kV) kV) := by rw [hsnd]; infer_instance
  have hsq := (p ≫ kV).toNormalization_normalizationPullback_fst kV
  have hto : (p ≫ kV).toNormalization = inv (pullback.fst (p ≫ kV) kV) ≫
      (pullback.snd (p ≫ kV) kV).toNormalization ≫ (p ≫ kV).normalizationPullback kV ≫
        pullback.fst _ _ := by
    rw [hsq, IsIso.inv_hom_id_assoc]
  refine ⟨by rw [hto]; infer_instance, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨p x, ?_⟩
    change (p ≫ kV) x = ((p ≫ kV).toNormalization ≫ (p ≫ kV).fromNormalization) x
    rw [toNormalization_fromNormalization]
  · rintro ⟨v, hv⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y v hv.symm
    obtain ⟨w, rfl⟩ := ((pullback.snd (p ≫ kV) kV).toNormalization ≫
      (p ≫ kV).normalizationPullback kV).surjective z
    refine ⟨pullback.fst (p ≫ kV) kV w, ?_⟩
    rw [← hz]
    change (pullback.fst (p ≫ kV) kV ≫ (p ≫ kV).toNormalization) w = _
    rw [← hsq]
    rfl

end Scheme.Hom

/-- Blueprint `lem-fin-normalization-extends-cover` (the cover is normal integral): a connected
scheme `P`, étale over an integral scheme `V` with integrally closed local rings, and locally
Noetherian, is integral with integrally closed local rings. -/
theorem Scheme.isIntegral_and_isIntegrallyClosed_stalk_of_etale {P V : Scheme.{u}} (p : P ⟶ V)
    [Etale p] [IsIntegral V] [IsLocallyNoetherian P] [ConnectedSpace P]
    (hV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v)) :
    IsIntegral P ∧ ∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x) := by
  have h := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale p hV
  have hdom (x : P) : IsDomain (P.presheaf.stalk x) := (h x).1
  have : IrreducibleSpace P := irreducibleSpace_of_isDomain_stalk _ hdom
  have : IsReduced P := isReduced_of_isReduced_stalk _
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _, fun x ↦ (h x).2⟩

/-- Blueprint `lem-fin-normalization-extends-cover`: Extending a finite cover by normalization.

Let `X` be an integral scheme of finite type over a field `k`, `kV : V ⟶ X` a nonempty open
subscheme with integrally closed local rings, and `p : P ⟶ V` a connected finite étale cover.
The normalization of `X` in `P` is Mathlib's relative normalization `Y = (p ≫ kV).normalization`
(the relative spectrum of the integral closure of `𝒪_X` in `(p ≫ kV)_* 𝒪_P`); since `P` is
integral, this is the normalization of `X` in the function field `k(P)`, a finite extension of
`k(X)`. Then `P` is normal integral, `Y ⟶ X` is finite, `Y` is normal integral, and
`P ⟶ Y` is an open immersion identifying `P ⟶ V` with the restriction of `Y ⟶ X` over `V`.

The hypothesis `QuasiCompact kV` (needed to form the normalization) is automatic: `X` is
locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian q`), and open immersions into
locally Noetherian schemes are quasi-compact. The same statement for the normalization
`X^{k(P)}` of `X` in the function field of `P` (`def-fin-normalization-extension`) is
`AlgebraicGeometry.Scheme.normalizationIn_extends_cover`. -/
theorem Scheme.normalization_comp_of_finite_etale {k : Type u} [Field k] {P V X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IsIntegral X]
    (kV : V ⟶ X) [IsOpenImmersion kV] [QuasiCompact kV] [Nonempty V]
    (hV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (p : P ⟶ V) [IsFinite p] [Etale p] [ConnectedSpace P] :
    IsIntegral P ∧ (∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) ∧
      IsOpenImmersion (p ≫ kV).toNormalization ∧ IsFinite (p ≫ kV).fromNormalization ∧
      IsIntegral (p ≫ kV).normalization ∧
      (∀ y : (p ≫ kV).normalization,
        IsIntegrallyClosed ((p ≫ kV).normalization.presheaf.stalk y)) ∧
      Set.range (p ≫ kV).toNormalization.base =
        (p ≫ kV).fromNormalization.base ⁻¹' Set.range kV.base := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsIntegral V := isIntegral_of_isOpenImmersion kV
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (p ≫ kV ≫ q)
  obtain ⟨hP, hPst⟩ := Scheme.isIntegral_and_isIntegrallyClosed_stalk_of_etale p hV
  have hgen : (p ≫ kV) (genericPoint P) = genericPoint X := by
    obtain ⟨x, hx, hfx⟩ := Flat.generalizingMap (p ≫ kV)
      (genericPoint_specializes ((p ≫ kV) (genericPoint P)))
    obtain rfl : x = genericPoint P := (hx.antisymm (genericPoint_specializes x)).eq
    exact hfx
  obtain ⟨h₁, h₂⟩ := Scheme.Hom.isOpenImmersion_toNormalization_comp p kV
  exact ⟨hP, hPst, h₁, (p ≫ kV).isFinite_fromNormalization_of_apply_genericPoint hgen q,
    inferInstance, (p ≫ kV).isIntegrallyClosed_stalk_normalization hPst, h₂⟩

end AlgebraicGeometry
