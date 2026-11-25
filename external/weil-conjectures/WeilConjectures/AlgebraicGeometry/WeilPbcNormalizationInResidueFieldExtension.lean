/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open AlgebraicGeometry

/-- Denominator clearing in the affine stalk supplies integral numerators and denominators.
The finite extension is integral over the residue field, which is a quotient of the stalk.
`IsIntegral.exists_multiple_integral_of_isLocalization` clears the coefficients of a monic
relation at the affine prime. The resulting denominator is a unit in the stalk and hence
has nonzero image in `K`. This proves the function-field calculation used in Stacks 09Z6. -/
private theorem finite_residue_extension_integral_quotients
    (X : Scheme.{u}) (x : X) (K : Type u) [Field K]
    [Algebra (X.residueField x) K] [Module.Finite (X.residueField x) K]
    (U : X.Opens) (hU : IsAffineOpen U)
    (hxU : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x) (closedPoint K) ∈ U) :
    let h := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
    let θ := (Spec (.of K)).presheaf.mapIso
      (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem h hxU).symm).op ≪≫
        Scheme.ΓSpecIso (.of K)
    let := (h.app U ≫ θ.hom).hom.toAlgebra
    ∀ l : K, ∃ a b : K, _root_.IsIntegral Γ(X, U) a ∧
      _root_.IsIntegral Γ(X, U) b ∧ b ≠ 0 ∧ a / b = l := by
  dsimp only
  let h := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
    X.fromSpecResidueField x
  let θ := (Spec (.of K)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem h hxU).symm).op ≪≫
      Scheme.ΓSpecIso (.of K)
  let : Algebra Γ(X, U) K := (h.app U ≫ θ.hom).hom.toAlgebra
  change h (closedPoint K) ∈ U at hxU
  have hpt : h (closedPoint K) = x := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hx : x ∈ U := hpt ▸ hxU
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  let f : X.presheaf.stalk x ⟶ .of K :=
    X.residue x ≫ CommRingCat.ofHom (algebraMap (X.residueField x) K)
  have : IsLocalHom (X.residue x).hom := by
    change IsLocalHom (IsLocalRing.residue (X.presheaf.stalk x))
    infer_instance
  have : IsLocalHom f.hom := by
    dsimp only [f, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact RingHom.isLocalHom_comp _ _
  have hf : h = Spec.map f ≫ X.fromSpecStalk x := by
    simp [h, f, Scheme.fromSpecResidueField, Spec.map_comp, Category.assoc]
  have hθ : h.app U ≫ θ.hom = X.presheaf.germ U x hx ≫ f := by
    have hxF : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint K) ∈ U := hf ▸ hxU
    have h₁ := Scheme.germ_stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) U hxF
    have h₂ := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk f U hxF
    have h₃ := h₁.symm.trans h₂
    clear_value h
    subst h
    exact h₃
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  let : Algebra (X.presheaf.stalk x) K := f.hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq' congr($(hθ).hom)
  have : IsScalarTower (X.presheaf.stalk x) (X.residueField x) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsIntegral (X.presheaf.stalk x) (X.residueField x) :=
    Algebra.isIntegral_of_surjective (X.residue_surjective x)
  intro l
  have hl : _root_.IsIntegral (X.presheaf.stalk x) l :=
    isIntegral_trans (R := X.presheaf.stalk x) (A := X.residueField x) l
      (Algebra.IsIntegral.isIntegral l)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl l hl
  have hbunit : IsUnit (algebraMap Γ(X, U) K b) := by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) K]
    exact (IsLocalization.map_units (X.presheaf.stalk x) ⟨b, hb⟩).map _
  refine ⟨b • l, algebraMap Γ(X, U) K b, hbint, isIntegral_algebraMap,
    hbunit.ne_zero, ?_⟩
  rw [Algebra.smul_def, mul_div_cancel_left₀ _ hbunit.ne_zero]


/-- For a finite extension `K` of the residue field at a point of a quasi-separated scheme `X`,
the composite `Spec K ⟶ X` is quasi-compact and quasi-separated and factors through an integral
morphism from an integral normal scheme whose generic point has residue field `K`.

Source: Stacks Project, Morphisms Lemmas 035H, 035I, 035L and Etale Cohomology Lemma 09Z6
(blueprint: lem-weil-pbc-normalization-in-residue-field-extension). The proof first shows that
the composite from the affine field scheme is quasi-compact and quasi-separated. It applies
relative normalization to obtain an integral factorization with dominant map and uses
integrality of the source to make the normalization integral. On affine opens through the
chosen point, the coordinate ring is the integral closure of the corresponding domain in K;
finite-extension normality gives a normal domain with fraction field K. The normalization
normal-stalks theorem gives integrally closed domain stalks. Dominance and sobriety identify
the image of the unique point with the generic point, and the affine residue-field
calculation identifies its residue field with K.
-/
theorem normalization_in_finite_residue_field_extension
    (X : Scheme.{u}) [QuasiSeparatedSpace X] (x : X) (K : Type u) [Field K]
    [Algebra (X.residueField x) K] [Module.Finite (X.residueField x) K] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x) ∧
      QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x) ∧
      ∃ (Y : Scheme.{u}) (ν : Y ⟶ X) (g : Spec (.of K) ⟶ Y),
        IsIntegralHom ν ∧
          Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
              X.fromSpecResidueField x = g ≫ ν ∧
          IsIntegral Y ∧
          (∀ y : Y,
            IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          ∃ η : Y, IsGenericPoint η Set.univ ∧
            g (IsLocalRing.closedPoint K) = η ∧
            IsIso (g.residueFieldMap (IsLocalRing.closedPoint K)) := by
  let h := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
    X.fromSpecResidueField x
  have : QuasiCompact h := inferInstance
  have : QuasiSeparated h := inferInstance
  refine ⟨inferInstance, inferInstance, h.normalization, h.fromNormalization,
    h.toNormalization, inferInstance, h.toNormalization_fromNormalization.symm,
    inferInstance, ?_, ?_⟩
  · intro y
    refine ⟨inferInstance, h.isIntegrallyClosed_stalk_normalization ?_ y⟩
    intro z
    have hz : z = closedPoint K := Subsingleton.elim _ _
    subst z
    exact IsIntegrallyClosed.of_equiv
      (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.symm
  · let g := h.toNormalization
    have hη : IsGenericPoint (g (closedPoint K)) Set.univ := by
      have hd : DenseRange g := g.denseRange
      change closure ({g (closedPoint K)} : Set h.normalization) = Set.univ
      rw [← hd.closure_range]
      congr 1
      ext y
      exact ⟨fun hy ↦ ⟨closedPoint K, hy.symm⟩,
        fun ⟨z, hz⟩ ↦ by rw [← hz, Subsingleton.elim z (closedPoint K)]; rfl⟩
    refine ⟨g (closedPoint K), hη, rfl, ?_⟩
    have hq : g (closedPoint K) = genericPoint h.normalization :=
      hη.eq (genericPoint_spec h.normalization)
    have hfield : IsField (h.normalization.presheaf.stalk (g (closedPoint K))) := by
      rw [hq]
      exact Field.toIsField h.normalization.functionField
    let ψ := Scheme.stalkClosedPointTo g
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (h (closedPoint K))) isOpen_univ
    have hU' : g (closedPoint K) ∈ h.fromNormalization ⁻¹ᵁ U := by
      change (g ≫ h.fromNormalization) (closedPoint K) ∈ U
      rwa [Scheme.Hom.toNormalization_fromNormalization]
    have hpre : h ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem h hxU
    let θ : Γ(Spec (.of K), h ⁻¹ᵁ U) ≅ .of K :=
      (Spec (.of K)).presheaf.mapIso (eqToIso hpre.symm).op ≪≫ Scheme.ΓSpecIso (.of K)
    let : Algebra Γ(X, U) K := (h.app U ≫ θ.hom).hom.toAlgebra
    have hint (m : K) (hm : _root_.IsIntegral Γ(X, U) m) : m ∈ Set.range ψ.hom := by
      let : Algebra Γ(X, U) Γ(Spec (.of K), h ⁻¹ᵁ U) := (h.app U).hom.toAlgebra
      have ht : _root_.IsIntegral Γ(X, U) (θ.inv m) := by
        refine IsIntegral.map_of_comp_eq (RingHom.id _) θ.inv.hom ?_ hm
        ext b
        change h.app U b = θ.inv ((h.app U ≫ θ.hom) b)
        rw [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      let s := (h.normalizationObjIso hU).inv ⟨θ.inv m, ht⟩
      have hs := congr($(h.normalizationObjIso_hom_val hU) s)
      simp only [s, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hs
      have h1 := congr($(Scheme.germ_stalkClosedPointTo g _ hU') s)
      refine ⟨(h.normalization.presheaf.germ _ _ hU') s, h1.trans ?_⟩
      have key : g.app (h.fromNormalization ⁻¹ᵁ U) ≫
          ((Spec (.of K)).presheaf.mapIso
            (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem g hU').symm).op ≪≫
              Scheme.ΓSpecIso (.of K)).hom =
          g.appLE (h.fromNormalization ⁻¹ᵁ U) (h ⁻¹ᵁ U)
            (le_top.trans (Scheme.preimage_eq_top_of_closedPoint_mem g hU').ge) ≫ θ.hom := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
          Scheme.Hom.appLE, θ, Category.assoc, ← Functor.map_comp_assoc]
        rfl
      rw [key, CommRingCat.comp_apply, ← hs]
      exact θ.inv_hom_id_apply m
    let := hfield.toField
    have hsurj : Function.Surjective ψ.hom := by
      intro l
      obtain ⟨a, b, ha, hb, -, hab⟩ :=
        finite_residue_extension_integral_quotients X x K U hU hxU l
      obtain ⟨a', ha'⟩ := hint a ha
      obtain ⟨b', hb'⟩ := hint b hb
      refine ⟨a' / b', ?_⟩
      rw [map_div₀, ha', hb', hab]
    let δ := h.normalization.descResidueField ψ
    have hδ : IsIso δ := by
      apply (ConcreteCategory.isIso_iff_bijective δ).2
      refine ⟨δ.hom.injective, ?_⟩
      intro l
      obtain ⟨a, ha⟩ := hsurj l
      refine ⟨h.normalization.residue _ a, ?_⟩
      exact congr($(Scheme.residue_descResidueField ψ) a).trans ha
    let ψ₀ := Scheme.stalkClosedPointTo (𝟙 (Spec (.of K)))
    have : IsIso ψ₀ := by
      dsimp [ψ₀, Scheme.stalkClosedPointTo]
      infer_instance
    let δ₀ := (Spec (.of K)).descResidueField ψ₀
    have : IsIso δ₀ := by
      apply (ConcreteCategory.isIso_iff_bijective δ₀).2
      refine ⟨δ₀.hom.injective, ?_⟩
      intro l
      obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso ψ₀).2 l
      refine ⟨(Spec (.of K)).residue _ a, ?_⟩
      exact congr($(Scheme.residue_descResidueField ψ₀) a).trans ha
    have heq : g.residueFieldMap (closedPoint K) ≫ δ₀ = δ := by
      apply (cancel_epi (h.normalization.residue _)).1
      rw [← Category.assoc, Scheme.residue_residueFieldMap, Category.assoc]
      change g.stalkMap (closedPoint K) ≫
        ((Spec (.of K)).residue (closedPoint K) ≫ δ₀) =
          h.normalization.residue _ ≫ δ
      rw [Scheme.residue_descResidueField, Scheme.residue_descResidueField]
      simp [ψ, ψ₀, Scheme.stalkClosedPointTo]
    have : IsIso (g.residueFieldMap (closedPoint K) ≫ δ₀) := heq.symm ▸ hδ
    exact IsIso.of_isIso_comp_right _ δ₀

