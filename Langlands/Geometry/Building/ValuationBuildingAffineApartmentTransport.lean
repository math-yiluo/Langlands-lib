import Langlands.Geometry.Building.ValuationBuildingRealizationTransport
import Langlands.Geometry.Building.FiniteRealTorusSpace

/-! # Transport of the actual affine-apartment splitting axiom -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.GroupScheme.RealTorusSpace

variable {F : Type u} [Field F]
  {A S T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Postcomposition by an actual torus isomorphism maps the real cocharacter range
by the scalar-extended cocharacter equivalence. -/
theorem range_cocharacterMapReal_comp_iso (f : A ⟶ S) (σ : S ≅ T) :
    LinearMap.range (cocharacterMapReal (f ≫ σ.hom)) =
      (LinearMap.range (cocharacterMapReal f)).map (cocharacterRealCongr σ).toLinearMap := by
  have h : cocharacterMapReal (f ≫ σ.hom) =
      (cocharacterRealCongr σ).toLinearMap.comp (cocharacterMapReal f) := by
    apply AlgebraTensorModule.ext
    intro r ν
    simp [cocharacterMapReal_tmul, cocharacterRealCongr_tmul, Category.assoc]
  rw [h, LinearMap.range_comp]

end Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B₁ B₂ : ValuationBuildingData G)
  (σ : B₁.S ≅ B₂.S)

/-- Retain the actual derived and central tori and postcompose their embeddings. -/
def ApartmentSplitting.transport (T : B₁.ApartmentSplitting) : B₂.ApartmentSplitting where
  D := T.D
  d := T.d
  derivedTorus := T.derivedTorus
  j := T.j
  e := T.e ≫ σ.hom
  centralTorus := T.centralTorus
  a := T.a ≫ σ.hom

variable (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)

/-- The actual normalizer groups are identified by the identity on rational points. -/
def normalizerEquivOfTorusIso : normalizerPoints B₁.i ≃* normalizerPoints B₂.i :=
  MulEquiv.subgroupCongr (normalizerPoints_eq_of_torusIso B₁ B₂ σ hσ)

@[simp] theorem normalizerEquivOfTorusIso_apply (n : normalizerPoints B₁.i) :
    (normalizerEquivOfTorusIso B₁ B₂ σ hσ n : rationalPoints G) = n := rfl

@[simp] theorem normalizerEquivOfTorusIso_symm_apply (n : normalizerPoints B₂.i) :
    ((normalizerEquivOfTorusIso B₁ B₂ σ hσ).symm n : rationalPoints G) = n := rfl

include hσ

/-- The two chosen normalizing automorphisms commute with the actual torus isomorphism. -/
theorem normalizingAut_comp_torusIso (n : normalizerPoints B₁.i) :
    (normalizingAut B₁.i n).hom ≫ σ.hom =
      σ.hom ≫ (normalizingAut B₂.i (normalizerEquivOfTorusIso B₁ B₂ σ hσ n)).hom := by
  have hs : B₁.i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ B₂.i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  have hn : IsNormalizingPoint B₂.i
      (normalizerEquivOfTorusIso B₁ B₂ σ hσ n : rationalPoints G)
      (σ.symm ≪≫ normalizingAut B₁.i n ≪≫ σ) := by
    simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.comp_id,
      normalizerEquivOfTorusIso_apply] using
      (isNormalizingPoint_normalizingAut B₁.i n).transport σ (Iso.refl G) hs
  rw [(isNormalizingPoint_normalizingAut B₂.i
    (normalizerEquivOfTorusIso B₁ B₂ σ hσ n)).unique B₂.i hn]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

section QuotientComparison

variable (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)
  (hΦ : ∀ (g : rationalPoints G) (q : B₁.ReducedBuilding), Φ (g • q) = g • Φ q)
  (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hmap : ∀ x : B₁.Apartment, Φ (B₁.apartmentMap x) = B₂.apartmentMap (e x))
  (hinj : Function.Injective B₂.apartmentMap)

include hΦ hmap hinj

/-- An injective target apartment map reflects the equivariant quotient comparison
to compatibility of the actual normalizer actions. -/
theorem normalizerAction_compatible_of_comparison
    (n : normalizerPoints B₁.i) (x : B₁.Apartment) :
    e (B₁.normalizerAction n x) =
      B₂.normalizerAction (normalizerEquivOfTorusIso B₁ B₂ σ hσ n) (e x) := by
  apply hinj
  rw [← hmap, B₂.normalizerAction_apply, ← B₂.normalizer_smul_apartmentMap,
    ← hmap, ← hΦ, B₁.normalizerAction_apply, ← B₁.normalizer_smul_apartmentMap,
    normalizerEquivOfTorusIso_apply]

end QuotientComparison

variable (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hact : ∀ (n : normalizerPoints B₁.i) (x : B₁.Apartment),
    e (B₁.normalizerAction n x) =
      B₂.normalizerAction (normalizerEquivOfTorusIso B₁ B₂ σ hσ n) (e x))

include hact

/-- Every field of KP Axiom 4.1.4 transfers to the actual transported splitting. -/
theorem ApartmentSplitting.transport_satisfiesAffineApartmentAxiom
    (T : B₁.ApartmentSplitting) (hT : B₁.SatisfiesAffineApartmentAxiom T) :
    B₂.SatisfiesAffineApartmentAxiom (T.transport B₁ B₂ σ) where
  isDerivedSubgroup := hT.isDerivedSubgroup
  isMaximalSplitTorus_j := hT.isMaximalSplitTorus_j
  isClosedSubgroup_e := by
    let eσ : B₁.S.toGrp ≅ B₂.S.toGrp :=
      { hom := CommGroupScheme.groupHom σ.hom
        inv := CommGroupScheme.groupHom σ.inv
        hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
        inv_hom_id := congrArg Additive.toMul σ.inv_hom_id }
    exact hT.isClosedSubgroup_e.comp (IsClosedSubgroup.of_iso eσ)
  j_comp_d := by
    change T.j ≫ T.d = CommGroupScheme.groupHom (T.e ≫ σ.hom) ≫ B₂.i
    rw [hT.j_comp_d, hσ]
    rfl
  isSplitComponent := by
    change IsSplitComponent (CommGroupScheme.groupHom (T.a ≫ σ.hom) ≫ B₂.i)
    have h : CommGroupScheme.groupHom (T.a ≫ σ.hom) ≫ B₂.i =
        CommGroupScheme.groupHom T.a ≫ B₁.i := by
      rw [hσ]
      rfl
    rw [h]
    exact hT.isSplitComponent
  isCompl := by
    change IsCompl (LinearMap.range (cocharacterMapReal (T.e ≫ σ.hom)))
      (LinearMap.range (cocharacterMapReal (T.a ≫ σ.hom)))
    rw [range_cocharacterMapReal_comp_iso, range_cocharacterMapReal_comp_iso]
    exact (Submodule.orderIsoMapComap (cocharacterRealCongr σ)).isCompl hT.isCompl
  normalizer_derivedTorus := by
    intro n
    let N := normalizerEquivOfTorusIso B₁ B₂ σ hσ
    obtain ⟨τ, hτ⟩ := hT.normalizer_derivedTorus (N.symm n)
    refine ⟨τ, ?_⟩
    change τ.hom ≫ (T.e ≫ σ.hom) =
      (T.e ≫ σ.hom) ≫ (normalizingAut B₂.i n).hom
    rw [← Category.assoc, hτ, Category.assoc,
      normalizingAut_comp_torusIso B₁ B₂ σ hσ (N.symm n)]
    simp only [N, MulEquiv.apply_symm_apply, Category.assoc]
  center_acts_trivially := by
    intro n hn
    let N := normalizerEquivOfTorusIso B₁ B₂ σ hσ
    have hc : B₁.normalizerAction (N.symm n) = 1 :=
      hT.center_acts_trivially (N.symm n) hn
    apply AffineEquiv.ext
    intro y
    have hy := hact (N.symm n) (e.symm y)
    simpa only [N, MulEquiv.apply_symm_apply, hc, AffineEquiv.coe_one, id_eq,
      e.apply_symm_apply] using hy.symm
  affineConjugations := B₂.hasAffineConjugations

end Langlands.Geometry.Building.ValuationBuildingData
