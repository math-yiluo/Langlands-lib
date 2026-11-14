import Langlands.Geometry.Building.CentralizingDescendedApartment
import Langlands.Geometry.Building.IntegralConjugacyApartmentContainment
import Langlands.GroupScheme.IntegralModel.ResidueMaximalSplitTorus

/-! # Centralizing charts from residue-maximal integral tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building.KPApartmentData

private def groupIso {S : Scheme.{u}} {T T' : CommGroupScheme S}
    (e : T ≅ T') : T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

private theorem groupHom_comp {S : Scheme.{u}} {T T' T'' : CommGroupScheme S}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    CommGroupScheme.groupHom (f ≫ g) =
      CommGroupScheme.groupHom f ≫ CommGroupScheme.groupHom g := rfl

variable (F K : Type u) [Field F] [Field K] [Algebra F K]
  {R : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [Algebra R K] [IsFractionRing R K]
  {k : Type u} [Field k] [Algebra R k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
  [Mono ((baseChange (algebraBaseMap F K)).map i).hom.hom.left]
  [IsAffineHom (baseChanged F K G).X.hom]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
    ((baseChange (algebraBaseMap F K)).map i) ω)
  (M : IntegralModel R K (baseChanged F K G))

/-- A descended residue-maximal integral torus containing the common split
subtorus gives a centralizing chart covering any integrally fixed subset
already covered by a translated chart with a closed integral reference torus. -/
def centralizingConjOfResidueMaximalIntegralTorus
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive (baseChanged F K G))
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj M.group).X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of K))}
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ baseChanged F K G)
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
      ((baseChange (algebraBaseMap F K)).map i))
    (f : A ⟶ (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
    (f' : A ⟶ (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T')
    (hf : CommGroupScheme.groupHom f ≫ (baseChange (algebraBaseMap F K)).map i = a)
    (hf' : CommGroupScheme.groupHom f' ≫ (baseChange (algebraBaseMap F K)).map j = a)
    {Y : Set D.ReducedBuilding}
    (hfix : M.integralPoints ≤ fixingSubgroup (rationalPoints (baseChanged F K G)) Y)
    (q : rationalPoints (baseChanged F K G))
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x))
    {T₀ T₁ : CommGroupScheme (Spec (CommRingCat.of R))}
    (hT₀ : IsSplitTorus T₀.toGrp) (hT₁ : IsSplitTorus T₁.toGrp)
    (i₀ : T₀.toGrp ⟶ M.group) (i₁ : T₁.toGrp ⟶ M.group)
    (e₀ : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
    (he₀ : M.genericHom i₀ = CommGroupScheme.groupHom e₀.hom ≫
      ((baseChange (algebraBaseMap F K)).map i ≫ ((baseChanged F K G).innerIso q).hom))
    (h₀ : IsClosedSubgroup i₀)
    (e₁ : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₁ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T')
    (he₁ : M.genericHom i₁ = CommGroupScheme.groupHom e₁.hom ≫
      (baseChange (algebraBaseMap F K)).map j)
    (h₁ : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁)
      ((baseChange (Spec.algebraMap R k)).map i₁)) :
    {g : rationalPoints (baseChanged F K G) //
      g ∈ centralizerPoints a ∧
      (∀ σ : K ≃ₐ[F] K,
        g⁻¹ * rationalConjugate F K G σ g ∈
          normalizerPoints
            (T := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
            ((baseChange (algebraBaseMap F K)).map i)) ∧
      Y ⊆ Set.range (fun x : D.Apartment => g • D.apartmentMap x)} := by
  have h₀K : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀)
      (M.genericHom i₀) := by
    rw [he₀]
    exact (hi.comp_iso ((baseChanged F K G).innerIso q)).iso_comp
      (groupIso e₀)
  let B := M.henselianSplitTorusConjugatorOfResidueGeneric
    hM hk hG hT₁ hT₀ h₀ h₁ h₀K
  have h₁K := (B.isMaximalSplitTorus_generic_iff M).mpr h₀K
  have hj : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T')
      ((baseChange (algebraBaseMap F K)).map j) := by
    rw [he₁] at h₁K
    exact (IsMaximalSplitTorus.iso_comp_iff (groupIso e₁) _).mp h₁K
  have hq :
      (baseChange (algebraBaseMap F K)).map i ≫ ((baseChanged F K G).innerIso q).hom =
        CommGroupScheme.groupHom e₀.inv ≫ M.genericHom i₀ := by
    rw [he₀, ← Category.assoc]
    change _ = CommGroupScheme.groupHom
      (e₀.inv ≫ e₀.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  let e := e₀.symm ≪≫
    ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso B.torusIso).symm ≪≫
    e₁
  have hconj :
      (baseChange (algebraBaseMap F K)).map i ≫
          ((baseChanged F K G).innerIso ((B.genericPoint M)⁻¹ * q)).hom =
        CommGroupScheme.groupHom e.hom ≫ (baseChange (algebraBaseMap F K)).map j := by
    simpa only [he₁, e, Iso.trans_hom, Iso.symm_hom,
      groupHom_comp, Category.assoc] using
      B.inverse_translated_generic_comm M q e₀.symm hq
  let c := D.centralizingConjCoveringOfDescendedTorus F K i j hG hA a
    hi hj f f' hf hf' ((B.genericPoint M)⁻¹ * q) e hconj
  refine ⟨c.val, c.property.1, c.property.2.1, ?_⟩
  intro y hy
  exact (c.property.2.2 y).mp
    (D.subset_range_integralConjugacyApartmentMap B hfix q hY hy)

end Langlands.Geometry.Building.KPApartmentData
