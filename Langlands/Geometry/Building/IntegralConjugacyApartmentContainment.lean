import Langlands.GroupScheme.IntegralModel.SplitTorusConjugacy
import Langlands.Geometry.Building.ConjugateApartmentRealization

/-! # Integral split-torus conjugacy preserves covering apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.SplitTorusConjugator

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {T₁ T₀ : CommGroupScheme (Spec (CommRingCat.of R))}
  {i₁ : T₁.toGrp ⟶ M.group} {i₀ : T₀.toGrp ⟶ M.group}
  (A : SplitTorusConjugator i₁ i₀)
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G}

/-- Compose the initial generic square with the inverse of the same integral
conjugator. The point acts first by `q`, then by the inverse conjugator. -/
theorem inverse_translated_generic_comm
    (q : rationalPoints G)
    (e₀ : S ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀)
    (hq : i ≫ (G.innerIso q).hom =
      CommGroupScheme.groupHom e₀.hom ≫ M.genericHom i₀) :
    i ≫ (G.innerIso ((A.genericPoint M)⁻¹ * q)).hom =
      CommGroupScheme.groupHom
        (e₀ ≪≫ ((CommGroupScheme.baseChange
          (Spec.algebraMap R K)).mapIso A.torusIso).symm).hom ≫ M.genericHom i₁ := by
  rw [innerIso_mul_hom, ← Category.assoc, hq, Category.assoc,
    A.inverse_generic_comm M]
  rfl

end Langlands.GroupScheme.SplitTorusConjugator

namespace Langlands.Geometry.Building.KPApartmentData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G}
  {T₁ T₀ : CommGroupScheme (Spec (CommRingCat.of R))}
  {i₁ : T₁.toGrp ⟶ M.group} {i₀ : T₀.toGrp ⟶ M.group}
  (A : SplitTorusConjugator i₁ i₀)
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : Kˣ → ℝ} (D : KPApartmentData i ω)

/-- Translate a supplied chart by `q` and the inverse of the actual generic
point of an integral split-torus conjugator. -/
def integralConjugacyApartmentMap (q : rationalPoints G) (x : D.Apartment) :
    D.ReducedBuilding :=
  ((A.genericPoint M)⁻¹ * q) • D.apartmentMap x

/-- Integral fixation preserves coverage when the inverse conjugator acts
on the initial translated chart. -/
theorem subset_range_integralConjugacyApartmentMap
    {Y : Set D.ReducedBuilding}
    (hM : M.integralPoints ≤ fixingSubgroup (rationalPoints G) Y)
    (q : rationalPoints G)
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x)) :
    Y ⊆ Set.range (D.integralConjugacyApartmentMap A q) := by
  intro y hy
  obtain ⟨x, hx⟩ := hY hy
  change q • D.apartmentMap x = y at hx
  refine ⟨x, ?_⟩
  change ((A.genericPoint M)⁻¹ * q) • D.apartmentMap x = y
  rw [mul_smul, hx]
  exact ((mem_fixingSubgroup_iff _).mp
    (hM (M.integralPoints.inv_mem (A.genericPoint_mem_integralPoints M)))) y hy

/-- The generic square is derived from the recorded integral conjugacy;
the resulting actual target-torus apartment covers the same fixed subset. -/
theorem subset_range_integralConjugacy_conjugateApartmentMap
    [Mono (M.genericHom i₁).hom.hom.left]
    {Y : Set D.ReducedBuilding}
    (hM : M.integralPoints ≤ fixingSubgroup (rationalPoints G) Y)
    (q : rationalPoints G)
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x))
    (e₀ : S ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀)
    (hq : i ≫ (G.innerIso q).hom =
      CommGroupScheme.groupHom e₀.hom ≫ M.genericHom i₀) :
    Y ⊆ Set.range (D.conjugateApartmentMap
      (e₀ ≪≫ ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso).symm)
      ((A.genericPoint M)⁻¹ * q) (A.inverse_translated_generic_comm M q e₀ hq)) := by
  intro y hy
  obtain ⟨x, hx⟩ := D.subset_range_integralConjugacyApartmentMap A hM q hY hy
  refine ⟨D.apartmentTransportEquiv _ _ _ x, ?_⟩
  rw [D.conjugateApartmentMap_transport]
  exact hx

variable [HenselianLocalRing R]
  {k : Type u} [Field k] [Algebra R k]

/-- Closed integral split tori maximal in the specified generic group provide
an actual target-torus apartment containing any integrally fixed subset already
covered by the given translated chart. -/
theorem exists_integralConjugacy_conjugateApartmentMap
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G)
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₀ : IsSplitTorus T₀.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj M.group).X.left]
    (hi₁ : IsClosedSubgroup i₁) (hi₀ : IsClosedSubgroup i₀)
    (hi₁K : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₁)
      (M.genericHom i₁))
    (hi₀K : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀)
      (M.genericHom i₀))
    {Y : Set D.ReducedBuilding}
    (hfix : M.integralPoints ≤ fixingSubgroup (rationalPoints G) Y)
    (q : rationalPoints G)
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x))
    (e₀ : S ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₀)
    (hq : i ≫ (G.innerIso q).hom =
      CommGroupScheme.groupHom e₀.hom ≫ M.genericHom i₀) :
    letI : IsClosedImmersion (M.genericHom i₁).hom.hom.left := hi₁K.1.2
    ∃ (e : S ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₁)
      (g : rationalPoints G)
      (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ M.genericHom i₁),
      g * q⁻¹ ∈ M.integralPoints ∧
        Y ⊆ Set.range (D.conjugateApartmentMap e g h) := by
  let : IsClosedImmersion (M.genericHom i₁).hom.hom.left := hi₁K.1.2
  let B : SplitTorusConjugator i₁ i₀ :=
    M.henselianSplitTorusConjugator hM hk hG hT₁ hT₀ hi₁ hi₀ hi₁K hi₀K
  refine ⟨e₀ ≪≫ ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso B.torusIso).symm,
    (B.genericPoint M)⁻¹ * q, B.inverse_translated_generic_comm M q e₀ hq, ?_,
    D.subset_range_integralConjugacy_conjugateApartmentMap B hfix q hY e₀ hq⟩
  simpa only [mul_inv_cancel_right] using
    M.integralPoints.inv_mem (B.genericPoint_mem_integralPoints M)

end Langlands.Geometry.Building.KPApartmentData
