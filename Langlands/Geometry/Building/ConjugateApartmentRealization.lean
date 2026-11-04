import Langlands.Geometry.Building.CrossTorusReducedBuilding

/-! # Realizing a conjugate valuation apartment in the original quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (g : rationalPoints G)
  (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω)

/-- Rebase the conjugated quotient in the original quotient by the original action of `g`. -/
def conjugateReducedBuildingEquiv :
    (D.transport e (G.innerIso g) h).ReducedBuilding ≃ D.ReducedBuilding where
  toFun q := g • (D.reducedBuildingTransportEquiv e (G.innerIso g) h).symm q
  invFun q := D.reducedBuildingTransportEquiv e (G.innerIso g) h (g⁻¹ • q)
  left_inv q := by
    dsimp only
    rw [inv_smul_smul, Equiv.apply_symm_apply]
  right_inv q := by
    dsimp only
    rw [Equiv.symm_apply_apply, smul_inv_smul]

/-- Rebasing cancels inner twisting and intertwines the same original rational-point action. -/
theorem conjugateReducedBuildingEquiv_smul (u : rationalPoints G)
    (q : (D.transport e (G.innerIso g) h).ReducedBuilding) :
    D.conjugateReducedBuildingEquiv e g h (u • q) =
      u • D.conjugateReducedBuildingEquiv e g h q := by
  obtain ⟨q, rfl⟩ := (D.reducedBuildingTransportEquiv e (G.innerIso g) h).surjective q
  have hconj : rationalPoints.map (G.innerIso g).hom (g⁻¹ * u * g) = u := by
    rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self]
    group
  have hinv :
      (D.reducedBuildingTransportEquiv e (G.innerIso g) h).symm
          (u • D.reducedBuildingTransportEquiv e (G.innerIso g) h q) =
        (g⁻¹ * u * g) • q := by
    apply (D.reducedBuildingTransportEquiv e (G.innerIso g) h).injective
    rw [Equiv.apply_symm_apply, D.reducedBuildingTransportEquiv_smul, hconj]
  change g • (D.reducedBuildingTransportEquiv e (G.innerIso g) h).symm
      (u • D.reducedBuildingTransportEquiv e (G.innerIso g) h q) =
    u • (g • (D.reducedBuildingTransportEquiv e (G.innerIso g) h).symm
      (D.reducedBuildingTransportEquiv e (G.innerIso g) h q))
  rw [hinv, Equiv.symm_apply_apply, smul_smul, smul_smul]
  congr 1
  group

/-- The conjugate apartment is realized as an actual map into the original reduced quotient. -/
def conjugateApartmentMap (x : (D.transport e (G.innerIso g) h).Apartment) :
    D.ReducedBuilding :=
  D.conjugateReducedBuildingEquiv e g h
    ((D.transport e (G.innerIso g) h).apartmentMap x)

/-- The affine conjugation comparison realizes exactly the original action of `g`. -/
theorem conjugateApartmentMap_transport (x : D.Apartment) :
    D.conjugateApartmentMap e g h (D.apartmentTransportEquiv e (G.innerIso g) h x) =
      g • D.apartmentMap x := by
  change g • (D.reducedBuildingTransportEquiv e (G.innerIso g) h).symm
      ((D.transport e (G.innerIso g) h).apartmentMap
        (D.apartmentTransportEquiv e (G.innerIso g) h x)) = g • D.apartmentMap x
  rw [← D.reducedBuildingTransportEquiv_apartmentMap, Equiv.symm_apply_apply]

/-- The actual target normalizer acts through its original rational points in the same quotient. -/
theorem conjugateApartmentMap_smul (n : normalizerPoints j)
    (x : (D.transport e (G.innerIso g) h).Apartment) :
    D.conjugateApartmentMap e g h (n • x) =
      (n : rationalPoints G) • D.conjugateApartmentMap e g h x := by
  change D.conjugateReducedBuildingEquiv e g h
      ((D.transport e (G.innerIso g) h).apartmentMap (n • x)) =
    (n : rationalPoints G) • D.conjugateReducedBuildingEquiv e g h
      ((D.transport e (G.innerIso g) h).apartmentMap x)
  rw [apartmentMap_smul, D.conjugateReducedBuildingEquiv_smul]

/-- Its image is exactly the translate of the original apartment image by `g`. -/
theorem range_conjugateApartmentMap :
    Set.range (D.conjugateApartmentMap e g h) = g • Set.range D.apartmentMap := by
  apply Set.ext
  intro q
  constructor
  · rintro ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e (G.innerIso g) h).surjective x'
    rw [D.conjugateApartmentMap_transport]
    exact ⟨D.apartmentMap x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨D.apartmentTransportEquiv e (G.innerIso g) h x,
      D.conjugateApartmentMap_transport e g h x⟩

/-- The actual conjugate apartment map is injective exactly when the original chart is. -/
theorem conjugateApartmentMap_injective_iff :
    Function.Injective (D.conjugateApartmentMap e g h) ↔
      Function.Injective D.apartmentMap := by
  have hcomp :
      Function.Injective (D.conjugateApartmentMap e g h) ↔
        Function.Injective (D.transport e (G.innerIso g) h).apartmentMap := by
    constructor
    · intro hmap x y hxy
      exact hmap (congrArg (D.conjugateReducedBuildingEquiv e g h) hxy)
    · intro hmap x y hxy
      exact hmap ((D.conjugateReducedBuildingEquiv e g h).injective hxy)
  exact hcomp.trans (D.apartmentMap_injective_transport_iff e (G.innerIso g) h)

/-- Full stabilizers coincide under this same-action identification of quotient realizations. -/
theorem reducedFixer_conjugateReducedBuildingEquiv
    (q : (D.transport e (G.innerIso g) h).ReducedBuilding) :
    D.reducedFixer (D.conjugateReducedBuildingEquiv e g h q) =
      (D.transport e (G.innerIso g) h).reducedFixer q := by
  apply Subgroup.ext
  intro u
  rw [mem_reducedFixer, mem_reducedFixer,
    ← D.conjugateReducedBuildingEquiv_smul]
  exact (D.conjugateReducedBuildingEquiv e g h).injective.eq_iff

end Langlands.Geometry.Building.KPApartmentData
