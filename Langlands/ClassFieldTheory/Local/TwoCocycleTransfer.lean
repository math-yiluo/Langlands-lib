import Langlands.ClassFieldTheory.Local.Corestriction
import Langlands.Cohomology.Tate.CohomologyTransferZero
import Langlands.Cohomology.Tate.HomologyTransferRepresentatives
import Langlands.Cohomology.Tate.PositiveCorestriction

noncomputable section

open CategoryTheory

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The inhomogeneous coordinates of the ordinary cochain transfer. -/
theorem ordinaryCorestrictionCochainMap_apply (A : Rep.{u} R G) (n : ℕ)
    (c : (Fin n → H) → Rep.res H.subtype A) (g : Fin n → G) :
    (ordinaryCorestrictionCochainMap H A).f n c g =
      ∑ q : G ⧸ H, A.ρ q.out (c (transferTuple H n g q)) := by
  change (cochainsIsoStandard A).inv.f n
    (homTransfer H ((Rep.standardComplex R G).X n) A
      (standardCosetComparisonComponent H n ≫
        (cochainsIsoStandard (Rep.res H.subtype A)).hom.f n c)) g = _
  rw [cochainsIsoStandard_inv_apply, homTransfer_apply]
  apply Finset.sum_congr rfl
  intro q _
  change A.ρ q.out
    (((cochainsIsoStandard (Rep.res H.subtype A)).hom.f n c).hom
      ((standardCosetComparisonComponent H n).hom
        (Representation.ofMulAction R G (Fin (n + 1) → G) q.out⁻¹
          (MonoidAlgebra.single (Fin.partialProd g) 1)))) = _
  rw [Representation.ofMulAction_single, standardCosetComparisonComponent_single,
    cochainsIsoStandard_hom_single, one_smul]
  have hzero : cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 0) = 1 := by
    rw [Fin.partialProd_zero, mul_one, cosetCoordinate_inverse_out]
  change A.ρ q.out
    ((Rep.res H.subtype A).ρ (cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 0))
      (c (transferTuple H n g q))) = _
  rw [hzero, map_one, Module.End.one_apply]

/-- Transfer on actual 2-cocycles, expressed in pair coordinates. -/
def ordinaryCorestrictionCocycle₂ (A : Rep.{u} R G) :
    ModuleCat.of R (groupCohomology.cocycles₂ (Rep.res H.subtype A)) ⟶
      ModuleCat.of R (groupCohomology.cocycles₂ A) :=
  (groupCohomology.isoCocycles₂ (Rep.res H.subtype A)).inv ≫
    HomologicalComplex.cyclesMap (ordinaryCorestrictionCochainMap H A) 2 ≫
      (groupCohomology.isoCocycles₂ A).hom

theorem ordinaryCorestrictionCohomology_H2π (A : Rep.{u} R G) :
    groupCohomology.H2π (Rep.res H.subtype A) ≫ ordinaryCohomologyCorestriction H A 2 =
      ordinaryCorestrictionCocycle₂ H A ≫ groupCohomology.H2π A := by
  simp only [groupCohomology.H2π, ordinaryCohomologyCorestriction,
    ordinaryCorestrictionCocycle₂, Category.assoc, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.homologyπ_naturality]

theorem ordinaryCorestrictionCocycle₂_apply (A : Rep.{u} R G)
    (c : groupCohomology.cocycles₂ (Rep.res H.subtype A)) (s t : G) :
    ordinaryCorestrictionCocycle₂ H A c (s, t) =
      ∑ q : G ⧸ H, A.ρ q.out
        (c (piFinTwoEquiv (fun _ => H) (transferTuple H 2
          ((piFinTwoEquiv (fun _ => G)).symm (s, t)) q))) := by
  let B := Rep.res H.subtype A
  let F := ordinaryCorestrictionCochainMap H A
  have hi (d : groupCohomology.cocycles B 2) :
      groupCohomology.iCocycles A 2 (HomologicalComplex.cyclesMap F 2 d) =
        F.f 2 (groupCohomology.iCocycles B 2 d) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i F 2) d
  change ((groupCohomology.isoCocycles₂ A).hom
    (HomologicalComplex.cyclesMap F 2 ((groupCohomology.isoCocycles₂ B).inv c)) : G × G → A)
      (s, t) = _
  rw [show (((groupCohomology.isoCocycles₂ A).hom
      (HomologicalComplex.cyclesMap F 2 ((groupCohomology.isoCocycles₂ B).inv c))) :
        G × G → A) = (groupCohomology.cochainsIso₂ A).hom
          (groupCohomology.iCocycles A 2
            (HomologicalComplex.cyclesMap F 2 ((groupCohomology.isoCocycles₂ B).inv c))) from
    groupCohomology.isoCocycles₂_hom_comp_i_apply A _]
  rw [hi, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  change F.f 2 (fun i => c (piFinTwoEquiv (fun _ => H) i))
    ((piFinTwoEquiv (fun _ => G)).symm (s, t)) = _
  exact ordinaryCorestrictionCochainMap_apply H A 2 _ _

end Langlands.Tate

namespace Langlands.ClassFieldTheory.Local

open Langlands.Tate

variable (K : Type v) (L : Type w) (M : Type u)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

local notation "G" => Gal(M/K)
local notation "H" => relativeGaloisSubgroup K L M
local notation "A" => unitsRepresentation K M
local notation "B" => unitsRepresentation L M
local notation "B'" => Rep.res (Subgroup.subtype H) A
local notation "e" => relativeGaloisSubgroupEquiv K L M

private theorem transferTuple_pair (s t : G) (q : G ⧸ H) :
    piFinTwoEquiv (fun _ => H) (transferTuple H 2
      ((piFinTwoEquiv (fun _ => G)).symm (s, t)) q) =
        (schreierElement H s q, schreierElement H t (s⁻¹ • q)) := by
  let g := (piFinTwoEquiv (fun _ => G)).symm (s, t)
  have hp₁ : Fin.partialProd g (1 : Fin 3) = s := by
    have hs := Fin.partialProd_succ g (0 : Fin 2)
    change Fin.partialProd g 1 = Fin.partialProd g 0 * s at hs
    simpa only [Fin.partialProd_zero, one_mul] using hs
  have hp₂ : Fin.partialProd g (2 : Fin 3) = s * t := by
    have hs := Fin.partialProd_succ g (1 : Fin 2)
    change Fin.partialProd g 2 = Fin.partialProd g 1 * t at hs
    simpa only [hp₁] using hs
  apply Prod.ext
  · change (cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 0))⁻¹ *
        cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 1) = _
    rw [Fin.partialProd_zero, mul_one, hp₁, cosetCoordinate_inverse_out,
      inv_one, one_mul, cosetCoordinate_inverse_out_mul]
  · change (cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 1))⁻¹ *
        cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 2) = _
    rw [hp₁, hp₂, cosetCoordinate_inverse_out_mul, cosetCoordinate_inverse_out_mul,
      show schreierElement H (s * t) q = schreierElement H s q *
          schreierElement H t (s⁻¹ • q) from by
        apply Subtype.ext
        change q.out⁻¹ * (s * t) * ((s * t)⁻¹ • q).out =
          (q.out⁻¹ * s * (s⁻¹ • q).out) * ((s⁻¹ • q).out⁻¹ * t * (t⁻¹ • (s⁻¹ • q)).out)
        rw [mul_inv_rev, mul_smul]
        group, inv_mul_cancel_left]

private def subgroupCoefficient : Rep.res (e).symm.toMonoidHom B ⟶ B' :=
  Rep.ofHom ⟨LinearMap.id, fun h => by
    ext x
    change (B).ρ ((e).symm h) x = (B').ρ h x
    conv_rhs => rw [← (e).apply_symm_apply h]
    rfl⟩

private theorem subgroupCohomology_H2π
    (c : groupCohomology.cocycles₂ B) :
    (relativeSubgroupCohomologyIso K L M 2).hom (groupCohomology.H2π B c) =
      groupCohomology.H2π B' (groupCohomology.mapCocycles₂ (e).symm.toMonoidHom
        (subgroupCoefficient K L M) c) := by
  exact groupCohomology.H2π_comp_map_apply (e).symm.toMonoidHom
    (subgroupCoefficient K L M) c

variable [FiniteDimensional K M]

/-- The actual relative transfer on degree-two cocycles over a tower of fields. -/
def relativeTransferCocycle₂ (c : groupCohomology.cocycles₂ B) :
    groupCohomology.cocycles₂ A := by
  letI := Fintype.ofFinite (G ⧸ H)
  exact ordinaryCorestrictionCocycle₂ H A
    (groupCohomology.mapCocycles₂ (e).symm.toMonoidHom (subgroupCoefficient K L M) c)

/-- Relative corestriction sends a class to the class of its transferred cocycle. -/
theorem relativeCorestriction_H2π (c : groupCohomology.cocycles₂ B) :
    relativeCorestriction K L M 2 (groupCohomology.H2π B c) =
      groupCohomology.H2π A (relativeTransferCocycle₂ K L M c) := by
  let : Fintype G := Fintype.ofFinite _
  let : Fintype H := Fintype.ofFinite _
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have ht : ModuleCat.ofHom (relativeCorestriction K L M 2) =
      (relativeSubgroupCohomologyIso K L M 2).hom ≫ ordinaryCohomologyCorestriction H A 2 := by
    let cA := (TateCohomology.isoGroupCohomology 2).app A
    let cB := (TateCohomology.isoGroupCohomology 2).app B'
    change (relativeSubgroupCohomologyIso K L M 2).hom ≫
      cB.inv ≫ ModuleCat.ofHom (corestriction H A ((2 : ℕ) : ℤ)) ≫ cA.hom = _
    rw [corestriction_groupCohomology H A 2]
    change _ ≫ cB.inv ≫ (cB.hom ≫ ordinaryCohomologyCorestriction H A 2 ≫ cA.inv) ≫
      cA.hom = _
    simp only [Category.assoc, cB.inv_hom_id_assoc, cA.inv_hom_id]
    exact congrArg (fun f => (relativeSubgroupCohomologyIso K L M 2).hom ≫ f)
      (Category.comp_id (ordinaryCohomologyCorestriction H A 2))
  have h := ConcreteCategory.congr_hom ht (groupCohomology.H2π B c)
  change relativeCorestriction K L M 2 (groupCohomology.H2π B c) =
    ordinaryCohomologyCorestriction H A 2
    ((relativeSubgroupCohomologyIso K L M 2).hom (groupCohomology.H2π B c)) at h
  rw [h, subgroupCohomology_H2π]
  exact ConcreteCategory.congr_hom (ordinaryCorestrictionCohomology_H2π H A) _

/-- The transferred unit-valued cocycle is the product of the conjugated Schreier factors. -/
theorem relativeTransferCocycle₂_apply (c : groupCohomology.cocycles₂ B) (s t : G) :
    letI := Fintype.ofFinite (G ⧸ H)
    @Additive.toMul Mˣ (relativeTransferCocycle₂ K L M c (s, t)) =
      ∏ q : G ⧸ H, q.out • @Additive.toMul Mˣ
        (c ((e).symm (schreierElement H s q), (e).symm (schreierElement H t (s⁻¹ • q)))) := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  change @Additive.toMul Mˣ (ordinaryCorestrictionCocycle₂ H A
    (groupCohomology.mapCocycles₂ (e).symm.toMonoidHom (subgroupCoefficient K L M) c) (s, t)) = _
  rw [ordinaryCorestrictionCocycle₂_apply, toMul_sum]
  apply Finset.prod_congr rfl
  intro q _
  rw [transferTuple_pair K L M]
  rfl

end Langlands.ClassFieldTheory.Local
