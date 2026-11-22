import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # Reparametrization of the standard Levi models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

variable (M' : StandardIndex F G fam.i fam.ν → GroupScheme (Spec (CommRingCat.of F)))
  (e : ∀ J, M' J ≅ fam.M J) (dim : StandardIndex F G fam.i fam.ν → ℕ)
  (hs : ∀ J, SmoothOfRelativeDimension (dim J) (M' J).X.hom)

omit [NumberField F] in
private theorem reparametrized_torus_comp (J : StandardIndex F G fam.i fam.ν) :
    (fam.torus J ≫ (e J).inv) ≫ ((e J).hom ≫ fam.l J) ≫ fam.p J = fam.i := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using fam.torus_comp J

omit [NumberField F] in
include e in
private theorem reparametrized_levi_affine (J : StandardIndex F G fam.i fam.ν) :
    IsAffine (M' J).X.left := by
  let := ((fam.isCompatible J).levi.isConnectedReductive.of_iso (e J)).isAffineHom
  exact isAffine_of_isAffineHom (M' J).X.hom

omit [NumberField F] in
include e in
private theorem reparametrized_levi_finiteType (J : StandardIndex F G fam.i fam.ν) :
    LocallyOfFiniteType (M' J).X.hom := by
  let : Smooth (M' J).X.hom := ((fam.isCompatible J).levi.isConnectedReductive.of_iso (e J)).smooth
  infer_instance

/-- Use isomorphic models for the Levis of the same standard parabolics. -/
def reparametrizeLevi : StandardParabolicFamily F G where
  connectedReductive := fam.connectedReductive
  T := fam.T
  i := fam.i
  ν := fam.ν
  maximalSplit := fam.maximalSplit
  generic := fam.generic
  coroots := fam.coroots
  P := fam.P
  M := M'
  U := fam.U
  A := fam.A
  p := fam.p
  iU := fam.iU
  l J := (e J).hom ≫ fam.l J
  a J := fam.a J ≫ (e J).inv
  f := fam.f
  torus J := fam.torus J ≫ (e J).inv
  isCompatible J := (ParabolicRootPresentation.leviIsoComp
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ (e J)).isCompatible
  isUnipotentRadical := fam.isUnipotentRadical
  torus_comp := reparametrized_torus_comp fam M' e
  leviDim := dim
  leviSmooth := hs
  affineP := fam.affineP
  finiteTypeP := fam.finiteTypeP
  affineM := reparametrized_levi_affine fam M' e
  finiteTypeM := reparametrized_levi_finiteType fam M' e
  affineU := fam.affineU
  closedU := fam.closedU

local notation "other" => fam.reparametrizeLevi M' e dim hs

variable (J : StandardIndex F G fam.i fam.ν)

/-- The actual rational inducing quotient is independent of the Levi model. -/
theorem reparametrizeLevi_parabolicQuotientSubgroup :
    parabolicQuotientSubgroup F ((other).p J) ((other).iU J) ((other).l J) =
      parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J) := by
  apply parabolicQuotientSubgroup_eq_of_range_eq rfl
  change SubgroupFunctor.range (((e J).hom ≫ fam.l J) ≫ fam.p J) = _
  rw [Category.assoc, SubgroupFunctor.range_iso_comp]
  rfl

/-- The positive split component is unchanged as a subgroup of the parabolic. -/
theorem reparametrizeLevi_positiveSplitComponent :
    (other).positiveSplitComponent J = fam.positiveSplitComponent J := by
  unfold positiveSplitComponent
  change PositiveRealTorus.imageSubgroup F (fam.A J) (fam.P J)
    ((fam.a J ≫ (e J).inv) ≫ (e J).hom ≫ fam.l J) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Automorphy of an ambient inducing function is independent of the Levi model. -/
theorem reparametrizeLevi_isAutomorphicOn {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hG : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (φ : AdelicGroupPoints F G → ℂ) :
    (other).IsAutomorphicOn hG Kinf rho J φ ↔ fam.IsAutomorphicOn hG Kinf rho J φ := by
  simp only [IsAutomorphicOn, reparametrizeLevi_parabolicQuotientSubgroup]

/-- The unnormalized exponent on an ambient function is independent of the Levi model. -/
theorem reparametrizeLevi_hasUnnormalizedExponent
    (lam : ComplexCharacterParameter F (fam.P J)) (φ : AdelicGroupPoints F G → ℂ) :
    (other).HasUnnormalizedExponent J lam φ ↔ fam.HasUnnormalizedExponent J lam φ := by
  simp only [HasUnnormalizedExponent, unnormalizedAction, reparametrizeLevi_positiveSplitComponent]
  rfl

/-- Levi maximality of the fixed ambient compact is independent of the Levi model. -/
theorem reparametrizeLevi_isMaximalCompact (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) :
    IsMaximalCompactSubgroup F ((other).M J)
      (K.comap (map F ((other).M J) G ((other).l J ≫ (other).p J)).toMonoidHom) := by
  let a : AdelicGroupPoints F (M' J) ≃ₜ* AdelicGroupPoints F (fam.M J) :=
    { toFun := map F _ _ (e J).hom
      invFun := map F _ _ (e J).inv
      left_inv := fun x => by
        rw [← map_comp_apply_of_hom, Iso.hom_inv_id]
        change x ≫ 𝟙 (M' J).X = x
        exact Category.comp_id _
      right_inv := fun x => by
        rw [← map_comp_apply_of_hom, Iso.inv_hom_id]
        change x ≫ 𝟙 (fam.M J).X = x
        exact Category.comp_id _
      map_mul' := map_mul (map F _ _ (e J).hom)
      continuous_toFun := (map F _ _ (e J).hom).continuous
      continuous_invFun := (map F _ _ (e J).inv).continuous }
  have hMap := ((isMaximalCompactSubgroup_iff F _ _).mp hK).map a.symm
  apply (isMaximalCompactSubgroup_iff F _ _).mpr
  have hEq : K.comap (map F (M' J) G (((e J).hom ≫ fam.l J) ≫ fam.p J)).toMonoidHom =
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom).map a.symm.toMonoidHom := by
    apply Subgroup.ext
    intro x
    rw [Subgroup.mem_map_equiv]
    change map F (M' J) G (((e J).hom ≫ fam.l J) ≫ fam.p J) x ∈ K ↔
      map F (fam.M J) G (fam.l J ≫ fam.p J) (map F (M' J) (fam.M J) (e J).hom x) ∈ K
    rw [Category.assoc, map_comp_apply_of_hom]
  change CompactIwasawa.IsMaximalCompact
    (K.comap (map F (M' J) G (((e J).hom ≫ fam.l J) ≫ fam.p J)).toMonoidHom)
  rw [hEq]
  exact hMap

end Langlands.Global.StandardParabolicFamily
