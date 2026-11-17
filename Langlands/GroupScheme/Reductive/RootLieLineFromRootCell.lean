import Langlands.GroupScheme.Dynamic.NormalSubgroupProduct
import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.Rational.MonicRootParametrization
import Langlands.GroupScheme.Lie.TorusRegularElement
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Root Lie lines from independently supplied rank-one root cells -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace RootCellLie

section OpenCell

variable {R : CommRingCat.{u}} {G M Z U : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  [IsAffineHom Z.X.hom] [IsAffineHom U.X.hom]
  (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)
  [IsOpenImmersion (Dynamic.tripleCellMultiplication iM iZ iU).left]

/-- Every actual tangent vector splits into the three subgroup tangents in an
open multiplication chart around the identity. -/
theorem exists_lie_decomposition (A : Type u) [CommRing A] [Algebra R A]
    (X : Additive (lieKernel G A)) :
    ∃ (m : Additive (lieKernel M A)) (z : Additive (lieKernel Z A))
      (p : Additive (lieKernel U A)),
      X = Lie.targetMapLinear iM A m + Lie.targetMapLinear iZ A z +
        Lie.targetMapLinear iU A p := by
  let c := Dynamic.tripleCellMultiplication iM iZ iU
  let y₀ : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ M.X ⊗ (Z.X ⊗ U.X) :=
    lift 1 (lift 1 1)
  have hred : (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      X.toMul.val = y₀ ≫ c := by
    calc
      _ = 1 := X.toMul.property
      _ = _ := by
        simp only [y₀, c, Dynamic.lift_tripleCellMultiplication, MonObj.one_comp, one_mul]
  obtain ⟨y, hy, hyr⟩ :=
    Lie.exists_dualNumberLift_of_openImmersion A c X.toMul.val y₀ hred
  let m : Lie.AffinePoints M (DualNumber A) := y ≫ fst _ _
  let z : Lie.AffinePoints Z (DualNumber A) := y ≫ snd _ _ ≫ fst _ _
  let p : Lie.AffinePoints U (DualNumber A) := y ≫ snd _ _ ≫ snd _ _
  have hm : Lie.reduction M m = 1 := by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      (y ≫ fst _ _) = 1
    rw [← Category.assoc, hyr]
    exact lift_fst _ _
  have hz : Lie.reduction Z z = 1 := by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      (y ≫ snd _ _ ≫ fst _ _) = 1
    rw [← Category.assoc, hyr]
    simp only [y₀, lift_snd_assoc, lift_fst]
  have hp : Lie.reduction U p = 1 := by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      (y ≫ snd _ _ ≫ snd _ _) = 1
    rw [← Category.assoc, hyr]
    simp only [y₀, lift_snd_assoc, lift_snd]
  refine ⟨Additive.ofMul ⟨m, hm⟩, Additive.ofMul ⟨z, hz⟩,
    Additive.ofMul ⟨p, hp⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val = ((m ≫ iM.hom.hom) * (z ≫ iZ.hom.hom)) * (p ≫ iU.hom.hom)
  simpa only [c, Dynamic.tripleCellMultiplication, MonObj.comp_mul,
    Category.assoc, SubgroupFunctor.cellMultiplication, m, z, p, mul_assoc] using hy.symm

end OpenCell

private theorem weightPointAction_scalar {R : CommRingCat.{u}}
    {T : CommGroupScheme (Spec R)} (χ : characterLattice T)
    (V : Over (Spec R)) (t : V ⟶ T.X) (a : Γ(V.left, ⊤)) :
    VectorGroup.weightPointAction χ V t (VectorGroup.scalarPoint R V a) =
      VectorGroup.scalarPoint R V (VectorGroup.charValue χ V t * a) := by
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_weightPointAction, Pi.smul_apply, smul_eq_mul,
    VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint]

section Weight

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  {α : characterLattice T} (hα : α ≠ 0)
  (xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
  (hp : ∀ (V : Over (Spec (CommRingCat.of k)))
    (t : V ⟶ T.X) (a : V ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
    (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction α V t a ≫ xp.hom.hom)
  (hm : ∀ (V : Over (Spec (CommRingCat.of k)))
    (t : V ⟶ T.X) (a : V ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
    (t ≫ i.hom.hom) * (a ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction (-α) V t a ≫ xm.hom.hom)
  (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme _ _

include hT hα hp hm hopen

/-- A nonzero weight in an equivariant open line-torus-line cell is exactly
the differential image of its positive line factor. -/
theorem weightSpace_eq_range :
    weightSpace i α = LinearMap.range (Lie.targetMapLinear xp k) := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let := hopen
  have hp' : VectorGroup.IsTorusEquivariant i xp α := by
    intro V t a
    simpa only [weightPointAction_scalar] using
      hp V t (VectorGroup.scalarPoint _ V a)
  have hm' : VectorGroup.IsTorusEquivariant i xm (-α) := by
    intro V t a
    simpa only [weightPointAction_scalar] using
      hm V t (VectorGroup.scalarPoint _ V a)
  have hpw := hp'.lie_range_le_weightSpace
  have hmw := hm'.lie_range_le_weightSpace
  have hneg : -α ≠ α := by
    intro h
    have hh : α + α = 0 := by
      calc
        α + α = -α + α := congrArg (fun b => b + α) h.symm
        _ = 0 := neg_add_cancel α
    exact hT.nsmul_ne_zero hα (by decide : (2 : ℕ) ≠ 0) (by
      simpa only [two_nsmul] using hh)
  have hind := (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep
  have hd : Disjoint (weightSpace i α) (weightSpace i (-α) ⊔ weightSpace i 0) :=
    (hind α).mono_right (sup_le
      (le_iSup₂ (f := fun β (_ : β ≠ α) => weightSpace i β) (-α) hneg)
      (le_iSup₂ (f := fun β (_ : β ≠ α) => weightSpace i β) 0 (Ne.symm hα)))
  apply le_antisymm
  · intro X hX
    obtain ⟨m, z, p, he⟩ := exists_lie_decomposition xm i xp k X
    have hmp : Lie.targetMapLinear xm k m ∈ weightSpace i (-α) := hmw ⟨m, rfl⟩
    have hzp : Lie.targetMapLinear i k z ∈ weightSpace i 0 :=
      Lie.targetMap_mem_weightSpace_zero i z.toMul
    have hpp : Lie.targetMapLinear xp k p ∈ weightSpace i α := hpw ⟨p, rfl⟩
    have hsum : Lie.targetMapLinear xm k m + Lie.targetMapLinear i k z ∈
        weightSpace i α := by
      have hsub := (weightSpace i α).sub_mem hX hpp
      rw [he, add_sub_cancel_right] at hsub
      exact hsub
    have hsum' : Lie.targetMapLinear xm k m + Lie.targetMapLinear i k z ∈
        weightSpace i (-α) ⊔ weightSpace i 0 :=
      Submodule.add_mem_sup hmp hzp
    have hzero := (Submodule.disjoint_def.mp hd) _ hsum hsum'
    exact ⟨p, by rw [he, hzero, zero_add]⟩
  · exact hpw

/-- A nonzero actual weight space in the supplied cell has dimension one. -/
theorem finrank_weightSpace_eq_one (hne : weightSpace i α ≠ ⊥) :
    Module.finrank k (weightSpace i α) = 1 := by
  let E := RelativeRoot.vectorLieCoordinates
    (VectorGroup.coordinates (CommRingCat.of k) 1)
    VectorGroup.isNaturalVectorCoordinates (CommAlgCat.of k k)
  have : Module.Finite k
      (Additive (lieKernel (VectorGroup.groupScheme (CommRingCat.of k) 1) k)) :=
    Module.Finite.equiv E.symm
  have hle : Module.finrank k (weightSpace i α) ≤ 1 := by
    rw [weightSpace_eq_range hT i hα xp xm hp hm hopen]
    have h := LinearMap.finrank_range_le (Lie.targetMapLinear xp k)
    rw [E.finrank_eq] at h
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using h
  let : Nontrivial (weightSpace i α) := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < Module.finrank k (weightSpace i α) := Module.finrank_pos
  omega

/-- A linear trivialization of the nonzero weight space from the supplied cell. -/
def lineEquiv (hne : weightSpace i α ≠ ⊥) :
    k ≃ₗ[k] weightSpace i α :=
  Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_weightSpace_eq_one hT i hα xp xm hp hm hopen hne))

end Weight
end RootCellLie
end Langlands.GroupScheme
