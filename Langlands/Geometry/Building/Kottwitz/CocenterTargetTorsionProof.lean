import Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionReduction
import Langlands.Geometry.Building.Kottwitz.TorusTargetFundamentalMap

/-!
# Torsion kernel of the cocenter inertia map

This module proves `CocenterTargetTorsionStatement` without hypotheses
(KP Lemma 11.5.2, torsion-kernel input). It follows the conditional reduction
`cocenterTargetTorsion_of_statements` of `CocenterTargetTorsionReduction`, but replaces
the two hypotheses there by the unconditional torus-target lemmas of
`TorusTargetFundamentalMap`: `Choice.comparison_self_of_isTorus`,
`Choice.isInducedMap_mapTo_of_isTorus` and `Choice.mapTo_galois_of_isTorus`.
The lemmas below are the torus-target versions (suffix `_of_isTorus`) of the
corresponding lemmas of the reduction module.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section TorusTarget

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [Normal k K]

/-- The selection law of the induced inertia map into a torus. -/
theorem fundamentalInertiaMap_spec_of_isTorus
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (f : G ⟶ T.toGrp) :
    IsFundamentalInertiaMap k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting G hG f
      (fundamentalInertiaMap k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting G hG f) :=
  Classical.epsilon_spec ⟨Representation.Coinvariants.map _ _
    { toLinearMap := fundamentalGroupMap k E G T.toGrp hG
        hT.isConnectedReductive_of_fieldSplitting f
      isIntertwining' := fun σ => LinearMap.ext fun x =>
        Choice.mapTo_galois_of_isTorus E hT (chosenChoice k G hG)
          (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting) f σ.val x },
    fun _ => rfl⟩

end TorusTarget

section CocenterFundamental

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (c : Cocenter k G) (E : Type u) [Field E] [Algebra k E]

/-- On representatives, the fundamental cocharacter map is the cocharacter map of the
restriction `T → D` of the cocenter quotient. -/
theorem Cocenter.fundamentalCocharacterMap_projection_of_isTorus
    (ν : (chosenChoice k G hG).lattice E) :
    c.fundamentalCocharacterMap hG E ((chosenChoice k G hG).projection E ν) =
      c.torusCocharacterMap (chosenChoice k G hG) E ν := by
  let a := chosenChoice k G hG
  let hD := c.isTorus.isConnectedReductive_of_fieldSplitting
  let b := chosenChoice k c.torus.toGrp hD
  let BC := CommGroupScheme.baseChange (algebraBaseMap k E)
  let : IsIso b.inclusion := b.isMaximal.isIso_of_torus c.isTorus
  let d : a.torus ⟶ b.torus := Additive.ofMul (a.inclusion ≫ c.quotient ≫ inv b.inclusion)
  have hd : d ≫ (Additive.ofMul b.inclusion : b.torus ⟶ c.torus) = c.torusMap a := by
    change Additive.ofMul ((a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫ b.inclusion) =
      Additive.ofMul (a.inclusion ≫ c.quotient)
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hf : a.IsTorusFactorization E b c.quotient (BC.map d) := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.quotient =
      (GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hm := (Choice.isInducedMap_mapTo_of_isTorus E c.isTorus a b c.quotient).2 b _ hf ν
  rw [Choice.comparison_self_of_isTorus E c.isTorus b, LinearMap.id_apply] at hm
  change torusFundamentalComparison k E c.torus c.isTorus
    (a.mapTo E b c.quotient (a.projection E ν)) = _
  rw [hm, torusFundamentalComparison_spec k E c.torus c.isTorus]
  change (ν ≫ BC.map d) ≫ BC.map (Additive.ofMul b.inclusion) = ν ≫ BC.map (c.torusMap a)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hd]

/-- The fundamental cocharacter map is Galois equivariant. -/
theorem Cocenter.fundamentalCocharacterMap_galois_of_isTorus (σ : E ≃ₐ[k] E)
    (x : fundamentalGroup k G E hG) :
    c.fundamentalCocharacterMap hG E (fundamentalGroupGalois k G E hG σ x) =
      cocharacterLattice.galoisRepresentation k E c.torus σ
        (c.fundamentalCocharacterMap hG E x) := by
  change torusFundamentalComparison k E c.torus c.isTorus
      (fundamentalGroupMap k E G c.torus.toGrp hG
        c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient
        (fundamentalGroupGalois k G E hG σ x)) = _
  rw [show fundamentalGroupMap k E G c.torus.toGrp hG
        c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient
        (fundamentalGroupGalois k G E hG σ x) =
      fundamentalGroupGalois k c.torus.toGrp E
        c.isTorus.isConnectedReductive_of_fieldSplitting σ
        (fundamentalGroupMap k E G c.torus.toGrp hG
          c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient x) from
    Choice.mapTo_galois_of_isTorus E c.isTorus (chosenChoice k G hG)
      (chosenChoice k c.torus.toGrp c.isTorus.isConnectedReductive_of_fieldSplitting)
      c.quotient σ x]
  exact torusFundamentalComparison_galois k E c.torus c.isTorus σ _

end CocenterFundamental

section SeparableClosure

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (c : Cocenter k G)

/-- Over the separable closure the fundamental cocharacter map is surjective. -/
theorem Cocenter.fundamentalCocharacterMap_surjective_of_isTorus :
    Function.Surjective (c.fundamentalCocharacterMap hG (SeparableClosure k)) := by
  intro w
  obtain ⟨ν, rfl⟩ := c.torusCocharacterMap_surjective (chosenChoice k G hG) w
  exact ⟨_, c.fundamentalCocharacterMap_projection_of_isTorus hG (SeparableClosure k) ν⟩

/-- Over the separable closure the fundamental cocharacter map has torsion kernel. -/
theorem Cocenter.fundamentalCocharacterMap_torsion_of_isTorus
    (x : fundamentalGroup k G (SeparableClosure k) hG)
    (hx : c.fundamentalCocharacterMap hG (SeparableClosure k) x = 0) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  let a := chosenChoice k G hG
  obtain ⟨ν, rfl⟩ := (a.corootImage (SeparableClosure k)).mkQ_surjective x
  change c.fundamentalCocharacterMap hG (SeparableClosure k)
    (a.projection (SeparableClosure k) ν) = 0 at hx
  rw [c.fundamentalCocharacterMap_projection_of_isTorus hG (SeparableClosure k)] at hx
  obtain ⟨n, hn, hmem⟩ := c.exists_pos_smul_mem_corootImage a ν hx
  refine ⟨n.toNat, by omega, ?_⟩
  have hsmul : n.toNat • ν = n • ν := by
    rw [← natCast_zsmul, Int.toNat_of_nonneg hn.le]
  rw [← map_nsmul, hsmul]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

end SeparableClosure

/-- KP Lemma 11.5.2, torsion-kernel input: the cocenter inertia map has torsion kernel. -/
theorem cocenterTargetTorsion_proof : CocenterTargetTorsionStatement.{u} := by
  intro F _ _ _ _ G hG c y hy
  let K := UnramifiedClosure F
  let E := SeparableClosure F
  let hD := c.isTorus.isConnectedReductive_of_fieldSplitting
  rw [MonoidHom.mem_ker] at hy
  have h0 : cocenterTargetMap F F G hG c (Multiplicative.toAdd y) = 0 :=
    congrArg Multiplicative.toAdd hy
  have hφ : ∀ x, cocenterTargetMap F F G hG c (fundamentalInertiaProjection F K E G hG x) =
      inertiaProjection F K E (cocharacterLattice.galoisRepresentation F E c.torus)
        (c.fundamentalCocharacterMap hG E x) := by
    intro x
    change torusInertiaComparison F K E c.torus c.isTorus
      (fundamentalInertiaMap F K E c.torus.toGrp hD G hG c.quotient
        (fundamentalInertiaProjection F K E G hG x)) = _
    rw [fundamentalInertiaMap_spec_of_isTorus F K E G hG c.torus c.isTorus c.quotient x,
      torusInertiaComparison_spec F K E c.torus c.isTorus]
    rfl
  obtain ⟨n, hn, hny⟩ := coinvariants_exists_nsmul_eq_zero
    (c.fundamentalCocharacterMap hG E)
    (c.fundamentalCocharacterMap_surjective_of_isTorus hG)
    (fun σ x => c.fundamentalCocharacterMap_galois_of_isTorus hG E σ.val x)
    (c.fundamentalCocharacterMap_torsion_of_isTorus hG)
    (cocenterTargetMap F F G hG c) hφ (Multiplicative.toAdd y) h0
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact hny

end Langlands.Geometry.Building.Kottwitz
