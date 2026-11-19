import Langlands.GroupScheme.SimplyConnected.StarFixedWeights
import Langlands.GroupScheme.Reductive.GaloisPinningBaseChange
import Langlands.GroupScheme.Reductive.InnerStarWeights

/-! # Star-fixed weights: comparison with `IsStarFixedWeight` and base change -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k K G)

/-! ## Comparison with `IsStarFixedWeight` -/

/-- Membership in `starFixedWeights` is the Library predicate `IsStarFixedWeight`. -/
theorem mem_starFixedWeights_iff_isStarFixedWeight
    (lam : characterLattice d.toSplitPinning.torus) :
    lam ∈ d.starFixedWeights ↔ d.IsStarFixedWeight lam :=
  d.mem_starFixedWeights lam

/-- The carrier of `starFixedWeights` is the set of weights satisfying `IsStarFixedWeight`. -/
theorem coe_starFixedWeights :
    (d.starFixedWeights : Set (characterLattice d.toSplitPinning.torus)) =
      {lam | d.IsStarFixedWeight lam} :=
  Set.ext d.mem_starFixedWeights_iff_isStarFixedWeight

/-- For a simply connected group whose star action fixes every simple vertex, every integral
weight is star fixed. -/
theorem starFixedWeights_eq_top_of_inner (hG : IsSimplyConnected G)
    (hinner : d.IsInnerStarAction) : d.starFixedWeights = ⊤ :=
  eq_top_iff.mpr fun lam _ =>
    (d.mem_starFixedWeights_iff_isStarFixedWeight lam).mpr
      (d.isStarFixedWeight_of_inner hG hinner lam)

/-! ## Base change to an intermediate field -/

variable (F : IntermediateField k K)

/-- A weight of `d` is fixed by the star action of `Gal(K/F)` exactly when its transport is a
star-fixed weight of the base change of `d` to `F`. -/
theorem weightTransport_mem_starFixedWeights_iff
    (lam : characterLattice d.toSplitPinning.torus) :
    d.weightTransport F lam ∈ (d.baseChange F).starFixedWeights ↔
      lam ∈ d.fixedWeights F.fixingSubgroup :=
  ((d.baseChange F).mem_starFixedWeights _).trans
    (d.forall_fixingSubgroup_starAction_iff F lam).symm

/-- The inverse weight transport of a star-fixed weight of the base change is fixed by the
star action of `Gal(K/F)`. -/
theorem weightTransport_symm_mem_fixedWeights_iff
    (mu : characterLattice (d.baseChange F).toSplitPinning.torus) :
    (d.weightTransport F).symm mu ∈ d.fixedWeights F.fixingSubgroup ↔
      mu ∈ (d.baseChange F).starFixedWeights := by
  rw [← d.weightTransport_mem_starFixedWeights_iff F, LinearEquiv.apply_symm_apply]

/-- A star-fixed weight of `d` transports to a star-fixed weight of every base change. -/
theorem weightTransport_mem_starFixedWeights {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.starFixedWeights) :
    d.weightTransport F lam ∈ (d.baseChange F).starFixedWeights :=
  (d.weightTransport_mem_starFixedWeights_iff F lam).mpr
    (d.starFixedWeights_le_fixedWeights F.fixingSubgroup hlam)

/-- The weight transport maps the weights fixed by `Gal(K/F)` onto the star-fixed weights of
the base change to `F`. -/
theorem map_fixedWeights_fixingSubgroup :
    (d.fixedWeights F.fixingSubgroup).map (d.weightTransport F).toLinearMap.toAddMonoidHom =
      (d.baseChange F).starFixedWeights := by
  ext mu
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact (d.weightTransport_mem_starFixedWeights_iff F lam).mpr hlam
  · intro hmu
    exact ⟨(d.weightTransport F).symm mu,
      (d.weightTransport_symm_mem_fixedWeights_iff F mu).mpr hmu,
      (d.weightTransport F).apply_symm_apply mu⟩

/-- The additive equivalence between the weights of `d` fixed by `Gal(K/F)` and the
star-fixed weights of the base change of `d` to `F`, given by the weight transport. -/
def fixedWeightsBaseChangeEquiv :
    d.fixedWeights F.fixingSubgroup ≃+ (d.baseChange F).starFixedWeights where
  toFun lam := ⟨d.weightTransport F lam,
    (d.weightTransport_mem_starFixedWeights_iff F lam).mpr lam.2⟩
  invFun mu := ⟨(d.weightTransport F).symm mu,
    (d.weightTransport_symm_mem_fixedWeights_iff F mu).mpr mu.2⟩
  left_inv lam := Subtype.ext ((d.weightTransport F).symm_apply_apply lam)
  right_inv mu := Subtype.ext ((d.weightTransport F).apply_symm_apply mu)
  map_add' a b := Subtype.ext ((d.weightTransport F).map_add a.1 b.1)

@[simp] theorem fixedWeightsBaseChangeEquiv_apply (lam : d.fixedWeights F.fixingSubgroup) :
    (d.fixedWeightsBaseChangeEquiv F lam : characterLattice (d.baseChange F).toSplitPinning.torus)
      = d.weightTransport F lam :=
  rfl

@[simp] theorem fixedWeightsBaseChangeEquiv_symm_apply
    (mu : (d.baseChange F).starFixedWeights) :
    ((d.fixedWeightsBaseChangeEquiv F).symm mu : characterLattice d.toSplitPinning.torus) =
      (d.weightTransport F).symm mu :=
  rfl

end Langlands.GroupScheme.GaloisPinningData
