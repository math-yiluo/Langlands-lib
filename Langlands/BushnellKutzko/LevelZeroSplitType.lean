import Langlands.BushnellKutzko.LatticeChainLayers
import Langlands.BushnellKutzko.PairConjugation
import Langlands.Representation.FiniteGeneralLinear.Cuspidal

/-! # Split types of level `(0, 0)` -/

open IsLocalRing ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uV uW

namespace LatticeChain

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [IsLocalRing O] [Field F]
  [Algebra O F] [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
  (L : LatticeChain O F V)

private def layerEndomorphism (i : ℤ) : L.order →* Module.End (ResidueField O) (L.Layer i) where
  toFun a := (L.layerAction a i).extendScalarsOfSurjective residue_surjective
  map_one' := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := L.intervalMk_surjective i (i + 1) q
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := L.intervalMk_surjective i (i + 1) q
    rfl

private def unitFiltrationZeroEquiv : L.unitFiltration 0 ≃* L.orderˣ :=
  (MulEquiv.subgroupCongr (show L.unitFiltration 0 = L.order.toSubmonoid.units by
    ext g
    exact L.mem_unitFiltration_zero)).trans L.order.toSubmonoid.unitsEquivUnitsType

/-- The reduction of `U(𝔄)` by its action on all the successive layers in one period,
in the supplied residue-field bases. The ranks of the layers may vary. -/
def layerReduction {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (L.Layer (i : ℕ))) :
    L.unitFiltration 0 →* (∀ i, GeneralLinear (d i) (ResidueField O)) :=
  MonoidHom.pi fun i =>
    (Matrix.GeneralLinearGroup.toLin' (b i)).symm.toMonoidHom.comp
      ((Units.map (L.layerEndomorphism (i : ℕ))).comp L.unitFiltrationZeroEquiv.toMonoidHom)

theorem layerReduction_spec {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (L.Layer (i : ℕ)))
    (g : L.unitFiltration 0) (i : Fin L.period) (v : V) (hv : v ∈ L.lattice (i : ℕ)) :
    (Matrix.GeneralLinearGroup.toLin' (b i) (L.layerReduction b g i)).toLinearEquiv
      (L.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) v hv) =
    L.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) ((g.1 : Module.End F V) v)
      (L.mem_order.mp g.2.1 _ _ hv) := by
  change (Matrix.GeneralLinearGroup.toLin' (b i)
    ((Matrix.GeneralLinearGroup.toLin' (b i)).symm
      (Units.map (L.layerEndomorphism (i : ℕ)) (L.unitFiltrationZeroEquiv g)))).toLinearEquiv _ = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- A choice of bases and irreducible cuspidal factors for the successive layers of `L`. -/
structure CuspidalLayerData where
  rank : Fin L.period → ℕ
  dim : Fin L.period → ℕ
  basis : ∀ i, Module.Basis (Fin (rank i)) (ResidueField O) (L.Layer (i : ℕ))
  factor : ∀ i, Representation ℂ (GeneralLinear (rank i) (ResidueField O)) (Fin (dim i) → ℂ)
  cuspidal : ∀ i, (factor i).IsIrreducible ∧ FiniteGeneralLinear.IsCuspidal (factor i)

namespace CuspidalLayerData

variable {L} (a : L.CuspidalLayerData)

/-- The rank and isomorphism class of the factor at a layer. -/
def factorClass (i : Fin L.period) :
    Σ d : ℕ, FiniteGeneralLinear.CuspidalClass.{uO, 0} d (ResidueField O) :=
  ⟨a.rank i, (FiniteGeneralLinear.CuspidalRep.of (a.factor i)
    (a.cuspidal i).1 (a.cuspidal i).2).isoClass⟩

/-- The external tensor product of the factors, inflated along the layer action of `U(𝔄)`. -/
def inflation :
    Representation ℂ (L.unitFiltration 0) (PiTensorProduct ℂ fun i => Fin (a.dim i) → ℂ) :=
  (PiTensorProduct.mapMonoidHom.comp (MonoidHom.piMap a.factor)).comp (L.layerReduction a.basis)

end CuspidalLayerData
end LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **BK93 (8.1.2).** A split type of level `(0, 0)` comes from a hereditary order
whose unit group acts by inflation of an inhomogeneous tensor of irreducible cuspidal factors. -/
def IsLevelZeroSplitType {K : Subgroup (Module.End F V)ˣ} (ρ : Representation ℂ K W) : Prop :=
  ∃ (L : LatticeChain 𝒪[F] F V) (a : L.CuspidalLayerData),
    (∃ i j, a.factorClass i ≠ a.factorClass j) ∧
    (∀ k : K, (k : (Module.End F V)ˣ) ∈ L.unitFiltration 1 → ρ k = 1) ∧
    IsPairIsomorphic ρ a.inflation

end Langlands.BushnellKutzko
