import Langlands.BushnellKutzko.SubfieldLatticeChain
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic
import Langlands.BushnellKutzko.RefinementChainTransport
import Langlands.BushnellKutzko.LevelZeroSplitType
import Langlands.BushnellKutzko.PureStratumApproximationMoyTransport

/-! # The centralizer chain over the valuation ring of `E`

Let `𝓛` be an `𝔬_F`-lattice chain in `V` whose stabilizer contains `E^×`, for a field `E` over `F`
acting on `V`. Let `L_E = 𝓛.subfieldChain E hE` be the same chain over the integral closure `𝔬_E` of
`𝔬_F` in `E`. Given a valuative relation on `E` whose valuation ring `𝒪[E]` is identified with
`𝔬_E` by a ring isomorphism `φ` compatible with the inclusions into `E`, `centralizerChain` is the
same chain over `𝒪[E]` (`LatticeChain.transfer`). This module compares the two: the layers are
additively isomorphic (`layerEquivE`), semilinearly for the residue field isomorphism
`residueEquivE`; layer bases transport (`transportBasis`); the unit filtrations and the periods
agree; and the reduction of `g ∈ U(𝔅)` on a layer in a transported basis is the image of its
reduction over `𝔬_E` under `residueEquivE` (`layerReduction_transfer`). -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

variable [ValuativeRel E] [IsDiscreteValuationRing (subfieldIntegers F E)]
  (φ : subfieldIntegers F E ≃+* 𝒪[E]) (hφ : ∀ a, algebraMap 𝒪[E] E (φ a) = algebraMap _ E a)

variable (𝓛 : LatticeChain 𝒪[F] F V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- The centralizer chain as a lattice chain over the valuation ring of `E`. -/
def centralizerChain : LatticeChain 𝒪[E] E V :=
  (𝓛.subfieldChain E hE).transfer φ hφ

theorem mem_centralizerChain_lattice (i : ℤ) (v : V) :
    v ∈ (centralizerChain φ hφ 𝓛 hE).lattice i ↔ v ∈ 𝓛.lattice i := Iff.rfl

local notation "L_E" => 𝓛.subfieldChain E hE
local notation "C" => centralizerChain φ hφ 𝓛 hE

/-- The map of layers from the centralizer chain over the integral closure to the same chain
over the valuation ring of `E`. -/
def layerTransfer (i : ℤ) : (L_E).Layer i →+ (C).Layer i where
  toFun q := Quotient.liftOn' q (fun x => (C).intervalMk i (i + 1) x.1 x.2) (by
    intro a b hab
    have h := (Submodule.quotientRel_def _).mp hab
    exact ((C).intervalMk_eq_iff a.2 b.2).mpr h)
  map_zero' := rfl
  map_add' := by
    intro q r
    induction q using Submodule.Quotient.induction_on
    induction r using Submodule.Quotient.induction_on
    rfl

/-- The inverse map of layers. -/
def layerTransferInv (i : ℤ) : (C).Layer i →+ (L_E).Layer i where
  toFun q := Quotient.liftOn' q (fun x => (L_E).intervalMk i (i + 1) x.1 x.2) (by
    intro a b hab
    have h := (Submodule.quotientRel_def _).mp hab
    exact ((L_E).intervalMk_eq_iff a.2 b.2).mpr h)
  map_zero' := rfl
  map_add' := by
    intro q r
    induction q using Submodule.Quotient.induction_on
    induction r using Submodule.Quotient.induction_on
    rfl

theorem layerTransfer_intervalMk (i : ℤ) (v : V) (hv : v ∈ 𝓛.lattice i) :
    layerTransfer φ hφ 𝓛 hE i ((L_E).intervalMk i (i + 1) v hv) =
      (C).intervalMk i (i + 1) v hv := rfl

theorem layerTransferInv_intervalMk (i : ℤ) (v : V) (hv : v ∈ 𝓛.lattice i) :
    layerTransferInv φ hφ 𝓛 hE i ((C).intervalMk i (i + 1) v hv) =
      (L_E).intervalMk i (i + 1) v hv := rfl

/-- The additive equivalence of layers. -/
def layerEquivE (i : ℤ) : (L_E).Layer i ≃+ (C).Layer i where
  toFun := layerTransfer φ hφ 𝓛 hE i
  invFun := layerTransferInv φ hφ 𝓛 hE i
  left_inv q := by
    induction q using Submodule.Quotient.induction_on
    rfl
  right_inv q := by
    induction q using Submodule.Quotient.induction_on
    rfl
  map_add' := (layerTransfer φ hφ 𝓛 hE i).map_add

/-- The residue fields of the integral closure and of the valuation ring of `E`. -/
def residueEquivE : IsLocalRing.ResidueField (subfieldIntegers F E) ≃+* 𝓀[E] :=
  IsLocalRing.ResidueField.mapEquiv φ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem residueEquivE_residue (a : subfieldIntegers F E) :
    residueEquivE φ (IsLocalRing.residue _ a) = IsLocalRing.residue _ (φ a) := by
  simp [residueEquivE, IsLocalRing.ResidueField.map_residue]

theorem layerEquivE_smul (i : ℤ) (c : IsLocalRing.ResidueField (subfieldIntegers F E))
    (q : (L_E).Layer i) :
    layerEquivE φ hφ 𝓛 hE i (c • q) = residueEquivE φ c • layerEquivE φ hφ 𝓛 hE i q := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    rw [residueEquivE_residue, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsLocalRing.ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul,
      IsScalarTower.algebraMap_smul]
    change Submodule.Quotient.mk (⟨((a • x : (L_E).lattice i) : V), (a • x).2⟩ : (C).lattice i) =
      φ a • Submodule.Quotient.mk (⟨(x : V), x.2⟩ : (C).lattice i)
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change a • (x : V) = φ a • (x : V)
    rw [← algebraMap_smul E a (x : V), ← algebraMap_smul E (φ a) (x : V), hφ]

theorem layerEquivE_symm_smul (i : ℤ) (c : 𝓀[E]) (q : (C).Layer i) :
    (layerEquivE φ hφ 𝓛 hE i).symm (c • q) =
      (residueEquivE φ).symm c • (layerEquivE φ hφ 𝓛 hE i).symm q := by
  rw [AddEquiv.symm_apply_eq, layerEquivE_smul, RingEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-- A basis of a layer of the centralizer chain over the integral closure, transported to a
basis over the residue field of `E`. -/
def transportBasis {ι : Type*} (i : ℤ)
    (b : Module.Basis ι (IsLocalRing.ResidueField (subfieldIntegers F E)) ((L_E).Layer i)) :
    Module.Basis ι 𝓀[E] ((C).Layer i) :=
  Module.Basis.ofRepr
    { toFun := fun q => Finsupp.mapRange (residueEquivE φ) (map_zero _)
        (b.repr ((layerEquivE φ hφ 𝓛 hE i).symm q))
      invFun := fun f => layerEquivE φ hφ 𝓛 hE i
        (b.repr.symm (Finsupp.mapRange (residueEquivE φ).symm (map_zero _) f))
      map_add' := fun q r => by
        rw [map_add, map_add]
        exact Finsupp.mapRange_add (fun x y => map_add _ x y) _ _
      map_smul' := fun c q => by
        rw [layerEquivE_symm_smul, map_smul]
        ext a
        simp [Finsupp.mapRange_apply]
      left_inv := fun q => by
        have h : Finsupp.mapRange (residueEquivE φ).symm (map_zero _)
            (Finsupp.mapRange (residueEquivE φ) (map_zero _)
              (b.repr ((layerEquivE φ hφ 𝓛 hE i).symm q))) =
            b.repr ((layerEquivE φ hφ 𝓛 hE i).symm q) := by
          ext a
          simp
        change layerEquivE φ hφ 𝓛 hE i (b.repr.symm (Finsupp.mapRange (residueEquivE φ).symm
          (map_zero _) (Finsupp.mapRange (residueEquivE φ) (map_zero _)
            (b.repr ((layerEquivE φ hφ 𝓛 hE i).symm q))))) = q
        rw [h, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        change Finsupp.mapRange (residueEquivE φ) (map_zero _)
          (b.repr ((layerEquivE φ hφ 𝓛 hE i).symm (layerEquivE φ hφ 𝓛 hE i
            (b.repr.symm (Finsupp.mapRange (residueEquivE φ).symm (map_zero _) f))))) = f
        rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
        ext a
        simp }

theorem transportBasis_apply {ι : Type*} (i : ℤ)
    (b : Module.Basis ι (IsLocalRing.ResidueField (subfieldIntegers F E)) ((L_E).Layer i))
    (a : ι) : transportBasis φ hφ 𝓛 hE i b a = layerEquivE φ hφ 𝓛 hE i (b a) := by
  classical
  rw [transportBasis, Module.Basis.coe_ofRepr]
  change layerEquivE φ hφ 𝓛 hE i (b.repr.symm (Finsupp.mapRange (residueEquivE φ).symm
    (map_zero _) (Finsupp.single a 1))) = _
  rw [Finsupp.mapRange_single, map_one, Module.Basis.repr_symm_single, one_smul]

theorem coe_centralizerChain_lattice (i : ℤ) :
    (((C).lattice i : Set V)) = ((L_E).lattice i : Set V) := rfl

/-- The unit filtrations of the two chains agree. -/
theorem centralizerChain_unitFiltration (n : ℕ) :
    (C).unitFiltration n = (L_E).unitFiltration n := by
  ext g
  have h : ∀ i, (((C).lattice i : Set V)) = ((L_E).lattice i : Set V) := fun i => rfl
  simp only [LatticeChain.mem_unitFiltration, LatticeChain.mem_order_iff_mem_endFiltration,
    LatticeChain.mem_endFiltration_congr h]

/-- The two chains have the same period. -/
theorem centralizerChain_period : (C).period = (L_E).period := by
  have : IsDiscreteValuationRing 𝒪[E] :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing φ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff φ.toMulEquiv).mpr hϖ
  exact PureApproximation.period_eq_of_coe_lattice_eq (C) (L_E) (fun i => rfl) hϖ' hϖ (hφ ϖ)

theorem transportBasis_repr {ι : Type*} (i : ℤ)
    (b : Module.Basis ι (IsLocalRing.ResidueField (subfieldIntegers F E)) ((L_E).Layer i))
    (y : (L_E).Layer i) (a : ι) :
    (transportBasis φ hφ 𝓛 hE i b).repr (layerEquivE φ hφ 𝓛 hE i y) a =
      residueEquivE φ (b.repr y a) := by
  unfold transportBasis
  change Finsupp.mapRange (residueEquivE φ) (map_zero _)
    (b.repr ((layerEquivE φ hφ 𝓛 hE i).symm (layerEquivE φ hφ 𝓛 hE i y))) a = _
  rw [AddEquiv.symm_apply_apply, Finsupp.mapRange_apply]

/-- Coordinates of the action of a matrix through `Matrix.GeneralLinearGroup.toLin'`. -/
theorem equivFun_toLin' {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {n : ℕ}
    (b : Module.Basis (Fin n) k M) (A : GeneralLinear n k) (x : M) :
    b.equivFun ((Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv x) =
      (A : Matrix (Fin n) (Fin n) k).mulVec (b.equivFun x) := by
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  have : Fintype.linearCombination k ⇑b ((A : Matrix (Fin n) (Fin n) k).mulVec ⇑(b.repr x)) =
      b.equivFun.symm ((A : Matrix (Fin n) (Fin n) k).mulVec (b.equivFun x)) := by
    rw [Module.Basis.equivFun_symm_apply, Fintype.linearCombination_apply]
    rfl
  rw [this, LinearEquiv.apply_symm_apply]

theorem mulVec_equivFun_self {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {n : ℕ}
    (β : Module.Basis (Fin n) k M) (A : Matrix (Fin n) (Fin n) k) (s r : Fin n) :
    A.mulVec (β.equivFun (β s)) r = A r s := by
  have h : β.equivFun (β s) = Pi.single s 1 := by
    ext u
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [h, Matrix.mulVec_single_one]
  rfl

/-- **Layer reduction under the transfer.** The reduction of `g ∈ U(𝔅)` on a layer of the chain
over the valuation ring of `E`, in the transported basis, is the image under the residue field
isomorphism of its reduction over the integral closure. -/
theorem layerReduction_transfer {d : Fin (L_E).period → ℕ}
    (b : ∀ i : Fin (L_E).period,
      Module.Basis (Fin (d i)) (IsLocalRing.ResidueField (subfieldIntegers F E))
        ((L_E).Layer ((i : ℕ) : ℤ)))
    (g : (L_E).unitFiltration 0) (i : Fin (C).period)
    (r s : Fin (d (Fin.cast (centralizerChain_period φ hφ 𝓛 hE) i))) :
    (((C).layerReduction
        (fun i' : Fin (C).period => transportBasis φ hφ 𝓛 hE _
          (b (Fin.cast (centralizerChain_period φ hφ 𝓛 hE) i')))
        ⟨g, by rw [centralizerChain_unitFiltration]; exact g.2⟩ i :
          GeneralLinear _ 𝓀[E]) : Matrix _ _ 𝓀[E]) r s =
      residueEquivE φ
        ((((L_E).layerReduction b g (Fin.cast (centralizerChain_period φ hφ 𝓛 hE) i) :
          GeneralLinear _ _) : Matrix _ _ _) r s) := by
  have hp := centralizerChain_period φ hφ 𝓛 hE
  obtain ⟨v, hv, hvs⟩ := (L_E).intervalMk_surjective (((Fin.cast hp i : Fin _) : ℕ) : ℤ)
    ((((Fin.cast hp i : Fin _) : ℕ) : ℤ) + 1) (b (Fin.cast hp i) s)
  have keyE := (L_E).layerReduction_spec b g (Fin.cast hp i) v hv
  have keyC := (C).layerReduction_spec
    (fun i' : Fin (C).period => transportBasis φ hφ 𝓛 hE _ (b (Fin.cast hp i')))
    ⟨g, by rw [centralizerChain_unitFiltration]; exact g.2⟩ i v hv
  have h1 : (C).intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1) v hv =
      transportBasis φ hφ 𝓛 hE _ (b (Fin.cast hp i)) s := by
    rw [transportBasis_apply, ← hvs]
    rfl
  have hmain := (congrArg (fun y => y) keyC).trans
    (congrArg (layerEquivE φ hφ 𝓛 hE (((Fin.cast hp i : Fin _) : ℕ) : ℤ)) keyE).symm
  rw [h1, hvs] at hmain
  have hL : (transportBasis φ hφ 𝓛 hE ((i : ℕ) : ℤ) (b (Fin.cast hp i))).equivFun
      ((Matrix.GeneralLinearGroup.toLin' (transportBasis φ hφ 𝓛 hE ((i : ℕ) : ℤ)
        (b (Fin.cast hp i)))
        ((C).layerReduction (fun i' : Fin (C).period => transportBasis φ hφ 𝓛 hE _
          (b (Fin.cast hp i'))) ⟨g, by rw [centralizerChain_unitFiltration]; exact g.2⟩ i)).toLinearEquiv
        (transportBasis φ hφ 𝓛 hE ((i : ℕ) : ℤ) (b (Fin.cast hp i)) s)) r =
      (transportBasis φ hφ 𝓛 hE ((i : ℕ) : ℤ) (b (Fin.cast hp i))).equivFun
        (layerEquivE φ hφ 𝓛 hE ((i : ℕ) : ℤ)
          ((Matrix.GeneralLinearGroup.toLin' (b (Fin.cast hp i))
            ((L_E).layerReduction b g (Fin.cast hp i))).toLinearEquiv
            (b (Fin.cast hp i) s))) r :=
    congrArg (fun y => (transportBasis φ hφ 𝓛 hE ((i : ℕ) : ℤ)
      (b (Fin.cast hp i))).equivFun y r) hmain
  rw [equivFun_toLin', mulVec_equivFun_self, Module.Basis.equivFun_apply,
    transportBasis_repr, ← Module.Basis.equivFun_apply, equivFun_toLin',
    mulVec_equivFun_self] at hL
  exact hL

end Langlands.BushnellKutzko.SplitTypeJacquet
