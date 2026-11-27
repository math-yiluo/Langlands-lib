import Langlands.BushnellKutzko.PeriodOneLatticeCoordinates

/-! # The period-one cuspidal layer calculation and maximal level-zero types -/

noncomputable section

open IsLocalRing ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

/-- Evaluating the single factor identifies the one-fold tensor power with the original
representation pulled back along the coordinate projection. -/
def tensorPowerOneEquiv {H J W : Type*} [Group H] [Group J] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ H W) (φ : J →* (Fin 1 → H)) :
    Representation.Equiv ((tensorPowerRepresentation σ 1).comp φ)
      (σ.comp ((Pi.evalMonoidHom _ 0).comp φ)) := by
  let e : (PiTensorProduct ℂ fun _ : Fin 1 => W) ≃ₗ[ℂ] W := PiTensorProduct.subsingletonEquiv 0
  refine Representation.Equiv.mk e fun j => LinearMap.ext fun z => ?_
  obtain ⟨w, rfl⟩ := e.symm.surjective z
  change e (((tensorPowerRepresentation σ 1) (φ j)) (e.symm w)) = σ (φ j 0) (e (e.symm w))
  rw [e.apply_symm_apply, show e.symm w = PiTensorProduct.tprod ℂ (fun _ : Fin 1 => w) from
    PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) w]
  change e (PiTensorProduct.map (fun i : Fin 1 => σ (φ j i))
    (PiTensorProduct.tprod ℂ (fun _ : Fin 1 => w))) = _
  rw [PiTensorProduct.map_tprod]
  exact PiTensorProduct.subsingletonEquiv_apply_tprod (0 : Fin 1) _

namespace LatticeChain

variable {O K V : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module O V] [Module K V]
  [IsScalarTower O K V]

/-- The cuspidal inflation on the single graded piece is intertwined precisely by the scalar
translates of the integral unit subgroup. -/
theorem selfIntertwining_periodOneLayer (L : LatticeChain O K V) (hL : L.period = 1) {n : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (σ : Representation ℂ (GeneralLinear n (ResidueField O)) W)
    (hσ : FiniteGeneralLinear.IsCuspidal σ)
    (b : ∀ i : Fin 1, Module.Basis (Fin n) (ResidueField O) (L.Layer ((i : ℕ) : ℤ)))
    (φ : L.unitFiltration 0 →* (Fin 1 → GeneralLinear n (ResidueField O)))
    (hφ : IsLayerReduction L (L.unitFiltration 0)
      (fun _ hu i _ hv => L.apply_mem_lattice_of_mem_unitFiltration hu i hv) b φ) :
    representationSelfIntertwining ((tensorPowerRepresentation σ 1).comp φ) =
      Set.range (Units.map (algebraMap K (Module.End K V)).toMonoidHom) *
        (L.unitFiltration 0 : Set (Module.End K V)ˣ) := by
  let σ₁ := σ.comp ((Pi.evalMonoidHom _ 0).comp φ)
  let ee := tensorPowerOneEquiv σ φ
  have hs : representationSelfIntertwining ((tensorPowerRepresentation σ 1).comp φ) =
      representationSelfIntertwining σ₁ := by
    ext g
    exact ⟨selfIntertwines_of_equiv ee, selfIntertwines_of_equiv ee.symm⟩
  rw [hs]
  obtain ⟨v, ϖ, hv, hϖ⟩ := exists_fraction_valuation_integers O K
  obtain ⟨a, ha⟩ := L.exists_basis_lift_layerZero hL (b 0)
  let e := L.latticeMatrixEquiv a hL
  let gM := L.matrixEquiv a
  let ρ := σ.comp (IntegralMatrices.reduction (IsFractionRing.injective O K))
  have hρ : σ₁ = ρ.comp e.toMonoidHom := by
    change σ.comp ((Pi.evalMonoidHom _ 0).comp φ) = _
    rw [L.layerReduction_eq_matrix_reduction a hL b ha φ hφ]
    rfl
  have hint : representationSelfIntertwining ρ =
      Set.range (GeneralLinear.scalar (n := n) (R := K)) *
        (IntegralMatrices.subgroup O K n : Set _) :=
    CuspidalMatrixIntertwining.selfIntertwining_inflatedCuspidal hv hϖ σ hσ
  ext g
  have he : g ∈ representationSelfIntertwining σ₁ ↔ gM g ∈ representationSelfIntertwining ρ := by
    rw [hρ]
    exact selfIntertwines_comp_mulEquiv_iff gM.toMonoidHom gM.injective e
      (L.coe_latticeMatrixEquiv a hL) ρ g
  rw [he, hint]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, m, hm, hgm⟩
    let u := e.symm ⟨m, hm⟩
    have hu : gM (u : (Module.End K V)ˣ) = m := congrArg Subtype.val (e.apply_symm_apply ⟨m, hm⟩)
    refine ⟨_, ⟨c, rfl⟩, u.val, u.2, gM.injective ?_⟩
    change gM (Units.map (algebraMap K (Module.End K V)).toMonoidHom c * u.val) = gM g
    rw [map_mul, L.matrixEquiv_scalar a, hu]
    exact hgm
  · rintro ⟨_, ⟨c, rfl⟩, u, hu, rfl⟩
    refine ⟨_, ⟨c, rfl⟩, gM u, (L.matrixEquiv_mem_integral_iff a hL u).2 hu, ?_⟩
    change GeneralLinear.scalar c * gM u = gM (Units.map (algebraMap K (Module.End K V)).toMonoidHom c * u)
    rw [map_mul, L.matrixEquiv_scalar a]

end LatticeChain

universe uF uV uW

/-- The intertwining of a level-zero simple type attached to a period-one lattice chain. -/
theorem levelZeroSimpleTypeIntertwining
    {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {V : Type uV} [AddCommGroup V] [Module F V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {J : Subgroup (Module.End F V)ˣ} {ρ : Representation ℂ J W}
    (L : LatticeChain 𝒪[F] F V) (h : IsLevelZeroSimpleTypeData L 1 ρ) :
    representationSelfIntertwining ρ =
      Set.range (Units.map (algebraMap F (Module.End F V)).toMonoidHom) *
        (J : Set (Module.End F V)ˣ) := by
  obtain ⟨_, hp, f, d, σ, hσ, hc, b, φ, hφ, _, hpair⟩ := h
  let : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear f (ResidueField 𝒪[F]))) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let : Nontrivial (Fin d → ℂ) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear f (ResidueField 𝒪[F]))) σ.asModule
  rw [hpair.selfIntertwining_eq,
    L.selfIntertwining_periodOneLayer hp.symm σ hc b φ hφ, hpair.choose]

end Langlands.BushnellKutzko
