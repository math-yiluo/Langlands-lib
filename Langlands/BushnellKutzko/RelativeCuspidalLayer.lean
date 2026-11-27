import Langlands.BushnellKutzko.MaximalSimpleTypeLevelZero

/-! # The period-one cuspidal layer in a simple stratum's centralizer -/

noncomputable section

open IsLocalRing ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem commute_of_mem_elementAlgebra {β x z : A} (h : Commute β x)
    (hz : z ∈ elementAlgebra β) : Commute z x :=
  (Algebra.commute_of_mem_adjoin_singleton_of_commute (R := F) hz h.symm).symm

/-- The units of the `F[β]`-linear endomorphism algebra, embedded by scalar restriction. -/
def centralizerUnitsRestrictScalars (β : A) : (Module.End (elementAlgebra β) V)ˣ →* G :=
  Units.map {
    toFun := LinearMap.restrictScalars F
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

theorem centralizerUnitsRestrictScalars_injective (β : A) :
    Function.Injective (centralizerUnitsRestrictScalars β) := by
  intro x y h
  apply Units.ext
  apply LinearMap.restrictScalars_injective F
  exact congrArg Units.val h

/-- The image of scalar restriction is the unit centralizer of the generator. -/
theorem centralizerUnitsRestrictScalars_range (β : A) :
    (centralizerUnitsRestrictScalars β).range = centralizerUnitGroup β := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change Commute β ((y.val : Module.End (elementAlgebra β) V).restrictScalars F)
    ext v
    let b : elementAlgebra β := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
    change b • y.val v = y.val (b • v)
    rw [map_smul]
  · intro hx
    let E := elementAlgebra β
    let lift (y : G) (hy : y ∈ centralizerUnitGroup β) : Module.End E V :=
      { toFun := y.val
        map_add' := y.val.map_add
        map_smul' := fun z w =>
          (LinearMap.congr_fun (commute_of_mem_elementAlgebra hy z.2).eq w).symm }
    refine ⟨⟨lift x hx, lift x⁻¹ (inv_mem hx), ?_, ?_⟩, rfl⟩
    · ext w
      exact LinearMap.congr_fun x.val_inv w
    · ext w
      exact LinearMap.congr_fun x.inv_val w

section Field

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- As a set of ambient automorphisms, the embedded multiplicative group consists of
ambient units whose underlying endomorphisms lie in the generated field. -/
theorem range_subfieldUnits_elementAlgebra (L : LatticeChain 𝒪[F] F V) (β : A)
    (hβ : IsField (elementAlgebra β)) :
    letI := hβ.toField
    Set.range (subfieldUnits F (elementAlgebra β) V) = {x : G | (x : A) ∈ elementAlgebra β} := by
  let := hβ.toField
  classical
  have := L.nontrivialSpace
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact x.val.2
  · intro hg
    let x : elementAlgebra β := ⟨g.val, hg⟩
    have hx : x ≠ 0 := fun he => g.ne_zero (congrArg Subtype.val he)
    exact ⟨Units.mk0 x hx, Units.ext rfl⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Scalar automorphisms over `F[β]` restrict to the embedded field units. -/
theorem centralizerUnitsRestrictScalars_scalar (β : A) (hβ : IsField (elementAlgebra β)) :
    letI := hβ.toField
    ∀ u : (elementAlgebra β)ˣ,
      centralizerUnitsRestrictScalars β
        (Units.map (algebraMap (elementAlgebra β) (Module.End (elementAlgebra β) V)).toMonoidHom u) =
        subfieldUnits F (elementAlgebra β) V u := by
  let := hβ.toField
  intro u
  rfl

set_option maxHeartbeats 1200000 in
/-- Reduction and self-intertwining on the single relative layer. The centralizer version
follows by transporting the period-one calculation through restriction of scalars. -/
theorem relativeCuspidalLayer (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) :
    letI := hS.1.1.fst.toField
    haveI : FiniteDimensional F (elementAlgebra S.b) :=
      S.chain.finiteDimensional_subfield (elementAlgebra S.b)
    haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
    let E := elementAlgebra S.b
    let C := S.chain.subfieldChain E hS.1.1.snd
    let U := relativeUnitFiltration S.chain S.b 0
    let kE := ResidueField (subfieldIntegers F E)
    C.period = 1 → ∀ (n : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
      (σ : Representation ℂ (GeneralLinear n kE) W), FiniteGeneralLinear.IsCuspidal σ →
    ∀ (b : ∀ i : Fin 1, Module.Basis (Fin n) kE (C.Layer ((i : ℕ) : ℤ)))
      (φ : U →* (Fin 1 → GeneralLinear n kE)),
      IsLayerReduction C U (fun _ hu i _ hv => S.chain.apply_mem_lattice_of_mem_unitFiltration
        hu.2 i hv) b φ →
      Function.Surjective ((Pi.evalMonoidHom _ (0 : Fin 1)).comp φ) ∧
      {x : G | x ∈ centralizerUnitGroup S.b ∧
        x ∈ representationSelfIntertwining ((tensorPowerRepresentation σ 1).comp φ)} =
          Set.range (subfieldUnits F E V) * (U : Set G) := by
  intro E C U kE hC n W _ _ _ σ hc b φ hφ
  let : Field E := hS.1.1.fst.toField
  let : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  let : IsDiscreteValuationRing (subfieldIntegers F E) := subfieldIntegers_isDiscreteValuationRing F E
  let : IsFractionRing (subfieldIntegers F E) E := subfieldIntegers_isFractionRing F E
  let ι := centralizerUnitsRestrictScalars (V := V) S.b
  have hι := centralizerUnitsRestrictScalars_injective (V := V) S.b
  have hRange : ι.range = centralizerUnitGroup S.b := centralizerUnitsRestrictScalars_range S.b
  have hOrder (x : Module.End E V) : x ∈ C.order ↔ x.restrictScalars F ∈ S.chain.order := by
    exact ⟨fun hx => S.chain.mem_order.2 fun i w hw => C.mem_order.1 hx i w hw,
      fun hx => C.mem_order.2 fun i w hw => S.chain.mem_order.1 hx i w hw⟩
  have hUnit (x : (Module.End E V)ˣ) : ι x ∈ U ↔ x ∈ C.unitFiltration 0 := by
    have hcomm : ι x ∈ centralizerUnitGroup S.b := hRange ▸ ⟨x, rfl⟩
    constructor
    · intro hx
      obtain ⟨hx₁, hx₂⟩ := S.chain.mem_unitFiltration_zero.1 hx.2
      exact C.mem_unitFiltration_zero.2 ⟨(hOrder x.val).2 hx₁, (hOrder x.inv).2 hx₂⟩
    · intro hx
      obtain ⟨hx₁, hx₂⟩ := C.mem_unitFiltration_zero.1 hx
      exact ⟨hcomm, S.chain.mem_unitFiltration_zero.2
        ⟨(hOrder x.val).1 hx₁, (hOrder x.inv).1 hx₂⟩⟩
  have hMap : (C.unitFiltration 0).map ι = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hUnit y).2 hy
    · intro hx
      have hx' : x ∈ ι.range := hRange.symm ▸ hx.1
      obtain ⟨y, rfl⟩ := hx'
      exact ⟨y, (hUnit y).1 hx, rfl⟩
  let e := ((C.unitFiltration 0).equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hMap)
  have hcoe (u : C.unitFiltration 0) : (e u : G) = ι (u : (Module.End E V)ˣ) := rfl
  let φE := φ.comp e.toMonoidHom
  have hφE : IsLayerReduction C (C.unitFiltration 0)
      (fun _ hu i _ hv => C.apply_mem_lattice_of_mem_unitFiltration hu i hv) b φE := by
    intro u i v hv
    exact hφ (e u) i v hv
  refine ⟨?_, ?_⟩
  · have hs := C.layerReduction_surjective_periodOne hC b φE hφE
    intro y
    obtain ⟨u, hu⟩ := hs y
    exact ⟨e u, hu⟩
  let r := (tensorPowerRepresentation σ 1).comp φ
  let rE := (tensorPowerRepresentation σ 1).comp φE
  have hint := C.selfIntertwining_periodOneLayer hC σ hc b φE hφE
  have hcomp (y : (Module.End E V)ˣ) : Intertwines rE rE y ↔ Intertwines r r (ι y) :=
    selfIntertwines_comp_mulEquiv_iff ι hι e hcoe r y
  have hscalar (a : Eˣ) :
      ι (Units.map (algebraMap E (Module.End E V)).toMonoidHom a) = subfieldUnits F E V a :=
    centralizerUnitsRestrictScalars_scalar S.b hS.1.1.fst a
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    have hx'' : x ∈ ι.range := hRange.symm ▸ hx
    obtain ⟨y, rfl⟩ := hx''
    have hy : y ∈ representationSelfIntertwining rE := (hcomp y).2 hx'
    change y ∈ representationSelfIntertwining ((tensorPowerRepresentation σ 1).comp φE) at hy
    rw [hint] at hy
    obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := hy
    refine ⟨_, ⟨a, rfl⟩, (e ⟨u, hu⟩ : G), (e ⟨u, hu⟩).2, ?_⟩
    change subfieldUnits F E V a * (e ⟨u, hu⟩ : G) = ι (_ * u)
    rw [hcoe, map_mul, hscalar]
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
    let t := e.symm ⟨u, hu⟩
    have ht : ι (t : (Module.End E V)ˣ) = u := congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
    let y := Units.map (algebraMap E (Module.End E V)).toMonoidHom a * t.val
    have hy : y ∈ representationSelfIntertwining ((tensorPowerRepresentation σ 1).comp φE) := by
      rw [hint]
      exact ⟨_, ⟨a, rfl⟩, t, t.2, rfl⟩
    have hey : ι y = subfieldUnits F E V a * u := by
      rw [show y = _ * _ from rfl, map_mul, hscalar, ht]
    change subfieldUnits F E V a * u ∈ centralizerUnitGroup S.b ∧
      Intertwines r r (subfieldUnits F E V a * u)
    rw [← hey]
    exact ⟨hRange ▸ ⟨y, rfl⟩, (hcomp y).1 hy⟩

end Field

end Langlands.BushnellKutzko
