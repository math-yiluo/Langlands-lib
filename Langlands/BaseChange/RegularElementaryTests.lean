import Langlands.BaseChange.TwistedDiagonalOpen
import Langlands.ClassFieldTheory.Local.UniverseZero.UniverseZeroModel
import Langlands.LocalFactor.DeligneHenniartTopLayerOrders
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Hecke.TestFunction

/-! # Regular elementary tests for cyclic base change -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified HarmonicAnalysis Matrix Set _root_.Topology
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus)
open ClassFieldTheory.Local
open LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer
open scoped Matrix.Norms.Operator

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

/-- Integral diagonal unit tuples multiplied coordinatewise by the weight powers. -/
def elementaryDiagonalTuples (E : PadicField.{v} p) (π : E.Carrierˣ)
    (ν : Fin (r + 1) → ℤ) : Set (Fin (r + 1) → E.Carrierˣ) :=
  Set.univ.pi fun i =>
    (fun x : E.Carrierˣ => π ^ ν i * x) '' (E.canonicalTopologicalData.unitSubgroup : Set E.Carrierˣ)

/-- The compact subgroup saturation of the weighted integral diagonal units. -/
def regularElementarySupport (E : PadicField.{v} p) (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
    (π : E.Carrierˣ) (ν : Fin (r + 1) → ℤ) : Set (GeneralLinear (r + 1) E.Carrier) :=
  twistedDiagonalSaturation τ (sphericalOpenSubgroup E r).toSubgroup
    (elementaryDiagonalTuples E π ν)

theorem mem_regularElementarySupport_iff (E : PadicField.{v} p)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ) (ν : Fin (r + 1) → ℤ)
    (g : GeneralLinear (r + 1) E.Carrier) :
    g ∈ regularElementarySupport E τ π ν ↔
      ∃ k ∈ sphericalOpenSubgroup E r, ∃ m : Fin (r + 1) → E.Carrierˣ,
        (∀ i, m i ∈ E.canonicalTopologicalData.unitSubgroup) ∧
        k⁻¹ * torus π ν * diagonalUnits m * entrywiseAut τ (r + 1) k = g := by
  constructor
  · rintro ⟨k, hk, a, ha, rfl⟩
    have ha' (i : Fin (r + 1)) : ∃ z ∈ E.canonicalTopologicalData.unitSubgroup,
        π ^ ν i * z = a i := ha i (Set.mem_univ _)
    choose m hm he using ha'
    refine ⟨k, hk, m, hm, ?_⟩
    have hprod : torus π ν * diagonalUnits m = diagonalUnits a := by
      rw [torus, ← map_mul]
      exact congrArg (fun b : Fin (r + 1) → E.Carrierˣ => diagonalUnits b) (funext he)
    rw [mul_assoc k⁻¹, hprod]
  · rintro ⟨k, hk, m, hm, rfl⟩
    have ha : (fun i => π ^ ν i * m i) ∈ elementaryDiagonalTuples E π ν :=
      fun i _ => ⟨m i, hm i, rfl⟩
    refine ⟨k, hk, _, ha, ?_⟩
    change k⁻¹ * diagonalUnits ((fun i => π ^ ν i) * m) * _ =
      k⁻¹ * torus π ν * diagonalUnits m * _
    rw [map_mul, ← mul_assoc]
    rfl

theorem isCompact_regularElementarySupport (E : PadicField.{v} p)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ) (ν : Fin (r + 1) → ℤ) :
    IsCompact (regularElementarySupport E τ π ν) := by
  let := E.canonicalNormedField
  let := E.canonicalNormedAlgebra
  let : CompleteSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) E.Carrier) :=
    FiniteDimensional.complete (Padic p) _
  let K := sphericalOpenSubgroup E r
  let A := elementaryDiagonalTuples E π ν
  let D := E.canonicalTopologicalData
  have hC : IsCompact (D.unitSubgroup : Set E.Carrierˣ) := by
    rw [← D.unitFiltration_zero]
    exact D.isCompact_unitFiltration 0
  have hA : IsCompact A :=
    isCompact_univ_pi fun i => hC.image (continuous_const.mul continuous_id)
  have hDiag : Continuous
      (diagonalUnits : (Fin (r + 1) → E.Carrierˣ) →* GeneralLinear (r + 1) E.Carrier) := by
    have hEmb : IsOpenEmbedding
        (Units.val : GeneralLinear (r + 1) E.Carrier → Matrix (Fin (r + 1)) (Fin (r + 1)) E.Carrier) :=
      Units.isOpenEmbedding_val
    apply hEmb.isEmbedding.continuous_iff.mpr
    exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  have hτ : Continuous τ := (Weil.Local.extension_isometry E E τ.toAlgHom).continuous
  have hMap : Continuous (entrywiseAut τ (r + 1)) :=
    Continuous.generalLinearGroup_map (f := τ.toRingHom) hτ
  let f : GeneralLinear (r + 1) E.Carrier × (Fin (r + 1) → E.Carrierˣ) →
      GeneralLinear (r + 1) E.Carrier :=
    fun x => x.1⁻¹ * diagonalUnits x.2 * entrywiseAut τ (r + 1) x.1
  have hf : Continuous f :=
    (continuous_fst.inv.mul (hDiag.comp continuous_snd)).mul (hMap.comp continuous_fst)
  have he : regularElementarySupport E τ π ν = f '' ((K : Set _) ×ˢ A) := by
    ext g
    constructor
    · rintro ⟨k, hk, a, ha, he⟩
      exact ⟨(k, a), ⟨hk, ha⟩, he⟩
    · rintro ⟨⟨k, a⟩, ⟨hk, ha⟩, he⟩
      exact ⟨k, hk, a, ha, he⟩
  rw [he]
  exact ((sphericalOpenSubgroup_isCompact E r).prod hA).image hf

theorem isOpen_regularElementarySupport (E : PadicField.{v} p)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    IsOpen (regularElementarySupport E τ π ν) := by
  let := E.canonicalNormedField
  let := E.canonicalNormedAlgebra
  let D := E.canonicalTopologicalData
  let A := elementaryDiagonalTuples E π ν
  let W (i : Fin (r + 1)) :=
    (fun x : E.Carrierˣ => π ^ ν i * x) '' (D.unitSubgroup : Set E.Carrierˣ)
  have hA : (fun b : Fin (r + 1) → E.Carrierˣ => fun i => (b i : E.Carrier)) '' A =
      Set.univ.pi (fun i => (Units.val : E.Carrierˣ → E.Carrier) '' W i) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩ i hi
      exact ⟨a i, ha i hi, rfl⟩
    · intro hb
      have hh (i : Fin (r + 1)) : ∃ a ∈ W i, (a : E.Carrier) = b i := hb i (Set.mem_univ _)
      choose a ha he using hh
      exact ⟨a, fun i _ => ha i, funext he⟩
  apply isOpen_twistedDiagonalSaturation τ (sphericalOpenSubgroup E r) A
  · rw [hA]
    apply isOpen_set_pi Set.finite_univ
    intro i _
    apply Units.isOpenEmbedding_val.isOpenMap
    exact (Homeomorph.mulLeft (π ^ ν i)).isOpenMap _ (isOpen_unitSubgroup E D)
  · intro a ha i j hij z hz
    by_contra hne
    have hord (i : Fin (r + 1)) : D.ord (a i : E.Carrier) = ν i := by
      obtain ⟨b, hb, hb'⟩ := ha i (Set.mem_univ _)
      rw [← hb', Units.val_mul, D.ord_mul (Units.ne_zero _) b.ne_zero,
        Units.val_zpow_eq_zpow_val, D.ord_zpow, hπ, mul_one,
        (mem_unitSubgroup_iff_ord_eq_zero E D b).mp hb, add_zero]
    have horder := congrArg D.ord hz
    rw [D.ord_mul (a i).ne_zero ((map_ne_zero τ).mpr hne), D.ord_mul (a j).ne_zero hne,
      LocalClassField.UniverseZero.ord_eq_of_algEquiv τ D D z, hord i, hord j] at horder
    exact hij (hν.injective (add_right_cancel horder))

/-- The characteristic function of the regular elementary support. -/
def regularElementaryTest (E : PadicField.{v} p)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    SchwartzBruhat (GeneralLinear (r + 1) E.Carrier) :=
  let hc := isCompact_regularElementarySupport E τ π ν
  Hecke.TestFunction.characteristic ⟨hc.isClosed, isOpen_regularElementarySupport E τ π hπ ν hν⟩ hc

@[simp] theorem regularElementaryTest_apply (E : PadicField.{v} p)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) (g : GeneralLinear (r + 1) E.Carrier) :
    regularElementaryTest E τ π hπ ν hν g =
      (regularElementarySupport E τ π ν).indicator (fun _ => (1 : ℂ)) g := rfl

section BaseChange

variable (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

/-- The image of the base uniformizer, as a unit of the upper field. -/
def elementaryUpperUniformizer : E.Carrierˣ :=
  Units.map (algebraMap F.Carrier E.Carrier) F.canonicalTopologicalData.uniformizerUnit

theorem ord_elementaryUpperUniformizer
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) :
    E.canonicalTopologicalData.ord (elementaryUpperUniformizer F E : E.Carrier) = 1 := by
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  have h := ramificationIndex_mul_ord_algebraMap (K := F) (M := E) T S T.uniformizer
  change (T.ramificationIndex : ℤ) * S.ord (algebraMap F.Carrier E.Carrier T.uniformizer) =
    (S.ramificationIndex : ℤ) * T.ord T.uniformizer at h
  rw [T.ord_uniformizer, he] at h
  have hne : (T.ramificationIndex : ℤ) ≠ 0 := by exact_mod_cast T.ramificationIndex_pos.ne'
  exact mul_left_cancel₀ hne h

/-- The regular Labesse pair, at weight `ν` upstairs and its degree-scaled
weight downstairs. Both sides use the base uniformizer. -/
def regularElementaryBaseChangeTests (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (l : ℕ) (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    SchwartzBruhat (GeneralLinear (r + 1) E.Carrier) ×
      SchwartzBruhat (GeneralLinear (r + 1) F.Carrier) :=
  ⟨regularElementaryTest E (σ.restrictScalars (Padic p)) (elementaryUpperUniformizer F E)
      (ord_elementaryUpperUniformizer F E he) ν hν,
    regularElementaryTest F AlgEquiv.refl F.canonicalTopologicalData.uniformizerUnit
      (by rw [F.canonicalTopologicalData.uniformizerUnit_val,
        F.canonicalTopologicalData.ord_uniformizer])
      (fun i => (l : ℤ) * ν i)
      (fun _ _ hij => mul_lt_mul_of_pos_left (hν hij) (by exact_mod_cast hσ.pos))⟩

variable (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
  (l : ℕ) (hσ : IsCyclicAlgebra σ l)
  (he : E.canonicalTopologicalData.ramificationIndex =
    F.canonicalTopologicalData.ramificationIndex)
  (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)

theorem regularElementaryBaseChangeTests_fst_apply (δ : GeneralLinear (r + 1) E.Carrier) :
    (regularElementaryBaseChangeTests F E σ l hσ he ν hν).1 δ =
      {d | ∃ k ∈ sphericalOpenSubgroup E r, ∃ m : Fin (r + 1) → E.Carrierˣ,
        (∀ i, m i ∈ E.canonicalTopologicalData.unitSubgroup) ∧
        k⁻¹ * torus (elementaryUpperUniformizer F E) ν * diagonalUnits m *
          entrywiseAut σ (r + 1) k = d}.indicator (fun _ => (1 : ℂ)) δ := by
  change (regularElementarySupport E (σ.restrictScalars (Padic p))
    (elementaryUpperUniformizer F E) ν).indicator (fun _ => (1 : ℂ)) δ = _
  congr 1
  ext d
  exact mem_regularElementarySupport_iff E _ _ ν d

theorem regularElementaryBaseChangeTests_snd_apply (γ : GeneralLinear (r + 1) F.Carrier) :
    (regularElementaryBaseChangeTests F E σ l hσ he ν hν).2 γ =
      {g | ∃ k ∈ sphericalOpenSubgroup F r, ∃ m : Fin (r + 1) → F.Carrierˣ,
        (∀ i, m i ∈ F.canonicalTopologicalData.unitSubgroup) ∧
        k⁻¹ * torus F.canonicalTopologicalData.uniformizerUnit (fun i => (l : ℤ) * ν i) *
          diagonalUnits m * k = g}.indicator (fun _ => (1 : ℂ)) γ := by
  change (regularElementarySupport F AlgEquiv.refl F.canonicalTopologicalData.uniformizerUnit
    (fun i => (l : ℤ) * ν i)).indicator (fun _ => (1 : ℂ)) γ = _
  congr 1
  ext g
  have ht : (AlgEquiv.refl : F.Carrier ≃ₐ[Padic p] F.Carrier) = 1 := rfl
  simpa only [ht, entrywiseAut_one_apply, Set.mem_ofPred_eq] using
    mem_regularElementarySupport_iff F AlgEquiv.refl _ (fun i => (l : ℤ) * ν i) g

end BaseChange

end Langlands.BaseChange
