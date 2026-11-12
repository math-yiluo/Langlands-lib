import Langlands.LocalFactor.DeligneHenniartUpperComparison
import Langlands.LocalFactor.DeligneHenniartApproximateDimensionOne
import Langlands.LocalFactor.DeligneHenniartTopLayerStatement

/-!
# Relative Herbrand functions between intermediate fields

For finite intermediate fields `E ≤ L` of the closure of a `p`-adic field `F`, this module
defines `ψ_{L/E}` at finite level, proves Herbrand's subgroup formula, transitivity, the
slope `e_L / e_E` past an index whose upper group lies in `W_L` (DH81 3.2(iii)) and the
bound `e_E ψ_{L/E}(s) ≤ e_L s`. It assembles the inputs `HerbrandInputRel` and
`ApproximateHerbrandInput` of the Deligne--Henniart witness lemmas; the second one uses the
first-order norm–trace congruence `TopLayerNormTraceStatement` (DH81 3.12(i)) as hypothesis.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic LocalClassField

universe u uK uE

section Tower

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (K : PadicField.{uK} p)
  {E : PadicField.{uE} p}
  [Algebra K.Carrier (AlgebraicClosure F.Carrier)] [Algebra E.Carrier (AlgebraicClosure F.Carrier)]
  [Algebra F.Carrier K.Carrier] [Algebra F.Carrier E.Carrier] [Algebra K.Carrier E.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower F.Carrier E.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower K.Carrier E.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) E.Carrier (AlgebraicClosure F.Carrier)]
  {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
  (hE : ∀ x : E.Carrier, algebraMap E.Carrier (AlgebraicClosure F.Carrier) x ∈
    M.toIntermediateField)

attribute [local instance] extension_padicScalarTower

omit [Algebra F.Carrier K.Carrier] [Algebra F.Carrier E.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower F.Carrier E.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) E.Carrier (AlgebraicClosure F.Carrier)] in
include hE in
theorem algebraMap_mem_of_tower (x : K.Carrier) :
    algebraMap K.Carrier (AlgebraicClosure F.Carrier) x ∈ M.toIntermediateField := by
  rw [IsScalarTower.algebraMap_apply K.Carrier E.Carrier (AlgebraicClosure F.Carrier)]
  exact hE _

omit [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)] in
/-- The scalar tower `F → K → M` for the finite Galois field `M` viewed over `E`. -/
theorem towerField_isScalarTower :
    IsScalarTower F.Carrier K.Carrier
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext
    (IsScalarTower.algebraMap_apply F.Carrier K.Carrier (AlgebraicClosure F.Carrier) x)

attribute [local instance] towerField_isScalarTower

/-- The relative index `φ_{M/E} ∘ ψ_{M/K}` of the tower `K → E`, computed in the finite
Galois field `M ⊇ E` viewed over `E`. -/
def towerIndex (v : ℝ) : ℝ :=
  Padic.herbrandPhi (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
    E.Carrier
    (Padic.herbrandPsi (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
      K.Carrier v)

/-- The index `[G_0 : G_0 ∩ Gal(M/E)]` in the inertia group of `Gal(M/K)`. -/
def towerRatio : ℕ :=
  (AlgEquiv.restrictScalarsHom K.Carrier :
    ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[E.Carrier]
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier) →*
    ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[K.Carrier]
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier)).range.relIndex
    (Padic.lowerRamificationGroup
      (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData K.Carrier 0)

/-- The identity of `M` from its structure over `K` to its structure over `E`, over `K`. -/
def towerFieldEquiv :
    (finiteGaloisPadicField K (extendFiniteGalois (algebraMap_mem_of_tower F K hE))).Carrier ≃ₐ[
        K.Carrier]
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The relative index of `K` computed in `M` viewed over `E`. -/
theorem relativeIndex_eq_tower (u : ℝ) :
    relativeIndex F M (algebraMap_mem_of_tower F K hE) u =
      Padic.herbrandPhi (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
        K.Carrier
        (Padic.herbrandPsi
          (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
          F.Carrier u) := by
  unfold relativeIndex
  rw [herbrandPsi_eq_of_algEquiv _ _ F.Carrier
      ((extendFiniteGaloisEquiv (algebraMap_mem_of_tower F K hE)).symm.trans
        (extendFiniteGaloisEquiv hE)),
    herbrandPhi_eq_of_algEquiv _ _ K.Carrier (towerFieldEquiv F K hE)]

/-- Transitivity: `ψ_{E/K} ∘ ψ_{K/F} = ψ_{E/F}`. -/
theorem towerIndex_relativeIndex (u : ℝ) :
    towerIndex F K hE (relativeIndex F M (algebraMap_mem_of_tower F K hE) u) =
      relativeIndex F M hE u := by
  rw [relativeIndex_eq_tower F K hE, towerIndex, Padic.herbrandPsi_herbrandPhi]
  rfl

omit [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)] in
theorem towerIndex_zero : towerIndex F K hE 0 = 0 := by
  simp [towerIndex]

omit [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)] in
theorem towerIndex_continuous : Continuous (towerIndex F K hE) :=
  (Padic.herbrandPhi_continuous _ _).comp (Padic.herbrandPsi_continuous _ _)

omit [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)] in
theorem towerIndex_strictMono : StrictMono (towerIndex F K hE) :=
  (Padic.herbrandPhi_strictMono _ _).comp (Padic.herbrandPsi_strictMono _ _)

omit [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)] in
/-- `ψ_{E/K}(s) ≤ [G_0 : G_0 ∩ Gal(M/E)] · s` for `s ≥ 0`. -/
theorem towerIndex_le_mul {s : ℝ} (hs : 0 ≤ s) :
    towerIndex F K hE s ≤ (towerRatio F K hE : ℝ) * s :=
  herbrandPhi_herbrandPsi_le_mul K.Carrier E.Carrier _ hs

/-- The restriction to `M` of an absolute Galois element, read in the ambient closure. -/
theorem absoluteRelativeRestriction_apply_coe
    (τ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier)
    (y : (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier) :
    ((absoluteRelativeRestriction F hE τ y : (extendFiniteGalois hE).toIntermediateField) :
      AlgebraicClosure F.Carrier) = τ (y : AlgebraicClosure F.Carrier) := by
  change (AlgEquiv.restrictNormalHom M.toIntermediateField τ
    ⟨(y : AlgebraicClosure F.Carrier), y.2⟩ : AlgebraicClosure F.Carrier) = _
  rw [AlgEquiv.restrictNormalHom_apply]

omit [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)] in
/-- An absolute Galois element restricts into the image of `Gal(M/K)` exactly when it
fixes `K`. -/
theorem absoluteRelativeRestriction_mem_range_iff (τ : Field.absoluteGaloisGroup F.Carrier) :
    absoluteRelativeRestriction F hE τ ∈
        (AlgEquiv.restrictScalarsHom F.Carrier :
          ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[K.Carrier]
            (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier) →*
          ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[F.Carrier]
            (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier)).range ↔
      ∀ k : K.Carrier, AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k := by
  have hρ := absoluteRelativeRestriction_apply_coe F hE τ
  constructor
  · rintro ⟨σ, hσ⟩ k
    have h1 := congrArg (fun π : _ ≃ₐ[F.Carrier] _ =>
      ((π (algebraMap K.Carrier (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier k) :
        (extendFiniteGalois hE).toIntermediateField) : AlgebraicClosure F.Carrier)) hσ
    simp only at h1
    rw [hρ] at h1
    refine h1.symm.trans ?_
    change ((σ (algebraMap K.Carrier _ k) : (extendFiniteGalois hE).toIntermediateField) :
      AlgebraicClosure F.Carrier) = _
    rw [σ.commutes]
    rfl
  · intro hk
    refine ⟨{ (absoluteRelativeRestriction F hE τ).toRingEquiv with
      commutes' := fun k => Subtype.ext ?_ }, ?_⟩
    · change ((absoluteRelativeRestriction F hE τ (algebraMap K.Carrier _ k) :
        (extendFiniteGalois hE).toIntermediateField) : AlgebraicClosure F.Carrier) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k
      rw [hρ]
      exact hk k
    · apply AlgEquiv.ext
      intro y
      rfl

/-- If every element of `G_F^{u₀}` fixing `K` fixes `E`, then the upper group of `M/K` of
index `ψ_{K/F}(u₀)` lies in `Gal(M/E)`. -/
theorem upperRamificationGroup_le_range_of_fix {u₀ : ℝ} (hu₀ : -1 ≤ u₀)
    (hfix : ∀ τ ∈ absoluteUpperRamificationGroup F u₀,
      (∀ k : K.Carrier, AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) →
      ∀ x : E.Carrier, AlgEquiv.toAlgHom τ (algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) =
        algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) :
    Padic.upperRamificationGroup
        (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData K.Carrier
        (relativeIndex F M (algebraMap_mem_of_tower F K hE) u₀) ≤
      (AlgEquiv.restrictScalarsHom K.Carrier :
        ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[E.Carrier]
          (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier) →*
        ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[K.Carrier]
          (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier)).range := by
  intro σ hσ
  rw [relativeIndex_eq_tower F K hE] at hσ
  have h1 := (restrictScalars_mem_upperRamificationGroup_iff F.Carrier K.Carrier
    (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData u₀ σ).mpr hσ
  rw [← map_absoluteRelativeRestriction_upper F hE hu₀] at h1
  obtain ⟨τ, hτ, hτσ⟩ := h1
  have hK : ∀ k : K.Carrier,
      AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k :=
    (absoluteRelativeRestriction_mem_range_iff F K hE τ).mp ⟨σ, hτσ.symm⟩
  have hmem : τ ∈ (relativeSubgroup F hE).comap (absoluteRelativeRestriction F hE) :=
    (mem_comap_absoluteRelativeRestriction_iff F hE τ).mpr (hfix τ hτ hK)
  obtain ⟨σ', hσ'⟩ := hmem
  refine ⟨σ', ?_⟩
  apply AlgEquiv.ext
  intro y
  exact congrArg (fun π : _ ≃ₐ[F.Carrier] _ => π y) (hσ'.trans hτσ)

/-- The slope of `ψ_{E/K}` past an index whose group fixes `E`. -/
theorem towerIndex_sub_eq {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hfix : ∀ τ ∈ absoluteUpperRamificationGroup F u₀,
      (∀ k : K.Carrier, AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) →
      ∀ x : E.Carrier, AlgEquiv.toAlgHom τ (algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) =
        algebraMap E.Carrier (AlgebraicClosure F.Carrier) x)
    {s t : ℝ} (hs : relativeIndex F M (algebraMap_mem_of_tower F K hE) u₀ ≤ s) (hst : s ≤ t) :
    towerIndex F K hE t - towerIndex F K hE s = (towerRatio F K hE : ℝ) * (t - s) := by
  have hv₀ : 0 ≤ relativeIndex F M (algebraMap_mem_of_tower F K hE) u₀ := by
    rw [relativeIndex_eq_tower F K hE]
    have h := (Padic.herbrandPhi_strictMono
      (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData K.Carrier).monotone
      ((Padic.herbrandPsi_strictMono
        (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
        F.Carrier).monotone hu₀)
    simpa using h
  exact herbrandPhi_herbrandPsi_sub_eq K.Carrier E.Carrier _ hv₀
    (upperRamificationGroup_le_range_of_fix F K hE (by linarith) hfix) hs hst

/-- `[G_0 : G_0 ∩ Gal(M/E)] · [I_F : I_F ∩ G_K] = [I_F : I_F ∩ G_E]`. -/
theorem towerRatio_mul_relIndex (SK SE : Subgroup (Field.absoluteGaloisGroup F.Carrier))
    (hSK : ∀ τ, τ ∈ SK ↔ ∀ k : K.Carrier,
      AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k)
    (hSE : ∀ τ, τ ∈ SE ↔ ∀ x : E.Carrier,
      AlgEquiv.toAlgHom τ (algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) =
        algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) :
    towerRatio F K hE * SK.relIndex (F.absoluteInertia F.canonicalTopologicalData) =
      SE.relIndex (F.absoluteInertia F.canonicalTopologicalData) := by
  set T := (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
  set HK := (AlgEquiv.restrictScalarsHom F.Carrier :
    ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[K.Carrier]
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier) →*
    ((finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier ≃ₐ[F.Carrier]
      (finiteGaloisPadicField E (extendFiniteGalois hE)).Carrier)).range
  have hlow0 : Padic.lowerRamificationGroup T F.Carrier 0 =
      (F.absoluteInertia F.canonicalTopologicalData).map (absoluteRelativeRestriction F hE) := by
    rw [← absoluteUpperCanonicalInertia F, map_absoluteRelativeRestriction_upper F hE (by norm_num),
      Padic.upperRamificationGroup_zero, ← Padic.lowerRamificationGroupReal_nat, Nat.cast_zero,
      Padic.lowerRamificationGroupReal_zero]
  have hE' : (relativeSubgroup F hE).relIndex (Padic.lowerRamificationGroup T F.Carrier 0) =
      SE.relIndex (F.absoluteInertia F.canonicalTopologicalData) := by
    rw [relativeSubgroup_relIndex_eq F hE]
    congr 1
    ext τ
    rw [hSE]
    exact mem_comap_absoluteRelativeRestriction_iff F hE τ
  have hK' : HK.relIndex (Padic.lowerRamificationGroup T F.Carrier 0) =
      SK.relIndex (F.absoluteInertia F.canonicalTopologicalData) := by
    rw [hlow0, ← Subgroup.relIndex_comap]
    congr 1
    ext τ
    rw [hSK]
    exact absoluteRelativeRestriction_mem_range_iff F K hE τ
  have h1 := lowerGroupOrder_subfield_mul_relIndex F.Carrier E.Carrier T 0
  have h2 := lowerGroupOrder_subfield_mul_relIndex F.Carrier K.Carrier T 0
  have h3 := lowerGroupOrder_subfield_mul_relIndex K.Carrier E.Carrier T 0
  have hpos := lowerGroupOrder_pos T E.Carrier 0
  rw [← hE', ← hK']
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← mul_assoc]
  change Padic.lowerGroupOrder T E.Carrier 0 * towerRatio F K hE * _ = _
  unfold towerRatio
  rw [h3, h2, h1]

/-- DH81 3.12(i) along the tower: if every element of `G_F^{u₀}` fixing `K` fixes `E`, where
`ψ_{K/F}(u₀) = n ≥ 1`, then the first-order norm–trace congruence holds for `E/K` at the
level `n` of `K` and the layer `ψ_{E/K}(n)` of `E`. -/
theorem topLayer_of_fix
    (htop : LocalFactor.NonabelianSystem.DeligneHenniart.TopLayerNormTraceStatement.{uK, uE, u})
    {n : ℕ} (hn : 1 ≤ n) {u₀ : ℝ} (hu₀ : -1 ≤ u₀)
    (hn₀ : relativeIndex F M (algebraMap_mem_of_tower F K hE) u₀ = n)
    (hfix : ∀ τ ∈ absoluteUpperRamificationGroup F u₀,
      (∀ k : K.Carrier, AlgEquiv.toAlgHom τ (algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k) →
      ∀ x : E.Carrier, AlgEquiv.toAlgHom τ (algebraMap E.Carrier (AlgebraicClosure F.Carrier) x) =
        algebraMap E.Carrier (AlgebraicClosure F.Carrier) x)
    (y : E.Carrier) (hy : y ≠ 0)
    (hord : towerIndex F K hE n ≤ (E.canonicalTopologicalData.ord y : ℝ)) :
    Algebra.trace K.Carrier E.Carrier y ∈ K.canonicalTopologicalData.additiveLattice (-(n : ℤ)) ∧
      ∀ (z : E.Carrierˣ) (t : K.Carrierˣ), (z : E.Carrier) = 1 + y →
        (t : K.Carrier) = 1 + Algebra.trace K.Carrier E.Carrier y →
        Units.map (Algebra.norm K.Carrier) z * t⁻¹ ∈
          K.canonicalTopologicalData.principalUnits (n + 1) := by
  set P := finiteGaloisPadicField E (extendFiniteGalois hE) with hP
  haveI : IsScalarTower (Padic p) K.Carrier E.Carrier := IsScalarTower.of_algebraMap_eq fun q => by
    apply (algebraMap E.Carrier (AlgebraicClosure F.Carrier)).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower K.Carrier E.Carrier P.Carrier := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K.Carrier E.Carrier (AlgebraicClosure F.Carrier) x)
  haveI : IsScalarTower (Padic p) E.Carrier P.Carrier := IsScalarTower.of_algebraMap_eq fun q =>
    Subtype.ext
      (IsScalarTower.algebraMap_apply (Padic p) E.Carrier (AlgebraicClosure F.Carrier) q)
  haveI : IsScalarTower (Padic p) K.Carrier P.Carrier := IsScalarTower.of_algebraMap_eq fun q =>
    Subtype.ext
      (IsScalarTower.algebraMap_apply (Padic p) K.Carrier (AlgebraicClosure F.Carrier) q)
  haveI : FiniteDimensional K.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier E.Carrier
  haveI : FiniteDimensional E.Carrier P.Carrier := (extendFiniteGalois hE).finiteDimensional
  haveI : FiniteDimensional K.Carrier P.Carrier :=
    FiniteDimensional.trans K.Carrier E.Carrier P.Carrier
  haveI : IsGalois F.Carrier P.Carrier := M.isGalois
  haveI : IsGalois K.Carrier P.Carrier :=
    IsGalois.tower_top_of_isGalois F.Carrier K.Carrier P.Carrier
  have hn1 : (-1 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨w, -, hw, heq⟩ :=
    exists_lt_upperRamificationGroup_eq P.canonicalTopologicalData K.Carrier hn1
  have hrange := upperRamificationGroup_le_range_of_fix F K hE hu₀ hfix
  rw [hn₀] at hrange
  refine htop p K E P K.canonicalTopologicalData E.canonicalTopologicalData
    P.canonicalTopologicalData n hn ⟨w, hw, fun σ hσ x => ?_⟩ y hy hord
  rw [heq] at hσ
  obtain ⟨σ', rfl⟩ := hrange hσ
  exact σ'.commutes x

omit [Algebra K.Carrier (AlgebraicClosure F.Carrier)] [Algebra F.Carrier K.Carrier]
  [Algebra K.Carrier E.Carrier] [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower K.Carrier E.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)] in
/-- The relative index `ψ_{E/F}` takes every value `v ≥ 0` at some `u ≥ 0`. -/
theorem exists_relativeIndex_eq {v : ℝ} (hv : 0 ≤ v) :
    ∃ u : ℝ, 0 ≤ u ∧ relativeIndex F M hE u = v := by
  set T := (finiteGaloisPadicField E (extendFiniteGalois hE)).canonicalTopologicalData
  refine ⟨Padic.herbrandPhi T F.Carrier (Padic.herbrandPsi T E.Carrier v), ?_, ?_⟩
  · have h1 := (Padic.herbrandPsi_strictMono T E.Carrier).monotone hv
    have h2 := (Padic.herbrandPhi_strictMono T F.Carrier).monotone h1
    simpa using h2
  · show Padic.herbrandPhi T E.Carrier (Padic.herbrandPsi T F.Carrier
      (Padic.herbrandPhi T F.Carrier (Padic.herbrandPsi T E.Carrier v))) = v
    rw [Padic.herbrandPsi_herbrandPhi, Padic.herbrandPhi_herbrandPsi]

end Tower

end Langlands.Ramification.HerbrandBridge

universe uF

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure Weil.Local VirtualRepresentation.LocalWeil.Ramification
open Ramification.HerbrandBridge Ramification.Padic LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

attribute [local instance] asPadicField_isScalarTower

section Single

variable (E : Extension F)

/-- `ψ_{E/F}` takes every value `v ≥ 0` at some `u ≥ 0`. -/
theorem exists_relativeHerbrandPsi_eq {v : ℝ} (hv : 0 ≤ v) :
    ∃ u : ℝ, 0 ≤ u ∧ relativeHerbrandPsi E u = v :=
  exists_relativeIndex_eq F (algebraMap_mem_galoisClosure E) hv

/-- The two carried upper groups of `W_E` agree: both come from `intermediateWeilEquiv`. -/
theorem intermediateUpperGroup_eq_weilUpperSubgroup (s : ℝ) :
    intermediateUpperGroup F E s = weilUpperSubgroup F E s := by
  ext g
  exact mem_intermediateUpperGroup F E g

end Single

section Relative

variable (E L : Extension F) (h : E.field ≤ L.field)

/-- The relative inverse Herbrand function `ψ_{L/E}` of an inclusion `E ≤ L` of finite
intermediate fields, computed as `φ_{M/L} ∘ ψ_{M/E}` in the Galois closure `M` of `L`
over the base field. -/
def intermediateHerbrandPsi (v : ℝ) : ℝ :=
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  towerIndex F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) v

theorem intermediateHerbrandPsi_zero : intermediateHerbrandPsi F E L h 0 = 0 := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact towerIndex_zero F _ _

theorem intermediateHerbrandPsi_continuous : Continuous (intermediateHerbrandPsi F E L h) := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact towerIndex_continuous F _ _

theorem intermediateHerbrandPsi_strictMono : StrictMono (intermediateHerbrandPsi F E L h) := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact towerIndex_strictMono F _ _

include h in
/-- The Galois closure of `E` lies in that of `L`. -/
theorem galoisClosure_le : galoisClosure E ≤ galoisClosure L :=
  (FiniteGaloisIntermediateField.le_iff _ _).mpr (IntermediateField.normalClosure_mono _ _ h)

/-- Transitivity: `ψ_{L/E} ∘ ψ_{E/F} = ψ_{L/F}`. -/
theorem intermediateHerbrandPsi_relativeHerbrandPsi (u : ℝ) :
    intermediateHerbrandPsi F E L h (relativeHerbrandPsi E u) = relativeHerbrandPsi L u := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key := towerIndex_relativeIndex F (E.asPadicField (p := p))
    (algebraMap_mem_galoisClosure L) u
  rw [relativeIndex_eq_of_le (galoisClosure_le F E L h) (algebraMap_mem_galoisClosure E)] at key
  exact key

/-- Herbrand's subgroup formula for `E ≤ L` on the carried upper groups:
`W_E^v ∩ W_L = W_L^{ψ_{L/E}(v)}` for `v ≥ 0`. -/
theorem weilInclusion_mem_intermediateUpperGroup_iff {v : ℝ} (hv : 0 ≤ v)
    (g : weilSubgroup F L) :
    weilInclusion F E L h g ∈ intermediateUpperGroup F E v ↔
      g ∈ intermediateUpperGroup F L (intermediateHerbrandPsi F E L h v) := by
  obtain ⟨u, hu, rfl⟩ := exists_relativeHerbrandPsi_eq F E hv
  rw [intermediateHerbrandPsi_relativeHerbrandPsi, intermediateUpperGroup_eq_weilUpperSubgroup,
    intermediateUpperGroup_eq_weilUpperSubgroup, ← coe_mem_upperGroup_iff F E (by linarith),
    ← coe_mem_upperGroup_iff F L (by linarith)]
  rfl

/-- If `W_E^{ψ_{E/F}(u₀)} ⊆ W_L` with `u₀ ≥ 0`, then every element of `G_F^{u₀}` fixing `E`
fixes `L`. -/
theorem fix_of_intermediateUpperGroup_le {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hW : ∀ g ∈ intermediateUpperGroup F E (relativeHerbrandPsi E u₀),
      (g : localWeilGroup F) ∈ weilSubgroup F L)
    (τ : Field.absoluteGaloisGroup F.Carrier) (hτ : τ ∈ absoluteUpperRamificationGroup F u₀)
    (hτE : ∀ k : (E.asPadicField (p := p)).Carrier,
      AlgEquiv.toAlgHom τ (algebraMap _ (AlgebraicClosure F.Carrier) k) =
        algebraMap _ (AlgebraicClosure F.Carrier) k)
    (x : (L.asPadicField (p := p)).Carrier) :
    AlgEquiv.toAlgHom τ (algebraMap _ (AlgebraicClosure F.Carrier) x) =
      algebraMap _ (AlgebraicClosure F.Carrier) x := by
  have hτ0 : τ ∈ F.absoluteInertia F.canonicalTopologicalData := by
    rw [← absoluteUpperCanonicalInertia F]
    exact absoluteUpperRamificationGroup_antitone F hu₀ hτ
  set w : localInertia F := (localInertiaEquiv F).symm ⟨τ, hτ0⟩
  have hwτ : localProjection F (w : localWeilGroup F) = τ :=
    congrArg Subtype.val ((localInertiaEquiv F).apply_symm_apply ⟨τ, hτ0⟩)
  have hw : (w : localWeilGroup F) ∈ upperGroup F u₀ := by
    change localProjection F (w : localWeilGroup F) ∈ absoluteUpperRamificationGroup F u₀
    rw [hwτ]
    exact hτ
  have hwE : (w : localWeilGroup F) ∈ weilSubgroup F E := by
    change localProjection F (w : localWeilGroup F) ∈ E.field.fixingSubgroup
    rw [hwτ]
    exact (IntermediateField.mem_fixingSubgroup_iff E.field τ).mpr fun y hy => hτE ⟨y, hy⟩
  have hg : (⟨w, hwE⟩ : weilSubgroup F E) ∈
      intermediateUpperGroup F E (relativeHerbrandPsi E u₀) := by
    rw [intermediateUpperGroup_eq_weilUpperSubgroup, ← coe_mem_upperGroup_iff F E (by linarith)]
    exact hw
  have hwL : localProjection F (w : localWeilGroup F) ∈ L.field.fixingSubgroup := hW _ hg
  rw [hwτ] at hwL
  exact (IntermediateField.mem_fixingSubgroup_iff L.field τ).mp hwL x.1 x.2

/-- The index `[G_0 : G_0 ∩ Gal(M/L)]` of the tower `E ≤ L` is the relative ramification
index: `[G_0 : G_0 ∩ Gal(M/L)] · e_E = e_L`. -/
theorem towerRatio_mul_ramificationIndex :
    letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
      (IntermediateField.inclusion h).toAlgebra
    letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
        (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (towerRatio F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) : ℝ) *
        (fieldData F E).ramificationIndex =
      (fieldData F L).ramificationIndex := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key := towerRatio_mul_relIndex F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L)
    E.field.fixingSubgroup L.field.fixingSubgroup
    (fun τ => (IntermediateField.mem_fixingSubgroup_iff E.field τ).trans
      ⟨fun hk k => hk k.1 k.2, fun hk x hx => hk ⟨x, hx⟩⟩)
    (fun τ => (IntermediateField.mem_fixingSubgroup_iff L.field τ).trans
      ⟨fun hk k => hk k.1 k.2, fun hk x hx => hk ⟨x, hx⟩⟩)
  rw [fieldData_ramificationIndex_eq E, fieldData_ramificationIndex_eq L, ← mul_assoc]
  congr 1
  exact_mod_cast key

/-- DH81 3.2(iii) for `E ≤ L`: if `W_E^{ψ_{E/F}(u₀)} ⊆ W_L` with `u₀ ≥ 0`, then
`e_E (ψ_{L/E}(t) - ψ_{L/E}(s)) = e_L (t - s)` for `ψ_{E/F}(u₀) ≤ s ≤ t`. -/
theorem ramificationIndex_mul_intermediateHerbrandPsi_sub {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hW : ∀ g ∈ intermediateUpperGroup F E (relativeHerbrandPsi E u₀),
      (g : localWeilGroup F) ∈ weilSubgroup F L)
    {s t : ℝ} (hs : relativeHerbrandPsi E u₀ ≤ s) (hst : s ≤ t) :
    ((fieldData F E).ramificationIndex : ℝ) *
        (intermediateHerbrandPsi F E L h t - intermediateHerbrandPsi F E L h s) =
      (fieldData F L).ramificationIndex * (t - s) := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hs' : relativeIndex F (galoisClosure L) (algebraMap_mem_of_tower F (E.asPadicField (p := p))
      (algebraMap_mem_galoisClosure L)) u₀ ≤ s := by
    rw [relativeIndex_eq_of_le (galoisClosure_le F E L h) (algebraMap_mem_galoisClosure E)]
    exact hs
  have key := towerIndex_sub_eq F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) hu₀
    (fun τ hτ hτE => fix_of_intermediateUpperGroup_le F E L hu₀ hW τ hτ hτE) hs' hst
  have hr : (towerRatio F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) : ℝ) *
      (fieldData F E).ramificationIndex = (fieldData F L).ramificationIndex :=
    towerRatio_mul_ramificationIndex F E L h
  change _ * (towerIndex F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) t -
    towerIndex F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) s) = _
  rw [key, ← hr]
  ring

/-- `e_E ψ_{L/E}(s) ≤ e_L s` for `s ≥ 0`. -/
theorem ramificationIndex_mul_intermediateHerbrandPsi_le {s : ℝ} (hs : 0 ≤ s) :
    ((fieldData F E).ramificationIndex : ℝ) * intermediateHerbrandPsi F E L h s ≤
      (fieldData F L).ramificationIndex * s := by
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key := towerIndex_le_mul F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) hs
  have hr : (towerRatio F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) : ℝ) *
      (fieldData F E).ramificationIndex = (fieldData F L).ramificationIndex :=
    towerRatio_mul_ramificationIndex F E L h
  have heE : (0 : ℝ) ≤ (fieldData F E).ramificationIndex := Nat.cast_nonneg _
  calc ((fieldData F E).ramificationIndex : ℝ) * intermediateHerbrandPsi F E L h s
      ≤ (fieldData F E).ramificationIndex *
          ((towerRatio F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) : ℝ) * s) :=
        mul_le_mul_of_nonneg_left key heE
    _ = (fieldData F L).ramificationIndex * s := by
        rw [← hr]
        ring

/-- The relative Herbrand input of DH81 4.7 for `E ≤ L`, whenever `W_E^{b/2} ⊆ W_L`. -/
theorem herbrandInputRel_of_le {b : ℕ}
    (hW : ∀ g ∈ intermediateUpperGroup F E ((b : ℝ) / 2),
      (g : localWeilGroup F) ∈ weilSubgroup F L) :
    HerbrandInputRel F E L h b := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  obtain ⟨u₀, hu₀, hψ⟩ := exists_relativeHerbrandPsi_eq F E (by positivity : (0 : ℝ) ≤ b / 2)
  refine ⟨intermediateHerbrandPsi F E L h, intermediateHerbrandPsi_continuous F E L h,
    intermediateHerbrandPsi_strictMono F E L h, intermediateHerbrandPsi_zero F E L h,
    fun v hv g => weilInclusion_mem_intermediateUpperGroup_iff F E L h hv g, ?_,
    ramificationIndex_mul_intermediateHerbrandPsi_le F E L h hb0⟩
  rw [ramificationIndex_mul_intermediateHerbrandPsi_sub F E L h hu₀ (by rw [hψ]; exact hW)
    hψ.le (by linarith)]
  ring

/-- The approximate Herbrand input of DH81 4.3–4.4 for `E ≤ L` relative to the carried
upper groups of `E`, whenever `W_E^b ⊆ W_L`, from the first-order norm–trace congruence
(DH81 3.12(i)). -/
theorem approximateHerbrandInput_of_le
    (htop : TopLayerNormTraceStatement.{uF, uF, uF}) {b : ℕ} (hb : 1 ≤ b)
    (hW : ∀ g ∈ intermediateUpperGroup F E (b : ℝ),
      (g : localWeilGroup F) ∈ weilSubgroup F L) :
    ApproximateHerbrandInput F E L h (intermediateUpperGroup F E) b := by
  obtain ⟨u₀, hu₀, hψ⟩ := exists_relativeHerbrandPsi_eq F E (Nat.cast_nonneg (α := ℝ) b)
  refine ⟨intermediateHerbrandPsi F E L h, intermediateHerbrandPsi_continuous F E L h,
    intermediateHerbrandPsi_strictMono F E L h, intermediateHerbrandPsi_zero F E L h,
    fun v hv g => weilInclusion_mem_intermediateUpperGroup_iff F E L h hv g, ?_⟩
  intro y hy hord
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn₀ : relativeIndex F (galoisClosure L) (algebraMap_mem_of_tower F (E.asPadicField (p := p))
      (algebraMap_mem_galoisClosure L)) u₀ = b := by
    rw [relativeIndex_eq_of_le (galoisClosure_le F E L h) (algebraMap_mem_galoisClosure E)]
    exact hψ
  exact topLayer_of_fix F (E.asPadicField (p := p)) (algebraMap_mem_galoisClosure L) htop hb
    (by linarith) hn₀
    (fun τ hτ hτE => fix_of_intermediateUpperGroup_le F E L hu₀ (by rw [hψ]; exact hW) τ hτ hτE)
    y hy hord

end Relative

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
