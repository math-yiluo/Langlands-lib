import Langlands.TraceFormula.RationalLocalGeneralLinear
import Langlands.TraceFormula.SplitRationalOrbitIsolation
import Langlands.Global.CompletionPadic

/-! # Rational orbit isolation in the actual completed split algebra -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ComplexOrder TensorProduct

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme
open AdelicGroupAutomorphism BaseChange HarmonicAnalysis JacquetLanglands

universe u

section LocalCoordinates

variable (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L]
  (v : FinitePlace K) (m n : ℕ)

local notation "Fᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)
local notation "Sᵥ" => Fin (m + 1) → Fᵥ

local instance : Algebra Fᵥ Eᵥ := LocalBaseChangeAlgebra.algebra K L (.inr v)

/-- An algebra splitting of the completed tensor algebra gives the
corresponding group isomorphism on invertible matrices. -/
def localSplitGLEquiv (c : Eᵥ ≃ₐ[Fᵥ] Sᵥ) :
    GeneralLinear n Eᵥ ≃* GeneralLinear n Sᵥ :=
  Units.mapEquiv c.toRingEquiv.mapMatrix.toMulEquiv

/-- The isomorphism on local matrices respects their actual topologies. -/
def localSplitGLHomeomorph [FiniteDimensional K L] (c : Eᵥ ≃ₐ[Fᵥ] Sᵥ) :
    GeneralLinear n Eᵥ ≃ₜ* GeneralLinear n Sᵥ where
  toMulEquiv := localSplitGLEquiv K L v m n c
  continuous_toFun := by
    have : IsModuleTopology Fᵥ Eᵥ := LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)
    have h : Continuous c.toRingHom := IsModuleTopology.continuous_of_linearMap c.toLinearMap
    exact h.generalLinearGroup_map
  continuous_invFun := by
    have : IsModuleTopology Fᵥ Eᵥ := LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)
    have h : Continuous c.symm.toRingHom := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
    exact h.generalLinearGroup_map

private theorem localSplitGLEquiv_entrywiseAut
    (σ : L ≃ₐ[K] L) (c : Eᵥ ≃ₐ[Fᵥ] Sᵥ)
    (hc : ∀ z, c (localGalois K L σ (.inr v) z) = splitCyclicShift Fᵥ (m + 1) (c z))
    (g : GeneralLinear n Eᵥ) :
    localSplitGLEquiv K L v m n c (entrywiseAut (localGalois K L σ (.inr v)) n g) =
      entrywiseAut (splitCyclicShift Fᵥ (m + 1)) n (localSplitGLEquiv K L v m n c g) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact hc (g i j)

/-- The splitting transports norm association to the cyclic shift. -/
theorem localSplitGLEquiv_normAssociated
    (σ : L ≃ₐ[K] L) (c : Eᵥ ≃ₐ[Fᵥ] Sᵥ)
    (hc : ∀ z, c (localGalois K L σ (.inr v) z) = splitCyclicShift Fᵥ (m + 1) (c z))
    {δ : GeneralLinear n Eᵥ} {g₀ : GeneralLinear n Fᵥ}
    (h : IsNormAssociated (localGalois K L σ (.inr v)) (m + 1) δ g₀) :
    IsNormAssociated (splitCyclicShift Fᵥ (m + 1)) (m + 1)
      (localSplitGLEquiv K L v m n c δ) g₀ := by
  let e := localSplitGLEquiv K L v m n c
  let τ := splitCyclicShift Fᵥ (m + 1)
  have hpow (k : ℕ) (z : Eᵥ) : c ((localGalois K L σ (.inr v) ^ k) z) = (τ ^ k) (c z) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc, ih]
  have hnorm : e (cyclicNorm (localGalois K L σ (.inr v)) (m + 1) δ) =
      cyclicNorm τ (m + 1) (e δ) := by
    rw [cyclicNorm, cyclicNorm, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    apply Units.ext
    apply Matrix.ext
    intro i j
    change c ((localGalois K L σ (.inr v) ^ k) (δ i j)) = (τ ^ k) (c (δ i j))
    exact hpow k (δ i j)
  obtain ⟨y, hy⟩ := h
  refine ⟨e y, ?_⟩
  rw [← hnorm, ← map_inv, ← map_mul, ← map_mul, hy]
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact c.commutes (g₀ i j)

end LocalCoordinates

local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

local instance {K L : Type u} [Field K] [Field L] [NumberField K] [Algebra K L]
    (v : FinitePlace K) : Algebra (v.adicCompletion K) (LocalBaseChangeAlgebra K L (.inr v)) :=
  LocalBaseChangeAlgebra.algebra K L (.inr v)

local instance {A : Type u} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    MeasurableSpace (GeneralLinear n A) := borel _
local instance {A : Type u} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    BorelSpace (GeneralLinear n A) := ⟨rfl⟩

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Fᵥ" => v.adicCompletion K

/-- In the actual split completion, the ordinary and upper test functions
isolate the selected rational point classes from finite lists of competitors. -/
def FinitePlaceOrbitIsolationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlace K) (m n : ℕ) (σ : L ≃ₐ[K] L), IsCyclicAlgebra σ (m + 1) →
    ∀ (c : LocalBaseChangeAlgebra K L (.inr v) ≃ₐ[Fᵥ] (Fin (m + 1) → Fᵥ)),
      (∀ z, c (localGalois K L σ (.inr v) z) = splitCyclicShift Fᵥ (m + 1) (c z)) →
      let G := GeneralLinear n Fᵥ
      let E := GeneralLinear n (Fin (m + 1) → Fᵥ)
      let τ := splitCyclicShift Fᵥ (m + 1)
      let κ := splitGLCoordinates Fᵥ n (m + 1)
      let eF := localGLEquiv K n (.inr v)
      let eE := (localPointsEquiv K L n (.inr v)).trans (localSplitGLEquiv K L v m n c)
      let rF := GeneralLinearGroupPoints.rationalEquiv K n
      let rE := rationalWeilGLEquiv K L n
      let gF := AdelicGroupPoints.rational K GLₙ
      let gE := AdelicGroupPoints.rational K Wₙ
      let pF := AdelicGroupPoints.atPlace K GLₙ (.inr v)
      let pE := AdelicGroupPoints.atPlace K Wₙ (.inr v)
      let θloc := (Wₙ).affinePointsTarget (unitGaloisAut K L GLₙ σ).hom (placeCompletion K (.inr v))
      let θrat := (Wₙ).affinePointsTarget (unitGaloisAut K L GLₙ σ).hom (CommAlgCat.of K K)
      ∀ (R : Finset (RationalGroupPoints K GLₙ)) (T : Finset (RationalGroupPoints K Wₙ))
        (q₀ : RationalGroupPoints K GLₙ) (t₀ : RationalGroupPoints K Wₙ),
        IsRegularSemisimple (rF q₀) → IsNormAssociated σ (m + 1) (rE t₀) (rF q₀) →
        ∀ (ρF : Measure G) [ρF.IsHaarMeasure] (ρE : Measure E) [ρE.IsHaarMeasure],
          IsSplitProductHaar ρF ρE → ∀ (A : Set (Fin (m + 1) → G)) (V : Set G),
          IsOpen A → κ (eE (pE (gE t₀))) ∈ A →
          IsOpen V → (List.ofFn (κ (eE (pE (gE t₀))))).prod ∈ V →
          ∃ ψ : Fin (m + 1) → SchwartzBruhat G,
            let φ := splitTensor fun i ↦ (ψ i : G → ℂ)
            let f := convolutionProduct ρF ψ
            AreConcordant τ (m + 1) ρF ρE φ (f : G → ℂ) ∧
            φ (eE (pE (gE t₀))) = 1 ∧ tsupport φ ⊆ κ ⁻¹' A ∧ tsupport (f : G → ℂ) ⊆ V ∧
            (∀ g, 0 ≤ f g) ∧ 0 < f (List.ofFn (κ (eE (pE (gE t₀))))).prod ∧
            (∀ q ∈ R, (∃ x : PlaceGroupPoints K GLₙ (.inr v),
              f (eF (x⁻¹ * pF (gF q) * x)) ≠ 0) →
              ∃ a : RationalGroupPoints K GLₙ, a⁻¹ * q * a = q₀) ∧
            (∀ t ∈ T, (∃ y : PlaceGroupPoints K Wₙ (.inr v),
              φ (eE (y⁻¹ * pE (gE t) * θloc y)) ≠ 0) →
              ∃ a : RationalGroupPoints K Wₙ, a⁻¹ * t * θrat a = t₀)

set_option maxRecDepth 2500 in
set_option maxHeartbeats 1200000 in
theorem finitePlaceOrbitIsolation : FinitePlaceOrbitIsolationStatement.{u} := by
  classical
  intro K L _ _ _ _ _ v m n σ hσ c hc G E τ κ eF eE rF rE gF gE pF pE θloc θrat
    R T q₀ t₀ hreg hassoc ρF _ ρE _ hρ A V hA ht₀A hV ht₀V
  let F := v.adicCompletion K
  let : ValuativeRel F := (CompletionPadic.topologicalData v).valuativeRel
  let : IsNonarchimedeanLocalField F := (CompletionPadic.topologicalData v).localField
  let d := localSplitGLEquiv K L v m n c
  let baseMap := algebraMap K F
  let s := d.toMonoidHom.comp
    (Matrix.GeneralLinearGroup.map (n := Fin n) (upperRationalLocalMap K L (.inr v)).toRingHom)
  have hs (δ : GeneralLinear n L) (q : GeneralLinear n K) (h : IsNormAssociated σ (m + 1) δ q) :
      IsNormAssociated τ (m + 1) (s δ) (Matrix.GeneralLinearGroup.map baseMap q) :=
    localSplitGLEquiv_normAssociated K L v m n σ c hc
      (localize_normAssociated K L σ (m + 1) n (.inr v) δ q h)
  have hlocF (q : RationalGroupPoints K GLₙ) :
      eF (pF (gF q)) = Matrix.GeneralLinearGroup.map baseMap (rF q) :=
    localGLEquiv_atPlace_rational K n (.inr v) q
  have hlocE (t : RationalGroupPoints K Wₙ) : eE (pE (gE t)) = s (rE t) := by
    change d (localPointsEquiv K L n (.inr v) (pE (gE t))) = _
    rw [localPointsEquiv_atPlace_rational]
    rfl
  have htwE (x : PlaceGroupPoints K Wₙ (.inr v)) : eE (θloc x) = entrywiseAut τ n (eE x) := by
    exact (congrArg d (localPointsEquiv_twist K L σ n (.inr v) x)).trans
      (localSplitGLEquiv_entrywiseAut K L v m n σ c hc _)
  have hA' : κ (s (rE t₀)) ∈ A := hlocE t₀ ▸ ht₀A
  have hV' : (List.ofFn (κ (s (rE t₀)))).prod ∈ V := hlocE t₀ ▸ ht₀V
  obtain ⟨ψ, hmatch, hvalue, hsuppE, hsuppF, hnonneg, hpos, hclassF, hclassE⟩ :=
    splitRationalOrbitIsolation K L F n m σ hσ baseMap s hs (R.image rF) (T.image rE) (rE t₀) (rF q₀)
      hreg hassoc ρF ρE hρ A V hA hA' hV hV'
  refine ⟨ψ, hmatch, ?_, hsuppE, hsuppF, hnonneg, ?_, ?_, ?_⟩
  · simpa only [hlocE] using hvalue
  · simpa only [hlocE] using hpos
  · rintro q hq ⟨x, hx⟩
    rw [map_mul, map_mul, map_inv, hlocF] at hx
    obtain ⟨a, ha⟩ := hclassF (rF q) (Finset.mem_image_of_mem rF hq)
      ⟨eF x, hx⟩
    refine ⟨rF.symm a, rF.injective ?_⟩
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using ha
  · rintro t ht ⟨y, hy⟩
    rw [map_mul, map_mul, map_inv, hlocE, htwE] at hy
    obtain ⟨a, ha⟩ := hclassE (rE t) (Finset.mem_image_of_mem rE ht)
      ⟨eE y, hy⟩
    refine ⟨rE.symm a, rE.injective ?_⟩
    have htw (b : RationalGroupPoints K Wₙ) : rE (θrat b) = entrywiseAut σ n (rE b) :=
      rationalWeilGLEquiv_twist K L n σ b
    simpa only [map_mul, map_inv, htw, MulEquiv.apply_symm_apply] using ha

end Langlands.TraceFormula
