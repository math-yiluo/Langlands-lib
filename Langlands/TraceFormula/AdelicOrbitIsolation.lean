import Langlands.TraceFormula.AdelicRationalTwistedFiniteness
import Langlands.TraceFormula.FinitePlaceOrbitIsolation

/-! # Isolating one rational class in each norm-one adelic group -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ComplexOrder

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open AdelicGroupAutomorphism BaseChange HarmonicAnalysis JacquetLanglands

universe u

private theorem isTwistedConjugate_of_finiteSupportCutoff {H : Type u} [Group H]
    (Q : Subgroup H) (θ : H →* H) (C : Set H) (T : Finset Q) (r₀ : H)
    (hT : ∀ r : Q, (∃ x : H, twistedConj θ x r.val ∈ C) →
      ∃ t ∈ T, IsTwistedConjugate Q θ r.val t.val)
    (f : H → ℂ) (hf : Function.support f ⊆ C)
    (hcut : ∀ t ∈ T, (∃ x : H, f (twistedConj θ x (t : H)) ≠ 0) →
      IsTwistedConjugate Q θ (t : H) r₀)
    (r : Q) (h : ∃ x : H, f (twistedConj θ x (r : H)) ≠ 0) :
    IsTwistedConjugate Q θ (r : H) r₀ := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨t, ht, y, hy, hyt⟩ := hT r ⟨x, hf hx⟩
  change twistedConj θ y (r : H) = (t : H) at hyt
  have ht' : f (twistedConj θ (y⁻¹ * x) (t : H)) ≠ 0 := by
    rwa [← hyt, twistedConj_mul, mul_inv_cancel_left]
  obtain ⟨z, hz, hz₀⟩ := hcut t ht ⟨y⁻¹ * x, ht'⟩
  refine ⟨y * z, Q.mul_mem hy hz, ?_⟩
  change twistedConj θ (y * z) (r : H) = r₀
  rw [← twistedConj_mul, hyt]
  exact hz₀

private local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

private local instance (K : Type u) [Field K] (n : ℕ) :
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

private theorem exists_finite_ordinary_normOneClasses
    (K : Type u) [Field K] [NumberField K] (n : ℕ) (v : FinitePlace K)
    (C : Set (normOneSubgroup K GLₙ)) (hC : IsCompact C)
    (hEll : ∀ g ∈ C, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g)))) :
    ∃ R : Finset (rationalNormOneSubgroup K GLₙ), ∀ r : rationalNormOneSubgroup K GLₙ,
      (∃ x : normOneSubgroup K GLₙ, x⁻¹ * r.val * x ∈ C) →
      ∃ t ∈ R, IsTwistedConjugate (rationalNormOneSubgroup K GLₙ)
        (MonoidHom.id (normOneSubgroup K GLₙ)) r.val t.val := by
  classical
  let e := GeneralLinearGroupPoints.adelicHomeomorph K n
  let p : normOneSubgroup K GLₙ → AdelicGL K n := fun g ↦ e (g : AdelicGroupPoints K GLₙ)
  let D := p '' C
  have hD : IsCompact D := hC.image (e.continuous.comp continuous_subtype_val)
  have hDEll : ∀ g ∈ D, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n g)) := by
    rintro _ ⟨g, hg, rfl⟩
    exact hEll g hg
  let j := rationalNormOne K GLₙ
  let i := GeneralLinearGroupPoints.rationalEquiv K n
  let lift (r : RationalGL K n) : rationalNormOneSubgroup K GLₙ :=
    ⟨j (i.symm r), ⟨i.symm r, rfl⟩⟩
  obtain ⟨R, hR⟩ := generalLinearEllipticClassFiniteness K n v D hD hDEll
  refine ⟨R.image lift, ?_⟩
  rintro ⟨r, ⟨q, rfl⟩⟩ ⟨x, hx⟩
  have hxD : p (x⁻¹ * j q * x) ∈ D := Set.mem_image_of_mem p hx
  change e ((x : AdelicGroupPoints K GLₙ)⁻¹ * AdelicGroupPoints.rational K GLₙ q *
    (x : AdelicGroupPoints K GLₙ)) ∈ D at hxD
  rw [map_mul, map_mul, map_inv, GeneralLinearGroupPoints.adelicHomeomorph_rational] at hxD
  obtain ⟨_, t, ht, y, hy⟩ := hR (i q) ⟨e x, hxD⟩
  refine ⟨lift t, Finset.mem_image_of_mem lift ht, (lift y).val, (lift y).property, ?_⟩
  change (j (i.symm y))⁻¹ * j q * j (i.symm y) = j (i.symm t)
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg j
  apply i.injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hy

/-- One pair of matching split auxiliary tests isolates the chosen ordinary
and twisted rational classes for all norm-one functions with fixed broad
compact bounds and satisfying the finite-place support restrictions. -/
def AdelicOrbitIsolationStatement : Prop :=
  GeneralLinearWeilAdelicTwistStatement.{u} →
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] (v : FinitePlace K) (w : FinitePlace L)
      (m n : ℕ) (σ : L ≃ₐ[K] L), IsCyclicAlgebra σ (m + 1) →
    ∀ (c : LocalBaseChangeAlgebra K L (.inr v) ≃ₐ[Fᵥ] (Fin (m + 1) → Fᵥ)),
      (∀ z, c (localGalois K L σ (.inr v) z) = splitCyclicShift Fᵥ (m + 1) (c z)) →
      let HG := normOneSubgroup K GLₙ
      let HW := normOneSubgroup K Wₙ
      let RG := rationalNormOneSubgroup K GLₙ
      let RW := rationalNormOneSubgroup K Wₙ
      let θ := normOneAut K (unitGaloisAut K L GLₙ σ)
      let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g ↦
        GeneralLinearGroupPoints.adelicHomeomorph L n
          (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
            (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
            (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
            (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
      let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g ↦
        ((List.range (m + 1)).map fun k ↦ adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) g).prod
      ∀ (CG : Set HG) (CW : Set HW), IsCompact CG → IsCompact CW →
        (∀ z ∈ CG, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
          (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n z)))) →
        (∀ z ∈ CW, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
          (AdelicGL.finite L n (Φ (N z))))) →
      ∀ (q₀ : RationalGroupPoints K GLₙ) (t₀ : RationalGroupPoints K Wₙ),
        IsRegularSemisimple (GeneralLinearGroupPoints.rationalEquiv K n q₀) →
        IsNormAssociated σ (m + 1) (rationalWeilGLEquiv K L n t₀)
          (GeneralLinearGroupPoints.rationalEquiv K n q₀) →
        let Q := rationalNormOne K GLₙ q₀
        let D := rationalNormOne K Wₙ t₀
        let G := GeneralLinear n Fᵥ
        let E := GeneralLinear n (Fin (m + 1) → Fᵥ)
        let τ := splitCyclicShift Fᵥ (m + 1)
        let κ := splitGLCoordinates Fᵥ n (m + 1)
        let pG := atPlace K GLₙ (.inr v)
        let pW := atPlace K Wₙ (.inr v)
        let eG := localGLEquiv K n (.inr v)
        let eW := (localPointsEquiv K L n (.inr v)).trans (localSplitGLEquiv K L v m n c)
        ∀ (ρF : Measure G) [ρF.IsHaarMeasure] (ρE : Measure E) [ρE.IsHaarMeasure],
          IsSplitProductHaar ρF ρE → ∀ (A : Set (Fin (m + 1) → G)) (V : Set G),
            IsOpen A → κ (eW (pW D)) ∈ A → IsOpen V → (List.ofFn (κ (eW (pW D)))).prod ∈ V →
            ∃ ψ : Fin (m + 1) → SchwartzBruhat G,
              let φ := splitTensor fun i ↦ (ψ i : G → ℂ)
              let f := convolutionProduct ρF ψ
              AreConcordant τ (m + 1) ρF ρE φ (f : G → ℂ) ∧
              φ (eW (pW D)) = 1 ∧ tsupport φ ⊆ κ ⁻¹' A ∧ tsupport (f : G → ℂ) ⊆ V ∧
              (∀ g, 0 ≤ f g) ∧ 0 < f (List.ofFn (κ (eW (pW D)))).prod ∧
              (∀ fOne : HG → ℂ, Function.support fOne ⊆ CG →
                (∀ z, fOne z ≠ 0 → f (eG (pG z)) ≠ 0) →
                ∀ r : RG, (∃ x : HG, fOne (x⁻¹ * r.val * x) ≠ 0) →
                  IsTwistedConjugate RG (MonoidHom.id HG) r.val Q) ∧
              (∀ φOne : HW → ℂ, Function.support φOne ⊆ CW →
                (∀ z, φOne z ≠ 0 → φ (eW (pW z)) ≠ 0) →
                ∀ r : RW, (∃ x : HW, φOne (x⁻¹ * r.val * θ x) ≠ 0) →
                  IsTwistedConjugate RW θ r.val D)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 4200000 in
theorem adelicOrbitIsolation : AdelicOrbitIsolationStatement.{u} := by
  classical
  intro hweil K L _ _ _ _ _ _ v w m n σ hσ c hc HG HW RG RW θ Φ N
    CG CW hCG hCW hEllG hEllW q₀ t₀ hreg hassoc Q D G E τ κ pG pW eG eW
    ρF _ ρE _ hρ A V hA hDA hV hDV
  obtain ⟨R, hR⟩ := exists_finite_ordinary_normOneClasses K n v CG hCG hEllG
  obtain ⟨T, hT⟩ := adelicRationalTwistedFiniteness hweil K L σ (m + 1) hσ n w CW hCW hEllW
  have hRationalG (r : RG) : ∃ q : RationalGroupPoints K GLₙ, rationalNormOne K GLₙ q = r.val :=
    r.property
  have hRationalW (r : RW) : ∃ t : RationalGroupPoints K Wₙ, rationalNormOne K Wₙ t = r.val :=
    r.property
  choose rG hrG using hRationalG
  choose rW hrW using hRationalW
  obtain ⟨ψ, hmatch, hvalue, hsuppW, hsuppG, hnonneg, hpos, hcutG, hcutW⟩ :=
    finitePlaceOrbitIsolation K L v m n σ hσ c hc (R.image rG) (T.image rW) q₀ t₀
      hreg hassoc ρF ρE hρ A V hA hDA hV hDV
  refine ⟨ψ, hmatch, hvalue, hsuppW, hsuppG, hnonneg, hpos, ?_, ?_⟩
  · intro fOne hsupp hloc
    apply isTwistedConjugate_of_finiteSupportCutoff RG (MonoidHom.id HG) CG R Q hR fOne hsupp
    rintro r hr ⟨x, hx⟩
    have hx' := hloc _ hx
    change convolutionProduct ρF ψ (eG (pG ((x : AdelicGroupPoints K GLₙ)⁻¹ *
      (r.val : AdelicGroupPoints K GLₙ) * (x : AdelicGroupPoints K GLₙ)))) ≠ 0 at hx'
    have hr' : (r.val : AdelicGroupPoints K GLₙ) = AdelicGroupPoints.rational K GLₙ (rG r) :=
      congrArg Subtype.val (hrG r).symm
    rw [map_mul pG, map_mul pG, map_inv pG, hr'] at hx'
    obtain ⟨a, ha⟩ := hcutG (rG r) (Finset.mem_image_of_mem rG hr) ⟨pG x, hx'⟩
    refine ⟨rationalNormOne K GLₙ a, ⟨a, rfl⟩, ?_⟩
    rw [MonoidHom.id_apply, ← hrG r, ← map_inv, ← map_mul, ← map_mul, ha]
  · intro φOne hsupp hloc
    apply isTwistedConjugate_of_finiteSupportCutoff RW θ.toMonoidHom CW T D hT φOne hsupp
    rintro r hr ⟨x, hx⟩
    have hx' := hloc _ hx
    change splitTensor (fun i ↦ (ψ i : G → ℂ)) (eW (pW
      ((x : AdelicGroupPoints K Wₙ)⁻¹ * (r.val : AdelicGroupPoints K Wₙ) *
        (θ x : AdelicGroupPoints K Wₙ)))) ≠ 0 at hx'
    have hr' : (r.val : AdelicGroupPoints K Wₙ) = AdelicGroupPoints.rational K Wₙ (rW r) :=
      congrArg Subtype.val (hrW r).symm
    have hθ (z : HW) : pW (θ z : AdelicGroupPoints K Wₙ) =
        (Wₙ).affinePointsTarget (unitGaloisAut K L GLₙ σ).asIso.hom (placeCompletion K (.inr v)) (pW z) := by
      change atPlace K Wₙ (.inr v)
        (AdelicGroupPoints.map K Wₙ Wₙ (unitGaloisAut K L GLₙ σ).asIso.hom z) = _
      exact atPlace_map K Wₙ _ (.inr v) z
    rw [map_mul pW, map_mul pW, map_inv pW, hr', hθ] at hx'
    obtain ⟨a, ha⟩ := hcutW (rW r) (Finset.mem_image_of_mem rW hr) ⟨pW x, hx'⟩
    refine ⟨rationalNormOne K Wₙ a, ⟨a, rfl⟩, ?_⟩
    have ht : θ (rationalNormOne K Wₙ a) =
        rationalNormOne K Wₙ ((Wₙ).affinePointsTarget
          (unitGaloisAut K L GLₙ σ).asIso.hom (CommAlgCat.of K K) a) :=
      mapNormOne_rationalNormOne K Wₙ Wₙ (unitGaloisAut K L GLₙ σ).asIso.hom a
    change (rationalNormOne K Wₙ a)⁻¹ * r.val * θ (rationalNormOne K Wₙ a) = D
    rw [← hrW r, ht, ← map_inv, ← map_mul, ← map_mul, ha]

end Langlands.TraceFormula
