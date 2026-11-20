import Langlands.Global.AdelicInducedStandardSlice
import Langlands.Global.AdelicArchimedeanPlaceComplement
import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Representation.Archimedean.AdmissibleProductTensor

/-! # Algebraic multiplicity tensors for archimedean coordinates of induced sections -/

noncomputable section

universe uF uV uW uI uR

namespace Langlands.Global.AdelicParabolicInduction

open NumberField Langlands.GeneralLinear AdelicBlockParabolic ArchimedeanGL
open Langlands.Archimedean Langlands.LocalFactor.Archimedean RealLeviSlices
open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {W : Type uW} [AddCommGroup W] [Module ℂ W] {I : Type uI}

section Coordinates

variable {R : Type uR} [RCLike R] {n : ℕ}

local notation "G" => Langlands.GeneralLinear n R
local notation "K" => Matrix.unitaryGroup (Fin n) R

private theorem slice_mem_kFiniteFunctions
    (κ : Representation ℂ K W) (C : Submodule ℂ (G → ℂ)) (q : W →ₗ[ℂ] (G → ℂ))
    (hK : ∀ k w, q (κ k w) = Whittaker.rightTranslation ℂ G (Unitary.toUnits k) (q w))
    (w : W) (hw : FiniteVectors.IsFiniteVector κ w) (hq : q w ∈ C) :
    q w ∈ kFiniteFunctions C (unitaryCompact R n) := by
  refine ⟨hq, ?_⟩
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact R n =>
    Whittaker.rightTranslation ℂ G k.val (q w)))
  let _ : FiniteDimensional ℂ (FiniteVectors.orbitSpan κ w) := hw
  apply Submodule.finiteDimensional_of_le (S₂ := (FiniteVectors.orbitSpan κ w).map q)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let k' : K := ⟨k.val.val, k.property⟩
  have hk : Unitary.toUnits k' = k.val := Units.ext rfl
  refine ⟨κ k' w, FiniteVectors.action_mem_orbitSpan κ k' w, ?_⟩
  change q (κ k' w) = Whittaker.rightTranslation ℂ G k.val (q w)
  rw [← hk]
  exact hK k' w

private theorem exists_coordinateTensor
    (C : Submodule ℂ (G → ℂ))
    (ρ : Representation ℂ K (kFiniteFunctions C (unitaryCompact R n)))
    (hρ : IsAdmissibleGKModule ρ)
    (hρK : ∀ k f, (ρ k f : G → ℂ) = Whittaker.rightTranslation ℂ G (Unitary.toUnits k) f)
    (D : Matrix (Fin n) (Fin n) R → Module.End ℂ (kFiniteFunctions C (unitaryCompact R n)))
    (hD : ∀ X f, (D X f : G → ℂ) = rightDerivative (matrixModel R n) X f)
    (κ : Representation ℂ K W) (δ : Matrix (Fin n) (Fin n) R → Module.End ℂ W)
    (hfin : ∀ w, FiniteVectors.IsFiniteVector κ w) (q : I → W →ₗ[ℂ] (G → ℂ))
    (hC : ∀ i w, q i w ∈ C)
    (hK : ∀ k w i, q i (κ k w) = Whittaker.rightTranslation ℂ G (Unitary.toUnits k) (q i w))
    (hLie : ∀ X w i, q i (δ X w) = rightDerivative (matrixModel R n) X (q i w))
    (hcont : ∀ i w, Continuous (q i w))
    (hsep : ∀ w, (∀ i g, q i w g = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] (kFiniteFunctions C (unitaryCompact R n) ⊗[ℂ] (I → ℂ)),
      Function.Injective e ∧
      (∀ k w, e (κ k w) = TensorProduct.map (ρ k) LinearMap.id (e w)) ∧
      ∀ X w, e (δ X w) = TensorProduct.map (D X) LinearMap.id (e w) := by
  let qK : W →ₗ[ℂ] (I → kFiniteFunctions C (unitaryCompact R n)) :=
    LinearMap.pi fun i => (q i).codRestrict _ fun w =>
      slice_mem_kFiniteFunctions κ C (q i) (fun k x => hK k x i) w (hfin w) (hC i w)
  have hqK (k : K) (w : W) (i : I) : qK (κ k w) i = ρ k (qK w i) := by
    apply Subtype.ext
    rw [hρK]
    exact hK k w i
  have hqLie (X : Matrix (Fin n) (Fin n) R) (w : W) (i : I) :
      qK (δ X w) i = D X (qK w i) := by
    apply Subtype.ext
    rw [hD]
    exact hLie X w i
  have hκ (w : W) (μ : W →ₗ[ℂ] ℂ) : Continuous fun k => μ (κ k w) := by
    let S := FiniteVectors.orbitSpan κ w
    let _ : FiniteDimensional ℂ S := hfin w
    let ev (p : I × G) : W →ₗ[ℂ] ℂ := (LinearMap.proj p.2).comp (q p.1)
    obtain ⟨m, p, c, hp⟩ := exists_sum_of_separating ev S
      (fun x _ hx => hsep x fun i g => hx (i, g)) μ
    have he (k : K) : μ (κ k w) =
        ∑ j, c j * q (p j).1 w ((p j).2 * Unitary.toUnits k) := by
      rw [hp (κ k w) (FiniteVectors.action_mem_orbitSpan κ k w)]
      exact Finset.sum_congr rfl fun j _ => by
        change c j * q (p j).1 (κ k w) (p j).2 = _
        rw [hK]
        rfl
    have hsum : Continuous
        (fun k : K => ∑ j, c j * q (p j).1 w ((p j).2 * Unitary.toUnits k)) :=
      continuous_finsetSum _ fun j _ => continuous_const.mul
        ((hcont (p j).1 w).comp (continuous_const.mul continuous_unitary_toUnits))
    exact hsum.congr fun k => (he k).symm
  have hspan := finiteDimensional_span_range_of_compactCoordinates κ ρ hρ hκ qK hqK
  refine ⟨toMultiplicityTensor qK (fun w => hspan w (hfin w)),
    toMultiplicityTensor_injective qK _ ?_, ?_, ?_⟩
  · intro w w' h
    apply sub_eq_zero.mp
    apply hsep
    intro i g
    have hz : qK (w - w') = 0 := by rw [map_sub, h, sub_self]
    exact congrArg (fun a : I → kFiniteFunctions C (unitaryCompact R n) => (a i : G → ℂ) g) hz
  · exact fun k w => toMultiplicityTensor_equivariant qK _ (κ k) (ρ k) (hqK k) w
  · exact fun X w => toMultiplicityTensor_equivariant qK _ (δ X) (D X) (hqLie X) w

end Coordinates

variable (F : Type uF) [Field F] [NumberField F]
variable {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (σ : Representation ℂ (FullLevi F B) V)

/-- Base points commuting with the image of an embedded local parabolic. -/
abbrev commutingPlaceBases {R : Type uR} [CommRing R] (ιP : B.parabolic R →* Full F B) :=
  {y : AdelicGL F n // ∀ p, Commute y (ιP p).val}

private theorem section_eq_zero_of_slices {R : Type} [CommRing R]
    (ι : Langlands.GeneralLinear n R →* AdelicGL F n)
    (ιP : B.parabolic R →* Full F B) (hι : ∀ p, (ιP p).val = ι p.val)
    (hcover : ∀ x : AdelicGL F n,
      ∃ (y : commutingPlaceBases F B ιP) (g : Langlands.GeneralLinear n R), y.val * ι g = x)
    (ℓ : I → V →L[ℂ] ℂ)
    (hsep : ∀ z, (∀ i p, ℓ i (inducingRepresentation F B σ (ιP p) z) = 0) → z = 0)
    (f : SmoothSections F B σ)
    (hf : ∀ (y : commutingPlaceBases F B ιP) i g,
      ℓ i (evaluate F B σ f.val (y.val * ι g)) = 0) :
    f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate F B σ f.val x = 0
  obtain ⟨y, g, rfl⟩ := hcover x
  apply hsep
  intro i p
  have hc := (localSectionRestriction F B σ ι ιP hι y.val y.property f).property p g
  change evaluate F B σ f.val (y.val * ι (p.val * g)) =
    inducingRepresentation F B σ (ιP p) (evaluate F B σ f.val (y.val * ι g)) at hc
  rw [← hc]
  exact hf y i (p.val * g)

section Real

variable {c : ℕ} (ds : Fin c → List RealBlock) (hsize : ∀ i, 0 < sz ds i)

local notation "B₀" => orderedBlockShape (sz ds) hsize
local notation "N" => (∑ i, sz ds i)

/-- A compact-finite source of actual sections embeds equivariantly into a real standard
module tensored with a scalar multiplicity space if the block standard coefficient probes
separate after the embedded parabolic action. -/
theorem exists_realPlaceStandardTensor
    (τ : Representation ℂ (FullLevi F (orderedBlockShape (sz ds) hsize)) V)
    (hτ : ∀ p, Continuous (inducingRepresentation F B₀ τ p))
    (v : {w : InfinitePlace F // InfinitePlace.IsReal w})
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin N) ℝ) W)
    (δ : Matrix (Fin N) (Fin N) ℝ → Module.End ℂ W)
    (hfin : ∀ w, FiniteVectors.IsFiniteVector κ w)
    (j : W →ₗ[ℂ] SmoothSections F B₀ τ) (hj : Function.Injective j)
    (hK : ∀ k w, j (κ k w) = compactRepresentation F B₀ τ
      (realPlaceCompactInclusion F N v k) (j w))
    (hLie : ∀ X w, j (δ X w) = realLieAction F B₀ τ hτ (realPlaceLieInclusion F N v X) (j w))
    (ℓ : I → V →L[ℂ] ℂ)
    (hℓ : ∀ a i z, blockCoefficientOrbit F B₀ τ
      (fun i => AdelicGL.realPlaceInclusion F (sz ds i) v) (ℓ a) i z ∈
        realStandardModule (sz ds i) (ds i))
    (hsep : ∀ z, (∀ i p, ℓ i (inducingRepresentation F B₀ τ
      (AdelicBlockParabolic.realPlaceInclusion F B₀ v p) z) = 0) → z = 0) :
    ∃ e : W →ₗ[ℂ] (kFiniteFunctions (realStandardModule N (flat ds)) (unitaryCompact ℝ N) ⊗[ℂ]
        ((commutingPlaceBases F B₀ (AdelicBlockParabolic.realPlaceInclusion F B₀ v) × I) → ℂ)),
      Function.Injective e ∧
      (∀ k w, e (κ k w) =
        TensorProduct.map (realStandardRep N (flat ds) k) LinearMap.id (e w)) ∧
      ∀ X w, e (δ X w) =
        TensorProduct.map (realStandardLie N (flat ds) (1 ⊗ₜ X)) LinearMap.id (e w) := by
  let ιP := AdelicBlockParabolic.realPlaceInclusion F B₀ v
  let q (p : commutingPlaceBases F B₀ ιP × I) :=
    (realPlaceSlice F B₀ τ v p.1.val (ℓ p.2)).comp j
  refine exists_coordinateTensor (realStandardModule N (flat ds)) (realStandardRep N (flat ds))
    (realStandardAdmissible N (flat ds)) (realStandardRep_apply_coe N (flat ds))
    (fun X => realStandardLie N (flat ds) (1 ⊗ₜ X))
    (realStandardLie_one_tmul_apply_coe N (flat ds)) κ δ hfin q ?_ ?_ ?_ ?_ ?_
  · intro p w
    exact realPlaceSlice_mem_standardModule F ds hsize τ v p.1.val p.1.property
      (ℓ p.2) (hℓ p.2) (j w)
  · intro k w p
    funext g
    change realPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j (κ k w)) g =
      realPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j w) (g * Unitary.toUnits k)
    rw [hK]
    exact (realPlaceSlice_compact F B₀ τ v p.1.val (ℓ p.2) (j w) k g).symm
  · intro X w p
    change realPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j (δ X w)) = _
    rw [hLie]
    exact (realPlaceSlice_rightDerivative F B₀ τ hτ v p.1.val (ℓ p.2) (j w) X).symm
  · exact fun p w => (realPlaceSlice_contMDiff F B₀ τ v p.1.val (ℓ p.2) (j w)).continuous
  · intro w hw
    apply hj
    rw [map_zero]
    refine section_eq_zero_of_slices F B₀ τ (AdelicGL.realPlaceInclusion F N v) ιP
      (realPlaceInclusion_val F B₀ v) ?_ ℓ hsep (j w) ?_
    · intro x
      obtain ⟨y, g, hy, hx⟩ := AdelicGL.exists_realPlace_complement F N v x
      exact ⟨⟨y, fun p => hy p.val⟩, g, hx⟩
    · exact fun y i g => hw (y, i) g

end Real

section Complex

variable {c : ℕ} (ds : Fin c → List ComplexCharacterData)
variable (hsize : ∀ i, 0 < (ds i).length)

local notation "blockSize" => (fun i => List.length (ds i))
local notation "B₀" => orderedBlockShape blockSize hsize
local notation "N" => (∑ i, blockSize i)
local notation "blocks" => List.flatten (List.ofFn ds)

/-- The complex standard tensor embeds the same kind of section source using real
directional derivatives on the complex matrix group. -/
theorem exists_complexPlaceStandardTensor
    (τ : Representation ℂ (FullLevi F (orderedBlockShape (fun i => (ds i).length) hsize)) V)
    (hτ : ∀ p, Continuous (inducingRepresentation F B₀ τ p))
    (v : {w : InfinitePlace F // InfinitePlace.IsComplex w})
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin N) ℂ) W)
    (δ : Matrix (Fin N) (Fin N) ℂ → Module.End ℂ W)
    (hfin : ∀ w, FiniteVectors.IsFiniteVector κ w)
    (j : W →ₗ[ℂ] SmoothSections F B₀ τ) (hj : Function.Injective j)
    (hK : ∀ k w, j (κ k w) = compactRepresentation F B₀ τ
      (complexPlaceCompactInclusion F N v k) (j w))
    (hLie : ∀ X w, j (δ X w) = realLieAction F B₀ τ hτ (complexPlaceLieInclusion F N v X) (j w))
    (ℓ : I → V →L[ℂ] ℂ)
    (hℓ : ∀ a i z, blockCoefficientOrbit F B₀ τ
      (fun i => AdelicGL.complexPlaceInclusion F (ds i).length v) (ℓ a) i z ∈
        complexStandardModule (ds i).length (ds i))
    (hsep : ∀ z, (∀ i p, ℓ i (inducingRepresentation F B₀ τ
      (AdelicBlockParabolic.complexPlaceInclusion F B₀ v p) z) = 0) → z = 0) :
    ∃ e : W →ₗ[ℂ] (kFiniteFunctions (complexStandardModule N blocks) (unitaryCompact ℂ N) ⊗[ℂ]
        ((commutingPlaceBases F B₀ (AdelicBlockParabolic.complexPlaceInclusion F B₀ v) × I) → ℂ)),
      Function.Injective e ∧
      (∀ k w, e (κ k w) =
        TensorProduct.map (complexStandardRep N blocks k) LinearMap.id (e w)) ∧
      ∀ X w, e (δ X w) =
        TensorProduct.map (complexStandardLie N blocks (1 ⊗ₜ X)) LinearMap.id (e w) := by
  let ιP := AdelicBlockParabolic.complexPlaceInclusion F B₀ v
  let q (p : commutingPlaceBases F B₀ ιP × I) :=
    (complexPlaceSlice F B₀ τ v p.1.val (ℓ p.2)).comp j
  refine exists_coordinateTensor (complexStandardModule N blocks) (complexStandardRep N blocks)
    (complexStandardAdmissible N blocks) (principalSeriesRep_apply_coe ℂ N _)
    (fun X => complexStandardLie N blocks (1 ⊗ₜ X))
    (principalSeriesLie_one_tmul_apply_coe ℂ N _) κ δ hfin q ?_ ?_ ?_ ?_ ?_
  · intro p w
    exact complexPlaceSlice_mem_standardModule F ds hsize τ v p.1.val p.1.property
      (ℓ p.2) (hℓ p.2) (j w)
  · intro k w p
    funext g
    change complexPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j (κ k w)) g =
      complexPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j w) (g * Unitary.toUnits k)
    rw [hK]
    exact (complexPlaceSlice_compact F B₀ τ v p.1.val (ℓ p.2) (j w) k g).symm
  · intro X w p
    change complexPlaceSlice F B₀ τ v p.1.val (ℓ p.2) (j (δ X w)) = _
    rw [hLie]
    exact (complexPlaceSlice_rightDerivative F B₀ τ hτ v p.1.val (ℓ p.2) (j w) X).symm
  · exact fun p w => (complexPlaceSlice_contMDiff F B₀ τ v p.1.val (ℓ p.2) (j w)).continuous
  · intro w hw
    apply hj
    rw [map_zero]
    refine section_eq_zero_of_slices F B₀ τ (AdelicGL.complexPlaceInclusion F N v) ιP
      (complexPlaceInclusion_val F B₀ v) ?_ ℓ hsep (j w) ?_
    · intro x
      obtain ⟨y, g, hy, hx⟩ := AdelicGL.exists_complexPlace_complement F N v x
      exact ⟨⟨y, fun p => hy p.val⟩, g, hx⟩
    · exact fun y i g => hw (y, i) g

end Complex

end Langlands.Global.AdelicParabolicInduction
