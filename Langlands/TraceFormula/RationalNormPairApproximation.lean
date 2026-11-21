import Langlands.TraceFormula.LocalTensorRationalDensity
import Langlands.BaseChange.RegularNormRepresentative
import Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularOpen
import Langlands.BaseChange.CyclicNormLemma
import Langlands.Global.CompletionPadic

/-! # Simultaneous approximation by a rational associated norm pair -/

noncomputable section

namespace Langlands.TraceFormula

open BaseChange JacquetLanglands Global _root_.Topology
open scoped PlaceCompletion

universe u

variable (K L : Type u) [Field K] [Field L] [NumberField K]
  [Algebra K L] [FiniteDimensional K L]

set_option hygiene false in
local notation "Fᵥ" => FiniteCompletion K v

set_option hygiene false in
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (.inr v)

local instance (v : FinitePlace K) : Algebra Fᵥ Eᵥ :=
  LocalBaseChangeAlgebra.algebra K L (.inr v)

local instance (v : FinitePlace K) : IsModuleTopology Fᵥ Eᵥ :=
  LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)

private theorem exists_regularNormNeighborhood
    (v : FinitePlace K) (σ : L ≃ₐ[K] L) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    (δ₀ : GeneralLinear n Eᵥ) (γ₀ : GeneralLinear n Fᵥ)
    (hAssoc : IsNormAssociated (localGalois K L σ (.inr v)) l δ₀ γ₀)
    (hReg : IsRegularSemisimple γ₀) (U : Set (GeneralLinear n Eᵥ))
    (V : Set (GeneralLinear n Fᵥ)) (hU : U ∈ nhds δ₀) (hV : V ∈ nhds γ₀) :
    ∃ B ∈ nhds δ₀, ∀ δ ∈ B, δ ∈ U ∧ ∃ γ ∈ interior V,
      IsNormAssociated (localGalois K L σ (.inr v)) l δ γ ∧ IsRegularSemisimple γ := by
  let : ValuativeRel Fᵥ := (CompletionPadic.topologicalData v).valuativeRel
  let : IsNonarchimedeanLocalField Fᵥ := (CompletionPadic.topologicalData v).localField
  let σv := localGalois K L σ (.inr v)
  have hσv : IsCyclicAlgebra σv l := isCyclicAlgebra_localGalois K L σ l (.inr v) hσ
  let D := {δ : GeneralLinear n Eᵥ | IsSigmaRegular σv l δ}
  let d₀ : D := ⟨δ₀, γ₀, hAssoc, hReg⟩
  have hD : IsOpen D := SigmaLiftCharacterIdentity.isOpen_sigmaRegular_of_norm_exists (F := Fᵥ) hσv
    (cyclicNormLemma Fᵥ Eᵥ σv l n hσv).1
  obtain ⟨s, hs, hs₀, hAll⟩ := regularNormRepresentative Fᵥ Eᵥ σv l n hσv d₀ γ₀ hAssoc hReg
  let A : Set D := Subtype.val ⁻¹' U ∩ s ⁻¹' interior V
  have hVs : interior V ∈ nhds (s d₀) :=
    hs₀.symm ▸ isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV)
  have hA : A ∈ nhds d₀ := Filter.inter_mem
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hU)
    (hs.continuousAt.preimage_mem_nhds hVs)
  refine ⟨Subtype.val '' A, hD.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hA, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨hd.1, s d, hd.2, hAll d⟩

/-- A finite family of local associated regular pairs can be approximated
simultaneously by one associated pair of rational matrices. -/
def RationalNormPairApproximationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ S : Finset (FinitePlace K),
    ∀ (δ₀ : ∀ v : S, GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v.val)))
      (γ₀ : ∀ v : S, GeneralLinear n (FiniteCompletion K v.val)),
      (∀ v, IsNormAssociated (localGalois K L σ (.inr v.val)) l (δ₀ v) (γ₀ v)) →
      (∀ v, IsRegularSemisimple (γ₀ v)) →
      ∀ (U : ∀ v : S, Set (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v.val))))
        (V : ∀ v : S, Set (GeneralLinear n (FiniteCompletion K v.val))),
        (∀ v, U v ∈ nhds (δ₀ v)) → (∀ v, V v ∈ nhds (γ₀ v)) →
        ∃ (δ : RationalGL L n) (γ : RationalGL K n), IsNormAssociated σ l δ γ ∧
          ∀ v : S,
            Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr v.val)).toRingHom δ ∈ U v ∧
            Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v.val)) γ ∈ V v

set_option maxHeartbeats 1900000 in
theorem rationalNormPairApproximation : RationalNormPairApproximationStatement.{u} := by
  classical
  intro K L _ _ _ _ _ _ σ l n hσ S δ₀ γ₀ hAssoc hReg U V hU hV
  choose W hW hChoice using fun v : S => exists_regularNormNeighborhood K L v.val σ l n hσ
    (δ₀ v) (γ₀ v) (hAssoc v) (hReg v) (U v) (V v) (hU v) (hV v)
  have hWp : Set.pi Set.univ W ∈ nhds δ₀ := set_pi_mem_nhds Set.finite_univ (fun v _ => hW v)
  obtain ⟨δ, hδ⟩ := (localTensorRationalDensity K L n S).mem_nhds hWp
  let δv (v : S) := Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr v.val)).toRingHom δ
  have hδv (v : S) : δv v ∈ W v := hδ v (Set.mem_univ v)
  have hδU (v : S) := (hChoice v (δv v) (hδv v)).1
  choose g hgV hLocal using fun v : S => (hChoice v (δv v) (hδv v)).2
  obtain ⟨γ, hγ⟩ := (cyclicNormLemma K L σ l n hσ).1 δ
  let γv (v : S) := Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v.val)) γ
  have hγv (v : S) :
      IsNormAssociated (localGalois K L σ (.inr v.val)) l (δv v) (γv v) :=
    localize_normAssociated K L σ l n (.inr v.val) δ γ hγ
  choose y hy using fun v : S =>
    (cyclicNormLemma (FiniteCompletion K v.val) (LocalBaseChangeAlgebra K L (.inr v.val))
      (localGalois K L σ (.inr v.val)) l n
      (isCyclicAlgebra_localGalois K L σ l (.inr v.val) hσ)).2.1
      (δv v) (γv v) (g v) (hγv v) (hLocal v).1
  let c (x : ∀ v : S, GeneralLinear n (FiniteCompletion K v.val)) (v : S) :=
    (x v)⁻¹ * γv v * x v
  have hc : Continuous c := continuous_pi fun v =>
    (((continuous_apply v).inv).mul continuous_const).mul (continuous_apply v)
  have hg : Set.pi Set.univ V ∈ nhds g :=
    set_pi_mem_nhds Set.finite_univ (fun v _ => mem_interior_iff_mem_nhds.mp (hgV v))
  have hcy : c y = g := funext hy
  have hcp : c ⁻¹' Set.pi Set.univ V ∈ nhds y :=
    hc.continuousAt.preimage_mem_nhds (hcy.symm ▸ hg)
  obtain ⟨Y, hY⟩ := (rationalGLWeakApproximation K n S).mem_nhds hcp
  refine ⟨δ, Y⁻¹ * γ * Y, ?_, fun v => ⟨hδU v, ?_⟩⟩
  · simpa using hγ.twistedConj hσ.pow_eq_one 1 Y
  · have hv : c (fun w => Matrix.GeneralLinearGroup.map
        (algebraMap K (FiniteCompletion K w.val)) Y) v ∈ V v := hY v (Set.mem_univ v)
    simpa only [map_mul, map_inv, c, γv] using hv

end Langlands.TraceFormula
