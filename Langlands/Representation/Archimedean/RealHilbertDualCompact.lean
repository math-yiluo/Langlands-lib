import Langlands.Representation.Archimedean.HilbertContinuousDual
import Langlands.Representation.Archimedean.CompactFiniteSmoothness
import Langlands.Representation.Archimedean.RealCompactTraceSeparation
import Langlands.Representation.Archimedean.TransposePairingRestriction

/-! # Compact-finite restriction of the real continuous Hilbert dual -/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator InnerProductSpace ComplexConjugate MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.KFiniteDual (kDual kDualRep)
open InductionStages (ofUnitary toUnitary ofUnitary_toUnitary continuous_toUnits')
open DerivativeSmoothVectors (derivativeCLM toSmooth)

variable (n : ℕ)

local notation "GLR" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "I" => matrixModel ℝ n

section CompactAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))

/-- The norm action of the actual orthogonal matrices, regarded algebraically. -/
def realNormCompactRepresentation : Representation ℂ K E :=
  (normCompactRepresentation Kc R).comp (ofUnitary n)

@[simp]
theorem realNormCompactRepresentation_apply (k : K) (v : E) :
    realNormCompactRepresentation n R k v = R (Unitary.toUnits k) v :=
  rfl

/-- The two realizations of the orthogonal group give the same finite vectors. -/
theorem realNormCompactFinite_iff (v : E) :
    FiniteVectors.IsFiniteVector (realNormCompactRepresentation n R) v ↔
      FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) v := by
  have hs : Function.Surjective (ofUnitary n) := fun k => ⟨toUnitary n k, ofUnitary_toUnitary k⟩
  let f := fun k : Kc => normCompactRepresentation Kc R k v
  change Module.Finite ℂ (Submodule.span ℂ (Set.range (f ∘ ofUnitary n))) ↔
    Module.Finite ℂ (Submodule.span ℂ (Set.range f))
  rw [hs.range_comp]

end CompactAction

section SmoothCompactAction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))

/-- The empty word coordinate embeds the genuine smooth compact-finite carrier
in the norm compact-finite carrier. -/
def realSmoothKFiniteToNorm :
    smoothHilbertKFinite ℝ n R →ₗ[ℂ]
      (FiniteVectors.subrepresentation (realNormCompactRepresentation n R)).toSubmodule := by
  let L := LinearMap.intertwiningMap_of_isIntertwiningMap
    (smoothHilbertCompactRepresentation ℝ n R) (realNormCompactRepresentation n R)
    (derivativeCLM I R []).toLinearMap (fun _ _ => rfl)
  exact (L.toLinearMap.comp (smoothHilbertKFinite ℝ n R).subtype).codRestrict _
    (fun y => y.property.map L)

theorem realSmoothKFiniteToNorm_injective :
    Function.Injective (realSmoothKFiniteToNorm n R) := by
  intro x y h
  apply Subtype.ext
  apply (toSmooth I R).injective
  apply Subtype.ext
  have he := congrArg (fun z : (FiniteVectors.subrepresentation
    (realNormCompactRepresentation n R)).toSubmodule => (z : H)) h
  exact he

variable [CompleteSpace H]
  [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure]
  [MeasurableSpace (unitaryCompact ℝ n)] [BorelSpace (unitaryCompact ℝ n)]
  (ν : Measure (unitaryCompact ℝ n)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]

include μ ν in
theorem realSmoothKFiniteToNorm_surjective (hR : IsContinuousRepresentation R)
    (hadm : IsAdmissible R Kc) :
    Function.Surjective (realSmoothKFiniteToNorm n R) := by
  intro x
  have hx := (realNormCompactFinite_iff n R x.val).mp x.property
  have hs := isSmoothVector_of_normCompactFinite μ Kc ν R hR hadm x.val hx
  obtain ⟨y, hy⟩ := exists_smoothHilbertKFinite_of_norm n R hs hx
  exact ⟨y, Subtype.ext hy⟩

end SmoothCompactAction

section Restriction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V) (g : V →ₗ[ℂ] H)

local notation "D" => StrongDual ℂ H
local notation "S" => inverseTransposeContinuousDual ℝ n R
local notation "Σ" => realNormCompactRepresentation n S

/-- Restriction of a continuous functional to an algebraic model. -/
def restrictHilbertFunctional : D →ₗ[ℂ] Module.Dual ℂ V where
  toFun L := L.toLinearMap.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompleteSpace H] in
theorem restrictHilbertFunctional_injective (hg : DenseRange g) :
    Function.Injective (restrictHilbertFunctional g) := by
  intro L M h
  apply ContinuousLinearMap.ext
  intro x
  apply congrFun (hg.equalizer L.continuous M.continuous ?_) x
  exact funext fun v => LinearMap.congr_fun h v

omit [CompleteSpace H] in
theorem inverseTransposeContinuousDual_realCompact_apply (k : K) (L : D) (x : H) :
    S (Unitary.toUnits k) L x = L (R (Unitary.toUnits k⁻¹) x) := by
  change continuousDualRepresentation R
    (Langlands.GeneralLinear.inverseTranspose n ℝ (Unitary.toUnits k)) L x = _
  rw [inverseTranspose_unitaryToUnits, compactIota_real, continuousDualRepresentation_apply,
    map_inv (Unitary.toUnits : K →* GLR)]

variable (hgK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V),
  g (ρ k v) = R (Unitary.toUnits k) (g v))

/-- Restriction intertwines the ordinary algebraic dual action of the
orthogonal group with the norm action of the twisted continuous dual. -/
def restrictHilbertFunctionalIntertwiner : (Σ).IntertwiningMap ρ.dual :=
  LinearMap.intertwiningMap_of_isIntertwiningMap Σ ρ.dual (restrictHilbertFunctional g)
    (fun k L => by
      apply LinearMap.ext
      intro v
      change S (Unitary.toUnits k) L (g v) = L (g (ρ k⁻¹ v))
      rw [inverseTransposeContinuousDual_realCompact_apply, hgK])

/-- Restriction of the norm compact-finite continuous dual into the algebraic finite dual. -/
def normDualRestriction :
    (FiniteVectors.subrepresentation Σ).toSubmodule →ₗ[ℂ] kDual ρ :=
  ((restrictHilbertFunctional g).comp (FiniteVectors.subrepresentation Σ).toSubmodule.subtype).codRestrict
    (kDual ρ) (fun L => L.property.map (restrictHilbertFunctionalIntertwiner n R ρ g hgK))

omit [CompleteSpace H] in
theorem normDualRestriction_injective (hg : DenseRange g) :
    Function.Injective (normDualRestriction n R ρ g hgK) := by
  intro L M h
  apply Subtype.ext
  exact restrictHilbertFunctional_injective g hg (congrArg Subtype.val h)

private def restrictDualIntertwiner {d : ℕ} (c : Kc →* Matrix (Fin d) (Fin d) ℂ)
    (T : intertwiners S Kc d c) : gkIntertwiners (kDualRep ρ) d (c.comp (ofUnitary n)) := by
  let c' := c.comp (ofUnitary n)
  let T' : (Langlands.KFiniteDual.matrixRep c').IntertwiningMap Σ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ T.val
      (fun k u => T.property (ofUnitary n k) u)
  have hfin (u : Fin d → ℂ) :
      FiniteVectors.IsFiniteVector (Langlands.KFiniteDual.matrixRep c') u :=
    Submodule.finiteDimensional_of_le le_top
  let L := restrictHilbertFunctionalIntertwiner n R ρ g hgK
  let T'' : (Fin d → ℂ) →ₗ[ℂ] kDual ρ :=
    ((restrictHilbertFunctional g).comp T.val).codRestrict (kDual ρ)
      (fun u => ((hfin u).map T').map L)
  refine ⟨T'', fun k u => ?_⟩
  apply Subtype.ext
  change restrictHilbertFunctional g (T.val (c (ofUnitary n k) *ᵥ u)) =
    ρ.dual k (restrictHilbertFunctional g (T.val u))
  rw [T.property]
  exact LinearMap.congr_fun (L.isIntertwining' k) (T.val u)

omit [CompleteSpace H] in
include hgK in
/-- Compact admissibility passes to the twisted continuous dual of a dense
algebraic model, by restricting finite type intertwiners to the algebraic finite dual. -/
theorem isAdmissible_inverseTransposeContinuousDual (hg : DenseRange g)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (L : V →ₗ[ℂ] ℂ), Continuous fun k => L (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) :
    IsAdmissible S Kc := by
  intro d c hc
  have hU : Continuous (ofUnitary n) := continuous_toUnits'.subtype_mk _
  let c' : K →* Matrix (Fin d) (Fin d) ℂ := c.comp (ofUnitary n)
  have hc' : Continuous c' := hc.comp hU
  let M : Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] kDual ρ) := gkIntertwiners (kDualRep ρ) d c'
  let : AddCommGroup M :=
    Submodule.addCommGroup (R := ℂ) (M := (Fin d → ℂ) →ₗ[ℂ] kDual ρ) M
  let : Module ℂ M := Submodule.module (R := ℂ) (M := (Fin d → ℂ) →ₗ[ℂ] kDual ρ) M
  have hA : IsAdmissibleGKModule (kDualRep ρ) :=
    Langlands.KFiniteDual.admissible_kDual hfin hcont hadm
  let : FiniteDimensional ℂ M := hA d c' hc'
  let L : intertwiners S Kc d c →ₗ[ℂ] M :=
    { toFun := restrictDualIntertwiner n R ρ g hgK c
      map_add' _ _ := by
        apply Subtype.ext
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rfl
      map_smul' _ _ := by
        apply Subtype.ext
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rfl }
  apply FiniteDimensional.of_injective (V₂ := M) L
  intro T U h
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  apply restrictHilbertFunctional_injective g hg
  exact congrArg (fun z : M => ((z.val u : kDual ρ) : Module.Dual ℂ V)) h

theorem inverseTransposeContinuousDual_toDual_realCompact (hU : HasUnitaryRealCompactAction n R)
    (k : K) (x : H) :
    S (Unitary.toUnits k) (InnerProductSpace.toDual ℂ H x) =
      InnerProductSpace.toDual ℂ H (R (Unitary.toUnits k) x) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [inverseTransposeContinuousDual_realCompact_apply]
  change ⟪x, R (Unitary.toUnits k⁻¹) y⟫_ℂ =
    ⟪R (Unitary.toUnits k) x, y⟫_ℂ
  calc
    _ = ⟪R (Unitary.toUnits k) x,
      R (Unitary.toUnits k) (R (Unitary.toUnits k⁻¹) y)⟫_ℂ := (hU (ofUnitary n k) _ _).symm
    _ = _ := by
      rw [← mul_apply_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
        one_apply_eq_self]

/-- For a unitary compact restriction, Riesz sends original compact-finite vectors
to compact-finite vectors of the twisted continuous dual. -/
theorem isFiniteVector_toDual_realCompact (hU : HasUnitaryRealCompactAction n R)
    (x : H) (hx : FiniteVectors.IsFiniteVector (realNormCompactRepresentation n R) x) :
    FiniteVectors.IsFiniteVector Σ (InnerProductSpace.toDual ℂ H x) := by
  let e := InnerProductSpace.toDual ℂ H
  let M := FiniteVectors.orbitSpan (realNormCompactRepresentation n R) x
  let N := M.map e.toLinearMap
  let : FiniteDimensional ℂ M := hx
  let f : M →ₗ⋆[ℂ] N := (e.toLinearMap.comp M.subtype).codRestrict N
    (fun y => ⟨y, y.property, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  let : FiniteDimensional ℂ N := Module.Finite.of_surjective f hf
  apply Submodule.finiteDimensional_of_le (S₂ := N)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change S (Unitary.toUnits k) (e x) ∈ N
  rw [inverseTransposeContinuousDual_toDual_realCompact n R hU]
  exact ⟨R (Unitary.toUnits k) x, FiniteVectors.action_mem_orbitSpan _ k x, rfl⟩

/-- Every algebraic finite dual functional extends to a norm-compact-finite continuous
functional on the Hilbert model. -/
theorem normDualRestriction_surjective (hinj : Function.Injective g)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (L : V →ₗ[ℂ] ℂ), Continuous fun k => L (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) (hU : HasUnitaryRealCompactAction n R) :
    Function.Surjective (normDualRestriction n R ρ g hgK) := by
  let : IsSemisimpleModule ℂ[K] ρ.asModule := Langlands.KFiniteDual.isSemisimpleModule hfin hcont
  let L := restrictHilbertFunctionalIntertwiner n R ρ g hgK
  let M := FiniteVectors.subrepresentation Σ
  let N : Subrepresentation ρ.dual :=
    { toSubmodule := M.toSubmodule.map (restrictHilbertFunctional g)
      apply_mem_toSubmodule := by
        intro k z
        rintro ⟨x, hx, rfl⟩
        exact ⟨(Σ) k x, M.apply_mem_toSubmodule k hx, LinearMap.congr_fun (L.isIntertwining' k) x⟩ }
  have hN : ∀ w ∈ N, FiniteVectors.IsFiniteVector ρ.dual w := by
    rintro _ ⟨x, hx, rfl⟩
    exact (show FiniteVectors.IsFiniteVector Σ x from hx).map L
  have hsep (v : V) (hv : ∀ L ∈ N, L v = 0) : v = 0 := by
    by_contra h
    let γ : ρ.IntertwiningMap (realNormCompactRepresentation n R) :=
      LinearMap.intertwiningMap_of_isIntertwiningMap _ _ g hgK
    have hx : FiniteVectors.IsFiniteVector (realNormCompactRepresentation n R) (g v) :=
      (hfin v).map γ
    let x := InnerProductSpace.toDual ℂ H (g v)
    have hx' : x ∈ M.toSubmodule := isFiniteVector_toDual_realCompact n R hU (g v) hx
    have hz := hv (restrictHilbertFunctional g x) ⟨x, hx', rfl⟩
    change ⟪g v, g v⟫_ℂ = 0 at hz
    exact h (hinj (by simpa only [map_zero] using inner_self_eq_zero.mp hz))
  intro w
  have hw := Langlands.KFiniteDual.mem_of_separating
    (Langlands.KFiniteDual.finiteDimensional_block hfin hcont hadm) N hN hsep w.property
  obtain ⟨x, hx, hex⟩ := hw
  exact ⟨⟨x, hx⟩, Subtype.ext hex⟩

/-- Restriction of actual smooth compact-finite continuous functionals to the
algebraic compact-finite dual. -/
def smoothHilbertDualRestriction : smoothHilbertKFinite ℝ n S →ₗ[ℂ] kDual ρ :=
  (normDualRestriction n R ρ g hgK).comp (realSmoothKFiniteToNorm n S)

@[simp]
theorem smoothHilbertDualRestriction_apply_apply (y : smoothHilbertKFinite ℝ n S) (v : V) :
    ((smoothHilbertDualRestriction n R ρ g hgK y : kDual ρ) : Module.Dual ℂ V) v =
      derivativeCLM I S [] y.val (g v) :=
  rfl

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure]
  [MeasurableSpace (unitaryCompact ℝ n)] [BorelSpace (unitaryCompact ℝ n)]
  (ν : Measure (unitaryCompact ℝ n)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]

/-- For a dense injective model with a unitary compact action, the genuine smooth
compact-finite vectors of the twisted continuous dual identify with the algebraic finite dual. -/
def smoothHilbertDualEquiv (hR : IsContinuousRepresentation R) (hd : DenseRange g)
    (hinj : Function.Injective g)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (L : V →ₗ[ℂ] ℂ), Continuous fun k => L (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) (hU : HasUnitaryRealCompactAction n R) :
    smoothHilbertKFinite ℝ n S ≃ₗ[ℂ] kDual ρ := by
  have hS := isContinuousRepresentation_inverseTransposeContinuousDual ℝ n R hR
  have hAS := isAdmissible_inverseTransposeContinuousDual n R ρ g hgK hd hfin hcont hadm
  refine LinearEquiv.ofBijective (smoothHilbertDualRestriction n R ρ g hgK) ⟨?_, ?_⟩
  · exact (normDualRestriction_injective n R ρ g hgK hd).comp (realSmoothKFiniteToNorm_injective n S)
  · exact (normDualRestriction_surjective n R ρ g hgK hinj hfin hcont hadm hU).comp
      (realSmoothKFiniteToNorm_surjective n S μ ν hS hAS)

end Restriction

end Langlands.Archimedean
