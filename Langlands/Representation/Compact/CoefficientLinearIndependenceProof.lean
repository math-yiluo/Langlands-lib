import Langlands.Representation.Compact.UnitarySquareIntegrableStatements
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.DFinsupp

/-! # Renard IV.3.3: independence of matrix coefficients -/

noncomputable section

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- Right translation on all functions, with no topology on the carrier. -/
abbrev coefficientRightRegular (G : Type u) [Group G] : Representation ℂ G (G → ℂ) :=
  Whittaker.rightTranslation ℂ G

/-- Fixing a functional makes coefficients an intertwiner into right translation. -/
abbrev coefficientRightIntertwiner {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) :
    ρ.IntertwiningMap (coefficientRightRegular G) :=
  HarishChandraSchwartz.coefficientIntertwiningMap ρ ℓ

/-- A nonzero functional on an irreducible representation gives an injective coefficient map. -/
theorem coefficientRightIntertwiner_injective {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hi : ρ.IsIrreducible)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) :
    Function.Injective (coefficientRightIntertwiner ρ ℓ) := by
  let := hi
  apply (Representation.IsIrreducible.injective_or_eq_zero
    (coefficientRightIntertwiner ρ ℓ)).resolve_right
  intro hz
  apply hℓ
  ext v
  have h := congrArg (fun F : ρ.IntertwiningMap (coefficientRightRegular G) => F v 1) hz
  simpa [coefficientRightIntertwiner,
    HarishChandraSchwartz.coefficientIntertwiningMap, matrixCoefficient] using h

/-- Distinct simple representations have independent nonzero coefficients, algebraically. -/
theorem coefficients_linearIndependent_of_irreducible
    {G : Type u} [Group G] [TopologicalSpace G] {ι : Type*}
    (π : ι → SmoothRep.{0, u, v} ℂ G) (hi : ∀ i, (π i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → IsEmpty (π i ≅ π j))
    (x : ∀ i, π i) (ℓ : ∀ i, Module.Dual ℂ (π i))
    (hx : ∀ i, x i ≠ 0) (hℓ : ∀ i, ℓ i ≠ 0) :
    LinearIndependent ℂ (fun i => matrixCoefficient (π i).representation (ℓ i) (x i)) := by
  classical
  let R := MonoidAlgebra ℂ G
  let σ := coefficientRightRegular G
  let F (i : ι) : (π i).representation.asModule →ₗ[R] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (coefficientRightIntertwiner (π i).representation (ℓ i))
  have hF (i : ι) : Function.Injective (F i) :=
    coefficientRightIntertwiner_injective (π i).representation (hi i) (ℓ i) (hℓ i)
  let N (i : ι) : Submodule R σ.asModule := (F i).range
  let e (i : ι) : (π i).representation.asModule ≃ₗ[R] N i := LinearEquiv.ofInjective (F i) (hF i)
  have hsimple (i : ι) : IsSimpleModule R (N i) := by
    have := (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hi i)
    exact (e i).isSimpleModule_iff.mp this
  let P (i : ι) : Submodule R σ.asModule := isotypicComponent R σ.asModule (N i)
  have hP (i : ι) : P i ∈ isotypicComponents R σ.asModule := ⟨N i, hsimple i, rfl⟩
  have hPinj : Function.Injective P := by
    intro i j hij
    by_contra hneij
    have := hsimple i
    have := hsimple j
    have hle : N i ≤ P j := hij ▸ (N i).le_isotypicComponent
    obtain ⟨eij⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent R σ.asModule (N j)) (N i) hle
    let a := ((e i).trans eij).trans (e j).symm
    let f := (Representation.IntertwiningMap.equivLinearMapAsModule
      (π i).representation (π j).representation).symm a.toLinearMap
    exact (hne i j hneij).false (SmoothRep.mkIso (f.ofBijective a.bijective))
  have hind : iSupIndep P := by
    let t : ι → isotypicComponents R σ.asModule := fun i => ⟨P i, hP i⟩
    have ht : Function.Injective t := fun i j h => hPinj (congrArg Subtype.val h)
    exact ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents R σ.asModule)).comp ht
  rw [linearIndependent_iff']
  intro s a ha i his
  let y (j : ι) : σ.asModule := σ.asModuleEquiv.symm
    (a j • matrixCoefficient (π j).representation (ℓ j) (x j))
  have hy (j : ι) : y j ∈ P j := by
    apply (N j).le_isotypicComponent
    refine ⟨(π j).representation.asModuleEquiv.symm (a j • x j), ?_⟩
    change matrixCoefficient (π j).representation (ℓ j) (a j • x j) =
      a j • matrixCoefficient (π j).representation (ℓ j) (x j)
    exact (matrixCoefficient (π j).representation (ℓ j)).map_smul _ _
  have hsum : ∑ j ∈ s, y j = 0 := by
    apply σ.asModuleEquiv.injective
    simpa [y] using ha
  have hyi := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero P).mp hind s y
    (fun j _ => hy j) hsum i his
  have hz : a i • x i = 0 := by
    apply hF i
    change matrixCoefficient (π i).representation (ℓ i) (a i • x i) =
      matrixCoefficient (π i).representation (ℓ i) 0
    rw [map_smul, map_zero]
    exact hyi
  exact (smul_eq_zero.mp hz).resolve_right (hx i)

/-- Renard IV.3.3 Corollary, with the exact published hypotheses. -/
theorem coefficientLinearIndependence : CoefficientLinearIndependenceStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ r π hi _ hne _ x ℓ hx hℓ
  exact coefficients_linearIndependent_of_irreducible π hi hne x (fun i => (ℓ i).val) hx
    (fun i h => hℓ i (Subtype.ext h))

end Langlands.Renard.CompactRepresentation
