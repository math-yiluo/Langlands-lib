import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Galois.AlgebraicHeckeLambdaAdicRealizationStatement
import Langlands.Galois.PureWeightParity
import Langlands.Global.IdeleClosedSubgroupDensity
import Langlands.Global.HeckeCharacterUnramifiedNorm
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily

/-!
# Hecke characters are determined by one member of a compatible realization

Two continuous characters of the idele classes of a number field with values in a Hausdorff
group are equal when they agree on all uniformizers at the finite places outside a finite set:
their equalizer is a closed subgroup containing the principal ideles and, away from the finite
set, every local multiplicative group, hence is everything by the density theorem
`Langlands.Global.IdeleDensity.eq_top_of_isClosed`. Consequently two Hecke characters with
compatible realizations through the same complex embedding of the coefficient field coincide as
soon as the realizations agree at one coefficient place: the common Frobenius values determine
the values at uniformizers away from a finite set of places.
-/

noncomputable section

universe u uL

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped Valued

section Density

variable {K : Type u} [Field K] [NumberField K]

/-- Two continuous homomorphisms from the idele classes to a Hausdorff group that agree on all
uniformizers at all finite places outside a finite set are equal. -/
theorem ideleClass_hom_ext_of_uniformizers_t2 {G : Type*} [Group G] [TopologicalSpace G]
    [T2Space G] (ρ₁ ρ₂ : IdeleClasses K →ₜ* G) (S : Finset (FinitePlace K))
    (h : ∀ v ∉ S, ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        ρ₁ (finiteClassInclusion K v π) = ρ₂ (finiteClassInclusion K v π)) :
    ρ₁ = ρ₂ := by
  let E : Subgroup (IdeleClasses K) := MonoidHom.eqLocus ρ₁.toMonoidHom ρ₂.toMonoidHom
  have hE : IsClosed (E : Set (IdeleClasses K)) := isClosed_eq ρ₁.continuous ρ₂.continuous
  let H : Subgroup (Ideles K) := E.comap (ideleClassMap K).toMonoidHom
  have hH : IsClosed (H : Set (Ideles K)) := hE.preimage (ideleClassMap K).continuous
  have hprin : ∀ a : Kˣ, diagonalUnits K a ∈ H := by
    intro a
    have h1 : ideleClassMap K (diagonalUnits K a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    change ρ₁ (ideleClassMap K (diagonalUnits K a)) = ρ₂ (ideleClassMap K (diagonalUnits K a))
    rw [h1, map_one, map_one]
  have hloc : ∀ v ∉ S, ∀ a : (FiniteCompletion K v)ˣ, finiteIdeleInclusion K v a ∈ H := by
    intro v hv a
    change finiteClassInclusion K v a ∈ E
    obtain ⟨π, hπ⟩ := Automorphic.Unramified.WeakInduction.exists_uniformizer v
    have ha0 : Valued.v (a : FiniteCompletion K v) ≠ 0 := by simp
    set m := WithZero.log (Valued.v (a : FiniteCompletion K v))
    have hπ' : Valued.v ((a * π ^ (m + 1) : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) =
        WithZero.exp (-1 : ℤ) := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ,
        ← WithZero.exp_log ha0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      congr 1
      simp only [smul_eq_mul]
      ring
    have hdecomp : a = (a * π ^ (m + 1)) * π ^ (-(m + 1)) := by group
    rw [hdecomp, map_mul, map_zpow]
    exact E.mul_mem (h v hv _ hπ') (E.zpow_mem (h v hv π hπ) _)
  have htop := IdeleDensity.eq_top_of_isClosed H S hH hprin hloc
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles K) x
  have hy : y ∈ H := htop ▸ Subgroup.mem_top y
  exact hy

end Density

section Realization

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- Two Hecke characters with compatible realizations through the same complex embedding are
equal if the realizations agree at one coefficient place. -/
theorem heckeCharacter_eq_of_lambdaAdic_eq (ι : L →+* ℂ) {χ₁ χ₂ : HeckeCharacter K}
    {ψ₁ ψ₂ : (lam : FinitePlace L) → LambdaAdicCharacter K L lam}
    (h₁ : IsCompatibleLambdaAdicRealization ι χ₁ ψ₁)
    (h₂ : IsCompatibleLambdaAdicRealization ι χ₂ ψ₂) (lam : FinitePlace L)
    (heq : ∀ g, ψ₁ lam g = ψ₂ lam g) : χ₁ = χ₂ := by
  classical
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  have hlam := (residueCharacteristic_prime lam).ne_zero
  let T := (finite_setOf_residueCharacteristic_eq K hlam).toFinset
  apply ideleClass_hom_ext_of_uniformizers_t2 χ₁ χ₂ (S₁ ∪ S₂ ∪ T)
  intro v hv π hπ
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hv₁, hv₂⟩, hvT⟩ := hv
  have hres : residueCharacteristic v ≠ residueCharacteristic lam := by
    intro h
    exact hvT ((Set.Finite.mem_toFinset _).mpr h)
  obtain ⟨hχ₁, a₁, ⟨ϖ₁, hϖ₁, hval₁⟩, hψ₁⟩ := hS₁ v hv₁
  obtain ⟨hχ₂, a₂, ⟨ϖ₂, hϖ₂, hval₂⟩, hψ₂⟩ := hS₂ v hv₂
  let c := geometricFrobeniusLift v
  have hc := geometricFrobeniusLift_spec v
  have e₁ := (hψ₁ lam hres).2 c hc
  have e₂ := (hψ₂ lam hres).2 c hc
  have hcoef : a₁ = a₂ := by
    apply (NumberField.FinitePlace.embedding lam).injective
    rw [← e₁, ← e₂]
    change ((ψ₁ lam (Field.absoluteGaloisGroup.map
        (NumberField.FinitePlace.embedding v) c) : (FiniteCompletion L lam)ˣ) :
        FiniteCompletion L lam) = ((ψ₂ lam (Field.absoluteGaloisGroup.map
        (NumberField.FinitePlace.embedding v) c) : (FiniteCompletion L lam)ˣ) :
        FiniteCompletion L lam)
    rw [heq]
  have hπ₁ : χ₁.finiteComponent v π = χ₁.finiteComponent v ϖ₁ :=
    HeckeCharacter.finiteComponent_eq_of_valued_eq χ₁ hχ₁ (hπ.trans hϖ₁.symm)
  have hπ₂ : χ₂.finiteComponent v π = χ₂.finiteComponent v ϖ₂ :=
    HeckeCharacter.finiteComponent_eq_of_valued_eq χ₂ hχ₂ (hπ.trans hϖ₂.symm)
  change χ₁.finiteComponent v π = χ₂.finiteComponent v π
  rw [hπ₁, hπ₂]
  apply Units.ext
  rw [hval₁, hval₂, hcoef]

end Realization

end Langlands.GaloisRepresentation
