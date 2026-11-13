import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent

/-! # Coefficient stability of the full stabilizer at a fixed point

The character kernel is stable for any invariant valuation. Semilinear permutations
then transport its intersection with the point stabilizer. The model-descent
corollary retains both the supplied model and the smooth-descent statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section InvariantValuation

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀] (valuation : Valuation K Γ₀)

private theorem rationalConjugate_mem_characterValuationKernel
    (σ : K ≃ₐ[k] K) (hvaluation : ∀ x : K, valuation (σ x) = valuation x)
    (g : rationalPoints (baseChanged k K G))
    (hg : g ∈ characterValuationKernel valuation (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈
      characterValuationKernel valuation (baseChanged k K G) := by
  apply mem_characterValuationKernel.mpr
  intro χ
  obtain ⟨χ', hχ'⟩ : ∃ χ' : rationalCharacters (baseChanged k K G),
      rationalCharacters.galoisRepresentation k K G σ χ' = χ :=
    ⟨rationalCharacters.galoisRepresentation k K G σ⁻¹ χ,
      rationalCharacters.galoisRepresentation_self_inv k K G σ χ⟩
  have heval := rationalCharacterEval_rationalConjugate_of_eq k K G σ χ χ' hχ' g
  exact (congrArg (fun z : Kˣ => valuation (z : K)) heval).trans
    ((hvaluation _).trans (mem_characterValuationKernel.mp hg χ'))

/-- Coefficient conjugation preserves and reflects the common valuation kernel of
 the actual rational characters, provided it preserves the field valuation. -/
theorem rationalConjugate_mem_characterValuationKernel_iff
    (σ : K ≃ₐ[k] K) (hvaluation : ∀ x : K, valuation (σ x) = valuation x)
    (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈ characterValuationKernel valuation (baseChanged k K G) ↔
      g ∈ characterValuationKernel valuation (baseChanged k K G) := by
  constructor
  · intro hg
    have hinv (x : K) : valuation (σ⁻¹ x) = valuation x := by
      exact (hvaluation (σ.symm x)).symm.trans (congrArg valuation (σ.apply_symm_apply x))
    have h := rationalConjugate_mem_characterValuationKernel k K G valuation σ⁻¹ hinv
      (rationalConjugate k K G σ g) hg
    simpa only [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one] using h
  · exact rationalConjugate_mem_characterValuationKernel k K G valuation σ hvaluation g

/-- A semilinear permutation transports the full character-kernel stabilizer,
without requiring its base point to be fixed. -/
theorem rationalConjugate_mem_characterKernel_inf_stabilizer_iff
    (σ : K ≃ₐ[k] K) (hvaluation : ∀ x : K, valuation (σ x) = valuation x)
    {Y : Type v} [MulAction (rationalPoints (baseChanged k K G)) Y]
    (α : Equiv.Perm Y)
    (hα : ∀ (g : rationalPoints (baseChanged k K G)) (z : Y),
      α (g • z) = rationalConjugate k K G σ g • α z)
    (y : Y) (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈
        characterValuationKernel valuation (baseChanged k K G) ⊓
          MulAction.stabilizer (rationalPoints (baseChanged k K G)) (α y) ↔
      g ∈ characterValuationKernel valuation (baseChanged k K G) ⊓
        MulAction.stabilizer (rationalPoints (baseChanged k K G)) y := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    rationalConjugate_mem_characterValuationKernel_iff k K G valuation σ hvaluation,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← hα]
  exact and_congr_right fun _ => α.injective.eq_iff

end InvariantValuation

/-- Internal algebraic assertion: at a coefficient-fixed point of any semilinear
`G(K)`-set, the subgroup `G(K)^1 ∩ G(K)_y` is stable under every coefficient
automorphism of the maximal unramified field. -/
def UnramifiedFixedPointStabilizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (Y : Type u) [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm Y),
    (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (z : Y),
      ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z) →
    ∀ y : Y, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, ρ σ y = y) →
    ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)),
      rationalConjugate F (inertiaFixedField F) G σ g ∈
          characterValuationKernel (MaximalUnramified.valuation F)
              (baseChanged F (inertiaFixedField F) G) ⊓
            MulAction.stabilizer (rationalPoints (baseChanged F (inertiaFixedField F) G)) y ↔
        g ∈ characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (inertiaFixedField F) G) ⊓
          MulAction.stabilizer (rationalPoints (baseChanged F (inertiaFixedField F) G)) y

/-- The fixed-point stabilizer assertion follows from actual character transport,
valuation invariance and injectivity of the semilinear permutations. -/
theorem unramifiedFixedPointStabilizer : UnramifiedFixedPointStabilizerStatement.{u} := by
  intro F _ _ _ _ G Y _ ρ hρ y hy σ g
  have h := rationalConjugate_mem_characterKernel_inf_stabilizer_iff F
    (inertiaFixedField F) G (MaximalUnramified.valuation F) σ
    (MaximalUnramified.valuation_galois F σ) (ρ σ) (hρ σ) y g
  simpa only [hy σ] using h

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)
  (hD : GaloisStable k K i D)

/-- The actual coefficient action on the supplied root-valuation quotient
transports its character-kernel point stabilizers. -/
theorem rationalConjugate_mem_characterKernel_inf_reducedFixer_iff
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation K Γ₀) (σ : K ≃ₐ[k] K)
    (hvaluation : ∀ x : K, valuation (σ x) = valuation x)
    (y : D.ReducedBuilding) (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈
        characterValuationKernel valuation (baseChanged k K G) ⊓
          D.reducedFixer (galoisQuotientAction k K i D hD σ y) ↔
      g ∈ characterValuationKernel valuation (baseChanged k K G) ⊓ D.reducedFixer y := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    rationalConjugate_mem_characterValuationKernel_iff k K G valuation σ hvaluation,
    D.mem_reducedFixer, D.mem_reducedFixer,
    galoisQuotientAction_smul_eq_iff k K i D hD]

end KPApartmentData

end Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

open Langlands.Geometry.Building

set_option maxHeartbeats 800000 in
/-- If the supplied smooth upstairs model has the full character-kernel
stabilizer of a coefficient-fixed point as its integral-point image, the
smooth-model descent statement applies. Neither model existence nor that
descent statement is assumed to be proved here. -/
theorem exists_descent_of_fixedPoint_integralPoints
    (hdescent : UnramifiedSmoothModelDescentStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    {Y : Type u}
    [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm Y)
    (hρ : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (z : Y),
      ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z)
    (y : Y) (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, ρ σ y = y)
    (M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM' : M'.IsSmooth)
    (himage : M'.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        MulAction.stabilizer (rationalPoints (baseChanged F (inertiaFixedField F) G)) y) :
    ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
      Nonempty (M.baseChangeUnramified.Iso M' (CategoryTheory.Iso.refl _)) := by
  apply hdescent F G M' hM'
  intro σ g hg
  rw [himage] at hg ⊢
  exact (unramifiedFixedPointStabilizer F G Y ρ hρ y hy σ g).mpr hg

end Langlands.GroupScheme.IntegralModel
