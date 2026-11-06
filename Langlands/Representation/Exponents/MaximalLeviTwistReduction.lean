import Langlands.Representation.Exponents.MaximalLeviReducibilityReductionStatements
import Langlands.Representation.Exponents.UnramifiedTwistRadicals

/-! # Unramified twists in the maximal-Levi reducibility theorem

Renard 2026, VII.1.3, first step of the proof (printed p.224/PDF p.230), with the
twisting isomorphism III.2.11: replacing `ρ` by `ρ ⊗ χ_M` for an unramified character
`χ` of `G(F)` changes neither the hypotheses nor the conclusion of the theorem. The last
theorem derives `MaximalLeviSupercuspidalReducibilityStatement` from its unitary case and
the unramified twist of VI.8.5.

The radical conditions needed by the published general twist comparisons for normalized
induction and normalized Jacquet modules come from
`Langlands.Representation.Exponents.UnramifiedTwistRadicals`: unramified characters are
trivial on the points of every unipotent group.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Levi

variable {k : Type u} [Field k] {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- `χ_M` is invariant under an automorphism of `M` induced by conjugation in `G(F)`. -/
theorem leviRestrictedCharacter_map_eq_of_conj (p : P ⟶ G) (l : M ⟶ P)
    (χ : rationalPoints G →* ℂˣ) (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom) (m : rationalPoints M) :
    leviRestrictedCharacter p l χ (rationalPoints.map φ.hom m) = leviRestrictedCharacter p l χ m := by
  rw [leviRestrictedCharacter_apply, leviRestrictedCharacter_apply, ← pointMap_comp_apply, hφ,
    ← Category.assoc, pointMap_comp_apply, rationalPoints_map_innerIso]
  change χ (g * rationalPoints.map (l ≫ p) m * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- For an unramified `χ`, `χ_M` is trivial on the radical points of every parabolic
of `M`. -/
theorem leviRestrictedCharacter_map_radical_eq_one [TopologicalSpace (rationalPoints G)]
    (p : P ⟶ G) (l : M ⟶ P)
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    {P' U' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ M) (r' : U' ⟶ P')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r') (y : rationalPoints U') :
    leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom
      (rationalPoints.map (r' ≫ p') y) = 1 := by
  rw [leviRestrictedCharacter_apply, ← pointMap_comp_apply]
  exact unramifiedCharacter_map_eq_one_of_isUnipotent χ _ hr'.1.isUnipotent y

variable [IsAffineHom G.X.hom]

local instance twistAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [NonarchimedeanGroup (rationalPoints G)]

section Induction

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)] in
/-- Pulling `σ ⊗ χ_M` back to the Levi image gives the twist by the restriction of `χ`
to the Levi image. -/
theorem pullback_leviRestrictedCharacter_twist_representation (p : P ⟶ G) (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm
        (σ.twist (leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom)
          (isOpen_ker_leviRestrictedCharacter p l hp hl
            (χ : rationalPoints G →ₜ* ℂˣ)))).representation =
      ((SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ).twist
        (subgroupSmoothCharacter (unramifiedSmoothCharacter χ) (pointImage (l ≫ p))).toMonoidHom
        (subgroupSmoothCharacter (unramifiedSmoothCharacter χ)
          (pointImage (l ≫ p))).isOpen_ker).representation := by
  let := leviPointTopology l hl
  ext x w
  change (((χ : rationalPoints G →ₜ* ℂˣ)
        (rationalPoints.map (l ≫ p) ((leviPointsEquiv p l hp hl).symm x)) : ℂˣ) : ℂ) •
      σ.representation ((leviPointsEquiv p l hp hl).symm x) w =
    (((χ : rationalPoints G →ₜ* ℂˣ) (x : rationalPoints G) : ℂˣ) : ℂ) •
      σ.representation ((leviPointsEquiv p l hp hl).symm x) w
  rw [← leviPointsEquiv_apply_coe p l hp hl, ContinuousMulEquiv.apply_symm_apply]

/-- Renard III.2.11 for the transported induction: `i_P^G(σ ⊗ χ_M) ≅ (i_P^G σ) ⊗ χ`
for an unramified character `χ` of `G(F)`. -/
def leviInductionUnramifiedTwistIso (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (leviInductionFunctor p l r hp hr hl hmul).obj
        (σ.twist (leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom)
          (isOpen_ker_leviRestrictedCharacter p l hp hl (χ : rationalPoints G →ₜ* ℂˣ))) ≅
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).twist
        (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom
        (Plancherel.unramifiedCharacter_isOpen_ker _ χ) :=
  letI := leviPointTopology l hl
  (inductionFunctor p l r hp hr hl hmul).mapIso
      (SmoothRep.mkIso
        (A := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm
          (σ.twist (leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom)
            (isOpen_ker_leviRestrictedCharacter p l hp hl (χ : rationalPoints G →ₜ* ℂˣ))))
        (B := (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ).twist
          (subgroupSmoothCharacter (unramifiedSmoothCharacter χ) (pointImage (l ≫ p))).toMonoidHom
          (subgroupSmoothCharacter (unramifiedSmoothCharacter χ)
            (pointImage (l ≫ p))).isOpen_ker)
        (equivOfRepresentationEq
          (pullback_leviRestrictedCharacter_twist_representation p l hp hl χ σ))) ≪≫
    ((normalizedInductionCharacterTwistIso
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (unramifiedSmoothCharacter χ)
      (pointImage_radical_le_ker_unramifiedSmoothCharacter p r hr χ)).app
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)).symm

/-- Irreducibility of the transported induction is unchanged by an unramified twist. -/
theorem leviInduction_isIrreducible_unramifiedTwist_iff (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (χ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj
        (σ.twist (leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom)
          (isOpen_ker_leviRestrictedCharacter p l hp hl
            (χ : rationalPoints G →ₜ* ℂˣ)))).IsIrreducible ↔
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsIrreducible := by
  let := leviPointTopology l hl
  rw [← SmoothRep.isIrreducible_twist_iff (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ χ)
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ)]
  exact ⟨SmoothRep.isIrreducible_of_iso (leviInductionUnramifiedTwistIso p l r hp hr hl hmul χ σ),
    SmoothRep.isIrreducible_of_iso (leviInductionUnramifiedTwistIso p l r hp hr hl hmul χ σ).symm⟩

end Induction

end Levi

section Conclusion

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- An intertwining relation `T ∘ (ρ ⊗ ν)(m) = c(m) • (ρ ⊗ ν)(f m) ∘ T` gives the same
relation for `ρ` when `ν ∘ f = ν`. -/
theorem intertwining_relation_of_twist (ρ : SmoothRep.{0, u, v} ℂ Γ) (ν : Γ →* ℂˣ)
    (hν : IsOpen (ν.ker : Set Γ)) (f : Γ → Γ) (hf : ∀ m, ν (f m) = ν m) (c : Γ → ℂ)
    (T : ρ ≃ₗ[ℂ] ρ)
    (hT : ∀ (m : Γ) (x : ρ), T ((ρ.twist ν hν).representation m x) =
      c m • (ρ.twist ν hν).representation (f m) (T x))
    (m : Γ) (x : ρ) :
    T (ρ.representation m x) = c m • ρ.representation (f m) (T x) := by
  have h : T (((ν m : ℂˣ) : ℂ) • ρ.representation m x) =
      c m • (((ν (f m) : ℂˣ) : ℂ) • ρ.representation (f m) (T x)) := hT m x
  rw [map_smul, hf, smul_comm (c m)] at h
  exact smul_right_injective ρ (Units.ne_zero (ν m)) h

end Conclusion

/-- Renard VII.1.3 from its unitary case and the unramified twist of VI.8.5: twisting `ρ`
by `χ_M` preserves irreducibility, supercuspidality and reducibility of the induction,
and the conclusion for `ρ ⊗ χ_M` is the conclusion for `ρ` with the same `g`, `φ`, `ψ`
and `T`. -/
theorem maximalLeviSupercuspidalReducibility_of_unitary
    (hU : MaximalLeviSupercuspidalReducibilityUnitaryStatement.{u, v})
    (hX : MaximalLeviUnitaryCentralTwistStatement.{u, v}) :
    MaximalLeviSupercuspidalReducibilityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hcusp hred
  obtain ⟨χ, hχ⟩ := hX k G hG P M U p l r hp hl hr hmul ρ hirr hcusp
  have hker := isOpen_ker_leviRestrictedCharacter p l hp hl (χ : rationalPoints G →ₜ* ℂˣ)
  obtain ⟨g, φ, hφ, hg, ψ, hψ, T, hT⟩ := hU k G hG P M U p l r hp hl hr hmul hproper hmax
    (ρ.twist _ hker) ((SmoothRep.isIrreducible_twist_iff _ hker ρ).mpr hirr)
    (fun P' M' U' p' l' r' hp' hl' hr' hmul' hp'proper =>
      (jacquetFunctor_subsingleton_twist_iff p' l' r' hp' hl' hr' hmul'
        ⟨leviRestrictedCharacter p l (χ : rationalPoints G →ₜ* ℂˣ).toMonoidHom, hker⟩
        (by
          rintro _ ⟨y, rfl⟩
          exact leviRestrictedCharacter_map_radical_eq_one p l χ p' r' hr' y)
        ρ).mpr (hcusp P' M' U' p' l' r' hp' hl' hr' hmul' hp'proper))
    ((leviInduction_isIrreducible_unramifiedTwist_iff p l r hp hr hl hmul χ ρ).not.mpr hred) hχ
  exact ⟨g, φ, hφ, hg, ψ, hψ, T, intertwining_relation_of_twist ρ _ hker _
    (leviRestrictedCharacter_map_eq_of_conj p l _ g φ hφ) _ T hT⟩

end Langlands.Aubert.General.RepresentedParabolic
