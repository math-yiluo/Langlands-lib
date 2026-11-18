import Langlands.Representation.Families.InducedTwistQuotientExclusionProof
import Langlands.Representation.Families.InducedTwistPersistenceEndpoints
import Langlands.Representation.Families.InducedTwistPersistenceAssembly
import Langlands.Representation.Exponents.LeviInductionUnitarityProof
import Langlands.Representation.Exponents.TemperedUniquenessIntertwiners
import Langlands.Representation.LanglandsClassification.LeviInductionQuotient
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Unitary.Twist

/-! # Generic irreducibility of represented induction at unitary twists -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Aubert.General Aubert.General.RepresentedParabolic GroupScheme Plancherel

section Quotients

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- A nonzero proper summand gives a nonzero intertwiner from a quotient by a
nonzero invariant subspace into the original representation. -/
private theorem exists_quotientIntertwiner (W : SmoothRep.{0, u, v} ℂ H)
    (hsem : W.representation.IsSemisimpleRepresentation)
    (S : Subrepresentation W.representation) (hbot : S ≠ ⊥) (htop : S ≠ ⊤) :
    ∃ (T : Subrepresentation W.representation), T ≠ ⊥ ∧
      ∃ f : (W.quotient T).representation.IntertwiningMap W.representation, f ≠ 0 := by
  let i := SmoothRep.hom (SmoothRep.subtype W S)
  let r := semisimpleIntertwiningRetraction hsem i (SmoothRep.subtype_injective W S)
  let e := i.comp r.map
  have hfix (v : W.subrepresentation S) : e (i v) = i v := by
    change i (r.map (i v)) = i v
    rw [r.left_inverse v]
  have he : e ≠ 0 := by
    have hS : S.toSubmodule ≠ ⊥ := fun h => hbot (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hS
    have h := hfix ⟨v, hv⟩
    intro hzero
    rw [hzero] at h
    change 0 = v at h
    exact hv0 h.symm
  have hker : e.ker ≠ ⊥ := by
    intro hzero
    have hinj : Function.Injective e := LinearMap.ker_eq_bot.mp
      (congrArg Subrepresentation.toSubmodule hzero)
    apply htop
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    rw [Submodule.eq_top_iff']
    intro v
    have hv : i (r.map v) = v := hinj (hfix (r.map v))
    rw [← hv]
    exact (r.map v).property
  let f : (W.quotient e.ker).representation.IntertwiningMap W.representation :=
    { toLinearMap := e.ker.toSubmodule.liftQ e.toLinearMap le_rfl
      isIntertwining' g := by
        apply Submodule.linearMap_qext
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ e g v }
  refine ⟨e.ker, hker, f, fun hzero => he ?_⟩
  ext v
  change f (SmoothRep.hom (W.mkQ e.ker) v) = 0
  rw [hzero]
  rfl

end Quotients

/-- A nonzero polynomial witnesses irreducibility of normalized induction at
unitary unramified twists of an irreducible admissible unitarizable representation. -/
theorem exists_generic_leviInduction_isIrreducible_of_unitary
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
      IsSplitComponent a →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ρ.IsIrreducible → ρ.IsAdmissible → IsUnitarizable ρ.representation →
        ∃ f : MvPolynomial (Fin (rationalImageRank M)) ℂ, f ≠ 0 ∧
          ∀ ψ ∈ rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
            (∀ m, ‖(ψ.val m : ℂ)‖ = 1) →
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible := by
  intro _ _ P M U p l r hp hl hr hmul A a ha ρ hρ hadm hunit
  classical
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨f, hf, hexclude⟩ := inducedTwistQuotientExclusion.{u, v} k G hG
    P M U p l r hp hl hr hmul A a ha ρ hρ hadm
  refine ⟨f, hf, ?_⟩
  intro ψ hψ hψunit
  let τ := ρ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)
  have hτi : τ.IsIrreducible := (SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ
  have hτa : τ.IsAdmissible := (SmoothRep.isAdmissible_twist_iff _ _ ρ).mpr hadm
  have hτu : IsUnitarizable τ.representation :=
    (isUnitarizable_twist_iff ψ.val.toMonoidHom hψunit ρ.representation).mpr hunit
  let W := (leviInductionFunctor p l r hp hr hl hmul).obj τ
  have hWa : W.IsAdmissible := leviInductionAdmissible k G hG P M U p l r hp hl hr hmul τ hτa
  have hWu : IsUnitarizable W.representation :=
    leviInductionUnitarizable k G hG P M U p l r hp hl hr hmul τ hτu
  have hcofinal := InducedTwistPersistence.exists_compact_openSubgroup_le (rationalPoints G)
  have hWsem := admissibleUnitarySemisimplicity _ hcofinal _ W.representation hWa hWu
  have : Nontrivial τ := by
    have : τ.representation.IsIrreducible := hτi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M)) τ.representation.asModule
  have : Nontrivial W := nontrivial_leviInduction p l r hp hl hr hmul τ
  change W.IsIrreducible
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    apply hx
    have hx' : x ∈ (⊤ : Subrepresentation W.representation) := trivial
    rwa [← h] at hx'
  · intro S
    by_cases hbot : S = ⊥
    · exact Or.inl hbot
    right
    by_contra htop
    obtain ⟨T, hT, g, hg⟩ := exists_quotientIntertwiner W hWsem S hbot htop
    have hQa : (W.quotient T).IsAdmissible := isAdmissible_of_surjective_coefficients hcofinal
      (SmoothRep.hom (W.mkQ T)) (SmoothRep.mkQ_surjective W T) hWa
    have hcentral := ha.isCentralSplitTorus.isCentral
    obtain ⟨χ, hχ⟩ := InducedTwistPersistence.exists_isGeneralizedEigencharacter_of_isAdmissible
      (rationalPoints.map a) hcentral.map_mem_center τ hτi hτa
    exact hexclude ψ hψ χ hχ T hT
      (InducedTwistPersistence.isGeneralizedEigencharacter_jacquet_of_ne_zero_induction
        p l r hp hl hr hmul hG hcentral (W.quotient T) hQa τ hτi g hg χ hχ)

end Langlands.Renard.AlgebraicFamily
