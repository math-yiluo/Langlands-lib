import Langlands.Representation.Exponents.UnramifiedJacquetExponentTwist
import Langlands.Representation.Exponents.ArbitraryParabolicExponentProof
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof

/-! # Fixed exponent norms throughout actual unitary twist families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryExponentNormAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Norms of the actual normalized Jacquet exponents at one specified point of
its split component. -/
def normalizedJacquetExponentNormSet (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (t : rationalPoints A.toGrp) : Set ℝ≥0 :=
  (fun χ : rationalPoints A.toGrp →* ℂˣ => ‖(χ t : ℂ)‖₊) ''
    normalizedJacquetExponents p l r hp hl hr hmul ha π

/-- For an admissible finite-length representation, the set of exponent norms
at each split-component point is finite. -/
theorem normalizedJacquetExponentNormSet_finite (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : π.IsAdmissible) (hfinite : π.HasFiniteLength) (t : rationalPoints A.toGrp) :
    (normalizedJacquetExponentNormSet p l r hp hl hr hmul ha π t).Finite := by
  have h := ((arbitraryParabolicExponent k G hG).1 P M U A p l r a hp hl hr hmul ha π hπ).2.2
    hfinite
  exact h.image _

/-- Unitary ambient twisting adds no new norms to the actual normalized Jacquet
exponents, at any specified component point. -/
theorem normalizedJacquetExponentNormSet_unitaryTwist_subset
    (ha : IsSplitComponent a)
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (hψ : ∀ g, ‖(ψ.val g : ℂ)‖ = 1)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (t : rationalPoints A.toGrp) :
    normalizedJacquetExponentNormSet p l r hp hl hr hmul ha
        (π.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) t ⊆
      normalizedJacquetExponentNormSet p l r hp hl hr hmul ha π t := by
  rintro z ⟨χ, hχ, rfl⟩
  obtain ⟨χ₀, hχ₀, heq, _⟩ :=
    exists_normalizedJacquetExponent_untwist p l r hp hl hr hmul ha ψ π χ hχ
  refine ⟨χ₀, hχ₀, ?_⟩
  have hψn : ∀ g, ‖(ψ.val.toMonoidHom g : ℂ)‖₊ = 1 := fun g => NNReal.coe_injective (hψ g)
  simp only [heq, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, nnnorm_mul,
    hψn, mul_one]

namespace GeometricLemmaIntersectionDatum

variable {Q L V : GroupScheme (Spec (CommRingCat.of k))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : V ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- A fixed finite set contains every split-component exponent norm of this
actual full geometric-lemma piece throughout all unitary unramified source twists.
It is the norm set of the untwisted inner source Jacquet module. -/
theorem exists_finite_unitaryTwistedPiece_exponentNorms
    {A' : CommGroupScheme (Spec (CommRingCat.of k))}
    {aL : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}
    (ha : IsSplitComponent aL) (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = aL)
    (t : rationalPoints A.toGrp) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), σ.IsAdmissible → σ.HasFiniteLength →
      ∃ R : Set ℝ≥0, R.Finite ∧
        ∀ (ψ : Plancherel.unramifiedCharacters
          (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
          (∀ m, ‖(ψ.val m : ℂ)‖ = 1) →
          ∀ χ : rationalPoints A.toGrp →* ℂˣ,
            IsGeneralizedEigencharacter
              ((D.pieceFunctor.obj (σ.twist ψ.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
                  (rationalPoints.map aL)) χ →
              ‖(χ t : ℂ)‖₊ ∈ R := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hσ hσfinite
  let := leviPointTopology D.l' D.hl'
  let t' := rationalPoints.map (CommGroupScheme.groupHom f) t
  let R := normalizedJacquetExponentNormSet D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul'
    (ha'.comp_iso D.φ) σ t'
  have hR : R.Finite := normalizedJacquetExponentNormSet_finite
    D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' hl.isConnectedReductive
      (ha'.comp_iso D.φ) σ hσ hσfinite t'
  refine ⟨R, hR, ?_⟩
  intro ψ hψ χ hχ
  have hτ := (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hσ
  have hJτ' := arbitraryParabolicJacquetAdmissibility k M hl.isConnectedReductive
    D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' _ hτ
  have hJτ : ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj
      (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv D.p' D.l' D.hp' D.hl') hJτ'
  obtain ⟨θ, hθ, heq, _⟩ :=
    exists_untwisted_sourceJacquetExponent_of_twisted_piece p l r hp hl hr hmul D
      ha ha' f hf σ ψ hJτ χ hχ
  refine ⟨θ, hθ, ?_⟩
  have hψn : ∀ m, ‖(ψ.val.toMonoidHom m : ℂ)‖₊ = 1 := fun m => NNReal.coe_injective (hψ m)
  simp only [t', heq, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, nnnorm_mul,
    hψn, mul_one]

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
