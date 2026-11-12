import Langlands.Representation.Geometric.RepresentedGeometricLemmaSourceJacquet
import Langlands.Representation.Exponents.UnramifiedTwistRadicals
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Geometric.RefinedJacquetRealTwist
import Langlands.Representation.Plancherel.SplitTorusRealPart

/-! # Exact exponent shifts for actual unramified normalized Jacquet modules -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unramifiedJacquetAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Normalized Jacquet restriction commutes naturally with an arbitrary ambient
unramified twist, with the actual Levi restriction of that character. -/
def leviJacquetUnramifiedTwistIso
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul)) :
    letI := leviPointTopology l hl
    SmoothRep.twistFunctor ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) ⋙
        leviJacquetFunctor.{u, v} p l r hp hr hl hmul ≅
      leviJacquetFunctor p l r hp hr hl hmul ⋙
        SmoothRep.twistFunctor
          (leviRestrictionCharacter p l hp hl (unramifiedSmoothCharacter ψ)).toMonoidHom
          (leviRestrictionCharacter p l hp hl (unramifiedSmoothCharacter ψ)).isOpen_ker :=
  leviJacquetTwistIso p l r hp hr hl hmul (unramifiedSmoothCharacter ψ)
    (pointImage_radical_le_ker_unramifiedSmoothCharacter p r hr ψ)

/-- Exact multiplication shift of every actual normalized Jacquet exponent.
No representation finiteness or temperedness is required. -/
theorem isNormalizedJacquetExponent_unramifiedTwist_iff
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a)
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha
        (π.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π
        (χ * (ψ.val.toMonoidHom.comp (rationalPoints.map (a ≫ l ≫ p)))⁻¹) := by
  let := leviPointTopology l hl
  rw [isNormalizedJacquetExponent_iff_leviJacquet,
    isNormalizedJacquetExponent_iff_leviJacquet]
  let e := SmoothRep.equivOfIso ((leviJacquetUnramifiedTwistIso p l r hp hl hr hmul ψ).app π)
  let ec : Representation.Equiv
      (((leviJacquetFunctor p l r hp hr hl hmul).obj
        (π.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation.comp
          (rationalPoints.map a))
        (Langlands.twist
          ((leviRestrictionCharacter p l hp hl (unramifiedSmoothCharacter ψ)).toMonoidHom.comp
            (rationalPoints.map a))
          (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
            (rationalPoints.map a))) :=
    Representation.Equiv.mk e.toLinearEquiv
      (fun t : rationalPoints A.toGrp => e.isIntertwining' (rationalPoints.map a t))
  have h := (isGeneralizedEigencharacter_iff_of_equiv ec χ).trans
    (isGeneralizedEigencharacter_twist_iff _ _ _)
  have hχ :
      ((leviRestrictionCharacter p l hp hl (unramifiedSmoothCharacter ψ)).toMonoidHom).comp
        (rationalPoints.map a) =
      ψ.val.toMonoidHom.comp (rationalPoints.map (a ≫ l ≫ p)) := by
    apply MonoidHom.ext
    intro t
    change ψ.val.toMonoidHom
      (rationalPoints.map (l ≫ p) (rationalPoints.map a t)) = _
    rw [← pointMap_comp_apply]
    rfl
  simpa only [hχ] using h

/-- Every exponent of an unramified twisted Jacquet module is the product of an
untwisted exponent and the actual restricted twist, with additive normalized real parts. -/
theorem exists_normalizedJacquetExponent_untwist
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a)
    (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters G => (Plancherel.rationalNormCharacters G c).toMul))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha
      (π.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) χ) :
    ∃ χ₀ : rationalPoints A.toGrp →* ℂˣ,
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ₀ ∧
      χ = χ₀ * ψ.val.toMonoidHom.comp (rationalPoints.map (a ≫ l ≫ p)) ∧
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ₀ +
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
          (ψ.val.toMonoidHom.comp (rationalPoints.map (a ≫ l ≫ p))) := by
  let θ := ψ.val.toMonoidHom.comp (rationalPoints.map (a ≫ l ≫ p))
  refine ⟨χ * θ⁻¹,
    (isNormalizedJacquetExponent_unramifiedTwist_iff p l r hp hl hr hmul ha ψ π χ).mp hχ,
    ?_, ?_⟩
  · change χ = (χ * θ⁻¹) * θ
    ext t
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_assoc, inv_mul_cancel, mul_one]
  · rw [Plancherel.SplitTorus.normalizedRealPart_mul,
      Plancherel.SplitTorus.normalizedRealPart_inv]
    abel

namespace GeometricLemmaIntersectionDatum

variable {Q L V : GroupScheme (Spec (CommRingCat.of k))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : V ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- An exponent of an actual full geometric-lemma piece of a twisted source
is an untwisted source-Jacquet exponent restricted to the target component,
times the twist restricted through the actual intersection maps. -/
theorem exists_untwisted_sourceJacquetExponent_of_twisted_piece
    {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
      let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj τ).IsAdmissible →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter ((D.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a)) χ →
        ∃ θ : rationalPoints A'.toGrp →* ℂˣ,
          IsNormalizedJacquetExponent D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul'
            (ha'.comp_iso D.φ) σ θ ∧
          χ = θ.comp (rationalPoints.map (CommGroupScheme.groupHom f)) *
            ψ.val.toMonoidHom.comp (rationalPoints.map
              (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p')) ∧
          Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
            Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
              (θ.comp (rationalPoints.map (CommGroupScheme.groupHom f))) +
            Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
              (ψ.val.toMonoidHom.comp (rationalPoints.map
                (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p'))) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ ψ τ hJ χ hχ
  obtain ⟨ω, hω, hωχ⟩ := D.exists_isNormalizedJacquetExponent_of_piece ha ha' f hf τ hJ χ hχ
  obtain ⟨θ, hθ, hprod, _⟩ := exists_normalizedJacquetExponent_untwist
    D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' (ha'.comp_iso D.φ) ψ σ ω hω
  have heq : χ = θ.comp (rationalPoints.map (CommGroupScheme.groupHom f)) *
      ψ.val.toMonoidHom.comp (rationalPoints.map
        (CommGroupScheme.groupHom f ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p')) := by
    rw [← hωχ, hprod]
    apply MonoidHom.ext
    intro t
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply]
    rw [← pointMap_comp_apply]
    rfl
  exact ⟨θ, hθ, heq, heq ▸ Plancherel.SplitTorus.normalizedRealPart_mul _ _ _⟩

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
