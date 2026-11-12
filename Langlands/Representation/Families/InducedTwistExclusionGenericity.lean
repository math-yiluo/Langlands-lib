import Langlands.Representation.Families.InducedTwistExclusionChamber
import Langlands.Representation.Families.InducedTwistExclusionConcrete
import Langlands.Representation.LanglandsClassification.UnramifiedPieceDisplacement
import Langlands.Representation.LanglandsClassification.LeviPositiveUnramifiedParameter
import Langlands.Representation.Exponents.UnramifiedJacquetExponentTwist
import Langlands.Representation.Families.UnramifiedPolynomialWitness
import Langlands.Representation.Smooth.IsotypicProjector
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof

/-! # Zariski-generic separation of geometric-lemma pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistExclusion

universe uM uA uV

/-- An admissible representation, finitely generated over its group algebra, has only
finitely many generalized eigencharacters along a central map. -/
theorem finite_isGeneralizedEigencharacter {M : Type uM} [Group M] [TopologicalSpace M]
    [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M] {A : Type uA} [Group A]
    (j : A →* M) (hj : ∀ t : A, j t ∈ Subgroup.center M)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ M V)
    (hπ : IsAdmissible π) [Module.Finite (MonoidAlgebra ℂ M) π.asModule] :
    {χ : A →* ℂˣ | IsGeneralizedEigencharacter (π.comp j) χ}.Finite := by
  let _ : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  apply (finite_generalizedWeights π j hj hπ).subset
  intro χ hχ
  exact ⟨isOpen_discrete _, (generalizedWeightSpace_ne_bot_iff j χ hj hπ.1).mpr hχ⟩

end Langlands.InducedTwistExclusion

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Displacement

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance : Mono pres.data.i.hom.hom.left :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.mono

/-- Equal moduli of two characters of a split torus give equal normalized real parts. -/
theorem normalizedRealPart_eq_of_norm_eq {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (χ₁ χ₂ : rationalPoints T.toGrp →* ℂˣ)
    (h : ∀ t, ‖(χ₁ t : ℂ)‖ = ‖(χ₂ t : ℂ)‖) :
    Plancherel.SplitTorus.normalizedRealPart hT χ₁ =
      Plancherel.SplitTorus.normalizedRealPart hT χ₂ := by
  have hn : Plancherel.SplitTorus.characterNorm χ₁ =
      Plancherel.SplitTorus.characterNorm χ₂ := by
    apply MonoidHom.ext
    intro t
    apply Units.ext
    apply NNReal.coe_injective
    exact h t
  unfold Plancherel.SplitTorus.normalizedRealPart Plancherel.SplitTorus.sectionLog
  simp only [hn]

/-- On a nonidentity piece, a character in the open coroot chamber has different moduli
at some point of the split component and at its conjugate through the piece. -/
theorem exists_norm_ne_of_nonidentity (hG : IsConnectedReductive G)
    (R : RelativeRootReflectionData pres.data.i)
    (ψ : leviUnramifiedCharacters l hl)
    (hψ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))} (a' : A'.toGrp ⟶ D.L')
    (g : A.toGrp ⟶ A'.toGrp) (hg : g ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (hz : DoubleCoset.mk (pointImage p) (pointImage p) z ≠
      DoubleCoset.mk (pointImage p) (pointImage p) 1) :
    letI := leviPointTopology l hl
    ∃ t : rationalPoints A.toGrp,
      ‖(ψ.val (rationalPoints.map (g ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p') t) : ℂ)‖ ≠
        ‖(ψ.val (rationalPoints.map a t) : ℂ)‖ := by
  let := leviPointTopology l hl
  obtain ⟨δ, -, hδ0, hδ⟩ := D.normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity pres
    rfl hG R ψ hψ (g ≫ a') (by simpa only [Category.assoc] using hg) hz
  by_contra hcon
  push Not at hcon
  have heq := normalizedRealPart_eq_of_norm_eq
    pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
    (ψ.val.toMonoidHom.comp (rationalPoints.map ((g ≫ a') ≫ D.φ.hom ≫ D.l' ≫ D.p')))
    (ψ.val.toMonoidHom.comp (rationalPoints.map a)) (fun t => by
      have h := hcon t
      simp only [Category.assoc] at h ⊢
      exact h)
  rw [heq] at hδ
  apply hδ0
  have h2 : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ =
      leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ - δ := hδ
  have := congrArg (fun x => leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ - x) h2
  simpa using this.symm

end Displacement

section Polynomial

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {P M : GroupScheme (Spec (CommRingCat.of k))} (l : M ⟶ P) (hl : IsRationalLeviSubgroup l)

/-- A finite product of polynomials is nonzero at a character exactly when every factor is. -/
theorem mem_rationalUnramifiedPrincipalOpen_prod {κ : Type*} (s : Finset κ)
    (f : κ → MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ)
    (ψ : leviUnramifiedCharacters l hl) :
    letI := leviPointTopology l hl
    ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive (∏ j ∈ s, f j) ↔
      ∀ j ∈ s, ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive (f j) := by
  let := leviPointTopology l hl
  simp only [Plancherel.mem_rationalUnramifiedPrincipalOpen, map_prod, ne_eq,
    Finset.prod_eq_zero_iff, not_exists, not_and]

/-- Two points with distinct values of one unramified character give a nonzero polynomial
off whose zero set the two weighted evaluations differ. -/
theorem exists_polynomial_ne_of_two_points (g₁ g₂ : rationalPoints M) (c₁ c₂ : ℂˣ)
    (ψ₀ : leviUnramifiedCharacters l hl)
    (h₀ : (letI := leviPointTopology l hl; (ψ₀.val g₁ : ℂ)) ≠
      (letI := leviPointTopology l hl; (ψ₀.val g₂ : ℂ))) :
    letI := leviPointTopology l hl
    ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
        (c₁ : ℂ) * ψ.val g₁ ≠ (c₂ : ℂ) * ψ.val g₂ := by
  let := leviPointTopology l hl
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let ν := fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul
  let b : Plancherel.unramifiedRegularFunctions ν :=
    algebraMap ℂ _ (c₁ : ℂ) * Plancherel.unramifiedEvaluationRegular ν g₁ -
      algebraMap ℂ _ (c₂ : ℂ) * Plancherel.unramifiedEvaluationRegular ν g₂
  have hb : ∀ ψ : Plancherel.unramifiedCharacters ν,
      b.val ψ = (c₁ : ℂ) * ψ.val g₁ - (c₂ : ℂ) * ψ.val g₂ := fun ψ => rfl
  have hiff := Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial_eval_ne_zero_iff
    M hl.isConnectedReductive b
  refine ⟨Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial M hl.isConnectedReductive b,
    ?_, ?_⟩
  · intro h0
    have e1 := hiff 1
    have e0 := hiff ψ₀
    rw [h0, map_zero, ne_self_iff_false, false_iff, not_not, hb] at e1 e0
    have h1 : ((1 : Plancherel.unramifiedCharacters ν).val g₁ : ℂ) = 1 := rfl
    have h2 : ((1 : Plancherel.unramifiedCharacters ν).val g₂ : ℂ) = 1 := rfl
    rw [h1, h2, mul_one, mul_one, sub_eq_zero] at e1
    rw [e1, ← mul_sub, mul_eq_zero, sub_eq_zero] at e0
    rcases e0 with h | h
    · exact Units.ne_zero c₂ h
    · exact h₀ h
  · intro ψ hψ
    have h := (hiff ψ).mp ((Plancherel.mem_rationalUnramifiedPrincipalOpen _ _ _ ψ).mp hψ)
    rw [hb] at h
    exact sub_ne_zero.mp h

end Polynomial

section Piece

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceSeparationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- **Generic separation of one nonidentity piece.** For an irreducible admissible `ρ` and
a nonidentity double coset, there is a nonzero polynomial such that, at every unramified
`ψ` off its zero set, no generalized `A_M`-eigencharacter of `ρψ` is a generalized
`A_M`-eigencharacter of the corresponding geometric-lemma piece of `ρψ`. -/
theorem exists_polynomial_pieceSeparation (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (pres : ParabolicRootPresentation p l a) [Mono pres.data.i.hom.hom.left]
    (R : RelativeRootReflectionData pres.data.i)
    (ψ₀ : leviUnramifiedCharacters l hl)
    (hψ₀ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ₀ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hρadm : letI := leviPointTopology l hl; ρ.IsAdmissible)
    {z : rationalPoints G}
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
    (hz : DoubleCoset.mk (pointImage p) (pointImage p) z ≠
      DoubleCoset.mk (pointImage p) (pointImage p) 1) :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
        ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            ((ρ.twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation.comp
                (rationalPoints.map a)) χ →
          ¬ IsGeneralizedEigencharacter
            ((D.pieceFunctor.obj (ρ.twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
                (rationalPoints.map a)) χ := by
  let := leviPointTopology l hl
  have := hl.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hG.smooth
  have ha := pres.isCompatible.splitComponent
  -- the split component of the intersection Levi
  obtain ⟨A', a', g, ha', hg⟩ := D.exists_isSplitComponent_factor ha
  -- a point separating the moduli of `ψ₀`
  obtain ⟨t, ht⟩ := exists_norm_ne_of_nonidentity D pres hG R ψ₀ hψ₀ a' g hg hz
  have ht' : (ψ₀.val (rationalPoints.map (g ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p') t) : ℂ) ≠
      ψ₀.val (rationalPoints.map a t) := fun h => ht (congrArg norm h)
  -- the finitely many untwisted source exponents
  let := leviPointTopology D.l' D.hl'
  have := leviPoints_locallyCompactSpace D.p' D.l' D.hp' D.hl'
  have := leviPoints_nonarchimedeanGroup D.p' D.l' D.hp' D.hl'
  have hρfin := moduleFinite_asModule_of_isIrreducible ρ.representation hρirr
  have hJfin := leviJacquetFiniteType k M hl.isConnectedReductive D.P' D.M' D.N' D.p' D.l' D.r'
    D.hp' D.hl' D.hr' D.hmul' ρ hρfin
  have hJadm' := arbitraryParabolicJacquetAdmissibility k M hl.isConnectedReductive
    D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ρ hρadm
  have hJadm : IsAdmissible ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl'
      D.hmul').obj ρ).representation :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv D.p' D.l' D.hp' D.hl') hJadm'
  have hcentral' : ∀ s, rationalPoints.map (a' ≫ D.φ.hom) s ∈
      Subgroup.center (rationalPoints D.M') :=
    fun s => (ha'.comp_iso D.φ).1.2.map_mem_center s
  have hΘ := InducedTwistExclusion.finite_isGeneralizedEigencharacter
    (rationalPoints.map (a' ≫ D.φ.hom)) hcentral' _ hJadm
  have hcentral : ∀ s, rationalPoints.map a s ∈ Subgroup.center (rationalPoints M) :=
    fun s => ha.1.2.map_mem_center s
  have hΩ := InducedTwistExclusion.finite_isGeneralizedEigencharacter
    (rationalPoints.map a) hcentral ρ.representation hρadm
  -- one polynomial for each pair of exponents
  have hpoly : ∀ q : (rationalPoints A'.toGrp →* ℂˣ) × (rationalPoints A.toGrp →* ℂˣ),
      ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
        ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
          ((q.1 (rationalPoints.map g t) : ℂˣ) : ℂ) *
              ψ.val (rationalPoints.map (g ≫ a' ≫ D.φ.hom ≫ D.l' ≫ D.p') t) ≠
            ((q.2 t : ℂˣ) : ℂ) * ψ.val (rationalPoints.map a t) :=
    fun q => exists_polynomial_ne_of_two_points l hl _ _ _ _ ψ₀ ht'
  choose F hF0 hF using hpoly
  refine ⟨∏ q ∈ hΘ.toFinset ×ˢ hΩ.toFinset, F q,
    Finset.prod_ne_zero_iff.mpr (fun q _ => hF0 q), ?_⟩
  intro ψ hψ χ hχρ hχD
  -- the source exponent of the piece
  have hτ := (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) ρ).mpr hρadm
  have hJτ' := arbitraryParabolicJacquetAdmissibility k M hl.isConnectedReductive
    D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' _ hτ
  have hJτ : ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv D.p' D.l' D.hp' D.hl') hJτ'
  obtain ⟨θ, hθ, hχeq, -⟩ :=
    GeometricLemmaIntersectionDatum.exists_untwisted_sourceJacquetExponent_of_twisted_piece
    p l r hp hl hr hmul D ha ha' (Additive.ofMul g) hg ρ ψ hJτ χ hχD
  have hθ' := (isNormalizedJacquetExponent_iff_leviJacquet D.p' D.l' D.r' D.hp' D.hl' D.hr'
    D.hmul' (ha'.comp_iso D.φ) ρ θ).mp hθ
  -- the untwisted exponent of `ρ`
  let ω := χ * (ψ.val.toMonoidHom.comp (rationalPoints.map a))⁻¹
  have hω : IsGeneralizedEigencharacter (ρ.representation.comp (rationalPoints.map a)) ω :=
    (isGeneralizedEigencharacter_twist_iff (ρ.representation.comp (rationalPoints.map a))
      (ψ.val.toMonoidHom.comp (rationalPoints.map a)) χ).mp hχρ
  have hmem := (mem_rationalUnramifiedPrincipalOpen_prod l hl _ F ψ).mp hψ (θ, ω)
    (Finset.mk_mem_product (hΘ.mem_toFinset.mpr hθ') (hΩ.mem_toFinset.mpr hω))
  apply hF (θ, ω) ψ hmem
  have h1 := congrArg (fun φ : rationalPoints A.toGrp →* ℂˣ => ((φ t : ℂˣ) : ℂ)) hχeq
  have h2 : ((χ t : ℂˣ) : ℂ) = ((ω t : ℂˣ) : ℂ) * ψ.val (rationalPoints.map a t) := by
    simp only [ω, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
      Units.val_mul, mul_assoc]
    have hinv : (ψ.val.toMonoidHom (rationalPoints.map a t))⁻¹ *
        ψ.val (rationalPoints.map a t) = 1 := inv_mul_cancel _
    rw [← Units.val_mul, hinv, Units.val_one, mul_one]
  rw [← h2]
  exact h1.symm

end Piece

end Langlands.Aubert.General.RepresentedParabolic
