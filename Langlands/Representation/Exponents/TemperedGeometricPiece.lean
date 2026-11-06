import Langlands.Representation.Exponents.TemperedGeometricPieceCone
import Langlands.Representation.Exponents.SelectedWeightSplitting
import Langlands.Representation.Exponents.TemperedGeometricLemmaStatement
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.UnitaryJacquetSplitting
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # The unitary part of one piece of the geometric lemma (Renard VII.2.5)

For intersection data `D` of a double coset `P z Q` and a tempered representation `ρ`
of `M(F)`, the zero-real-part selection, for a split component `A_L` of `L`, of the
geometric-lemma piece `i^L_{Q'} ∘ ι ∘ r^M_{P'} ρ` is the piece
`i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`. The proof splits `r^M_{P'} ρ` as the direct sum of its
unitary and nonunitary parts and induces the splitting. Exponents of `A_L` on the induced
unitary part restrict from exponents with zero real part. Exponents on the induced
nonunitary part restrict from exponents with nonzero real part in the cone of `P'`, so
their restriction to `A_L` is nonzero.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section JacquetParts

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedPieceJacquetPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- A generalized eigencharacter of the split component on a subrepresentation `S` of the
normalized Jacquet module is a normalized exponent, and its weight space contains a
nonzero vector of `S`. -/
theorem exists_mem_normalizedJacquetWeightSpace_of_subrepresentation
    (S : Subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π).representation)
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter
      (S.toRepresentation.comp (splitComponentPointsMap (l ≫ p) a)) χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
      ∃ v ∈ S, v ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ∧ v ≠ 0 := by
  obtain ⟨d, hd⟩ := hχ
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hd
  have hw' := map_mem_characterSpace_of_intertwiningMap
    (subrepresentationInclusion S (splitComponentPointsMap (l ≫ p) a)) χ d hw
  have hne : subrepresentationInclusion S (splitComponentPointsMap (l ≫ p) a) w ≠ 0 :=
    fun h => hw0 (Subtype.ext h)
  refine ⟨(isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mpr
    (isGeneralizedEigencharacter_of_map_ne_zero _ χ d hw hne), (w : _), w.2, ?_, hne⟩
  exact (mem_normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ _).mpr
    ⟨d, (mem_characterSpace _ χ d _).mp hw'⟩

/-- Every generalized eigencharacter of the split component on the unitary part
`(r_P^G π)_0` is a normalized exponent with zero normalized real part. -/
theorem normalizedRealPart_eq_zero_of_unitaryJacquetPart
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter
      ((unitaryJacquetPart p l r hp hl hr hmul ha π).toRepresentation.comp
        (splitComponentPointsMap (l ≫ p) a)) χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 := by
  obtain ⟨hexp, v, hv, hvχ, hv0⟩ :=
    exists_mem_normalizedJacquetWeightSpace_of_subrepresentation p l r hp hl hr hmul ha π _ hχ
  refine ⟨hexp, ?_⟩
  by_contra h0
  exact hv0 (Submodule.disjoint_def.mp
    (unitaryJacquetPart_disjoint_nonunitaryJacquetPart p l r hp hl hr hmul ha π) v hv
    (normalizedJacquetWeightSpace_le_nonunitaryJacquetPart p l r hp hl hr hmul ha π
      hexp h0 hvχ))

/-- Every generalized eigencharacter of the split component on the nonunitary part
`(r_P^G π)_+` is a normalized exponent with nonzero normalized real part. -/
theorem normalizedRealPart_ne_zero_of_nonunitaryJacquetPart
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter
      ((nonunitaryJacquetPart p l r hp hl hr hmul ha π).toRepresentation.comp
        (splitComponentPointsMap (l ≫ p) a)) χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0 := by
  obtain ⟨hexp, v, hv, hvχ, hv0⟩ :=
    exists_mem_normalizedJacquetWeightSpace_of_subrepresentation p l r hp hl hr hmul ha π _ hχ
  refine ⟨hexp, fun h0 => hv0 ?_⟩
  exact Submodule.disjoint_def.mp
    (unitaryJacquetPart_disjoint_nonunitaryJacquetPart p l r hp hl hr hmul ha π) v
    (normalizedJacquetWeightSpace_le_unitaryJacquetPart p l r hp hl hr hmul ha π
      hexp h0 hvχ) hv

end JacquetParts

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]

local instance temperedPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- The piece of Renard VII.2.5 for one double coset. Let `ρ` be a tempered
representation of `M(F)` whose normalized Jacquet module along `P'` is admissible, and
assume that parabolic quotients are compact and that `Q` has a root presentation for the
split component `a_L` of `L`. Then the zero-real-part selection, for `A_L`, of the piece
`i^L_{Q'} ∘ ι ∘ r^M_{P'} ρ` of the geometric lemma is isomorphic to
`i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`, for every split component `a'` of `M'`. -/
theorem nonempty_selectedWeightPart_pieceFunctor_equiv
    (hcompact : ArbitraryParabolicQuotientCompactStatement.{u})
    {AL : CommGroupScheme (Spec (CommRingCat.of k))} {aL : AL.toGrp ⟶ L}
    (haL : IsSplitComponent aL) (presQ : ParabolicRootPresentation q lQ aL)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
    (ha' : IsSplitComponent a') :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      IsNormalizedExponentTempered hl.isConnectedReductive ρ →
      ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ).IsAdmissible →
      Nonempty ((selectedWeightPart (D.pieceFunctor.obj ρ).ρ (rationalPoints.map aL)
          haL.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            haL.isCentralSplitTorus.1.1 χ = 0)).toRepresentation.Equiv
        (D.unitaryPieceRep ha' ρ).ρ) := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have := D.hlQ'.isConnectedReductive.isAffineHom
  intro ρ hρ hJac
  -- Write `a' = b ≫ φ` with `b` a split component of `L'`, and factor `a_L` through `b`.
  obtain ⟨b, rfl⟩ : ∃ b : A'.toGrp ⟶ D.L', b ≫ D.φ.hom = a' :=
    ⟨a' ≫ D.φ.inv, by simp⟩
  have hb : IsSplitComponent b := by
    simpa using ha'.comp_iso D.φ.symm
  obtain ⟨g, hg, hgc⟩ := D.exists_isCentralSplitTorus_factor haL.1
  obtain ⟨f, hf⟩ := hb.exists_factor haL.1.1.1 hgc.2
  have hf' : CommGroupScheme.groupHom (Additive.ofMul f) ≫ b ≫ D.lQ' ≫ D.q' = aL := by
    change f ≫ b ≫ D.lQ' ≫ D.q' = aL
    rw [← Category.assoc, hf, hg]
  -- The splitting of the Jacquet module into its unitary and nonunitary parts.
  let Jac := (jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ
  have hc := unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible
    D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ hJac
  let eM := leviPointsEquiv D.p' D.l' D.hp' D.hl'
  let E := SmoothRep.pullbackFunctor D.e
  let I := leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ'
  let J := (leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ
  let J₀ := leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ
  let J₁ := leviNonunitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ
  let ι₀ : J₀ ⟶ J := leviUnitaryJacquetModuleι D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ
  let ι₁ : J₁ ⟶ J :=
    leviNonunitaryJacquetModuleι D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ
  let π₀ : J ⟶ J₀ := (SmoothRep.pullbackFunctor eM).map
    (SmoothRep.subrepresentationProjection Jac _ _ hc)
  let π₁ : J ⟶ J₁ := (SmoothRep.pullbackFunctor eM).map
    (SmoothRep.subrepresentationProjection Jac _ _ hc.symm)
  have hsum : ∀ x, SmoothRep.hom ι₀ (SmoothRep.hom π₀ x) +
      SmoothRep.hom ι₁ (SmoothRep.hom π₁ x) = x :=
    fun x => SmoothRep.subtype_subrepresentationProjection_add Jac _ _ hc x
  have hsumI : ∀ x, SmoothRep.hom (I.map (E.map ι₀)) (SmoothRep.hom (I.map (E.map π₀)) x) +
      SmoothRep.hom (I.map (E.map ι₁)) (SmoothRep.hom (I.map (E.map π₁)) x) = x := by
    intro x
    apply Aubert.General.normalizedInductionFunctor_map_add_map
    exact hsum
  have hinj : Function.Injective (SmoothRep.hom (I.map (E.map ι₀))) := by
    apply Aubert.General.normalizedInductionFunctor_map_injective
    exact leviUnitaryJacquetModuleι_injective D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ
  -- Admissibility of the pieces.
  have hJ : J.IsAdmissible := isAdmissible_comp_continuousMulEquiv Jac.representation eM hJac
  have hJ₀ : J₀.IsAdmissible := isAdmissible_of_injective (SmoothRep.hom ι₀)
    (leviUnitaryJacquetModuleι_injective D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ) hJ
  have hJ₁ : J₁.IsAdmissible := isAdmissible_of_injective (SmoothRep.hom ι₁)
    (leviNonunitaryJacquetModuleι_injective D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ) hJ
  have hE : ∀ X : SmoothRep.{0, u, v} ℂ (rationalPoints D.M'), X.IsAdmissible →
      (E.obj X).IsAdmissible :=
    fun X hX => isAdmissible_comp_continuousMulEquiv X.representation D.e hX
  have hI : ∀ X : SmoothRep.{0, u, v} ℂ (rationalPoints D.L'), X.IsAdmissible →
      (I.obj X).IsAdmissible :=
    fun X hX => leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement hcompact
      hlQ.isConnectedReductive D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' X hX
  -- Induced pieces: every weight is the restriction of a weight on the Jacquet part.
  have hι := haL.isCentralSplitTorus.isCentral.map_mem_center
  have hsel : ∀ (S : Subrepresentation Jac.representation)
      (Pχ : (rationalPoints AL.toGrp →* ℂˣ) → Prop),
      (SmoothRep.pullback eM (SmoothRep.subrepresentation Jac S)).IsAdmissible →
      (∀ ψ, IsGeneralizedEigencharacter (S.toRepresentation.comp
          (splitComponentPointsMap (D.l' ≫ D.p') (b ≫ D.φ.hom))) ψ →
        Pχ (ψ.comp (rationalPoints.map (CommGroupScheme.groupHom (Additive.ofMul f))))) →
      selectedWeightPart
        (I.obj (E.obj (SmoothRep.pullback eM (SmoothRep.subrepresentation Jac S)))).representation
        (rationalPoints.map aL) hι Pχ = ⊤ := by
    intro S Pχ hS hP
    let X := SmoothRep.pullback eM (SmoothRep.subrepresentation Jac S)
    have hadm := hI _ (hE X hS)
    refine selectedWeightPart_eq_top_of_forall _ _ hι Pχ
      (generalizedWeightSpace_iSup_eq_top _ _ hι (I.obj (E.obj X)).isSmooth
        (CentralDecomposition.admissible_centerFinite _ hadm)) fun χ hχ => ?_
    have hχ' := (generalizedWeightSpace_ne_bot_iff (rationalPoints.map aL) χ hι
      (I.obj (E.obj X)).isSmooth).mp hχ
    obtain ⟨ψ, -, hψ, hψχ⟩ := exists_isGeneralizedEigencharacter_of_leviInduction
      D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' hb haL (Additive.ofMul f) hf'
      (E.obj X) (hE X hS) χ hχ'
    have hcomp : (E.obj X).representation.comp (rationalPoints.map b) =
        S.toRepresentation.comp (splitComponentPointsMap (D.l' ≫ D.p') (b ≫ D.φ.hom)) := by
      rw [← leviPointsEquiv_comp_map D.p' D.l' D.hp' D.hl' (b ≫ D.φ.hom)]
      apply MonoidHom.ext
      intro t
      change S.toRepresentation (eM (D.e (rationalPoints.map b t))) = _
      rw [D.e_apply, ← pointMap_comp_apply]
      rfl
    rw [hcomp] at hψ
    rw [← hψχ]
    exact hP ψ hψ
  have := ha'.isAffine
  have h₀ := hsel (unitaryJacquetPart D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ)
    (fun χ => Plancherel.SplitTorus.normalizedRealPart haL.isCentralSplitTorus.1.1 χ = 0) hJ₀
    (fun ψ hψ => by
      obtain ⟨hexp, h0⟩ := normalizedRealPart_eq_zero_of_unitaryJacquetPart
        D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ hψ
      have hopen :=
        ((isNormalizedJacquetExponent_iff_isOpen_ker_and _ _ _ _ _ _ _ _ ρ ψ).mp hexp).1
      change Plancherel.SplitTorus.normalizedRealPart _ _ = 0
      rw [Plancherel.SplitTorus.normalizedRealPart_comp_points haL.isCentralSplitTorus.1.1
        ha'.isCentralSplitTorus.1.1 (Additive.ofMul f) ψ hopen, h0, map_zero])
  have h₁ := hsel (nonunitaryJacquetPart D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ)
    (fun χ => ¬ Plancherel.SplitTorus.normalizedRealPart haL.isCentralSplitTorus.1.1 χ = 0) hJ₁
    (fun ψ hψ => by
      obtain ⟨hexp, hne⟩ := normalizedRealPart_ne_zero_of_nonunitaryJacquetPart
        D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' ha' ρ hψ
      have hopen :=
        ((isNormalizedJacquetExponent_iff_isOpen_ker_and _ _ _ _ _ _ _ _ ρ ψ).mp hexp).1
      have hcone := hρ.parabolic D.p' D.l' (b ≫ D.φ.hom) D.hp' D.hl' ha'
      obtain ⟨presM⟩ := hcone.1
      have hmem := hcone.2 presM _ D.r' D.hr' D.hmul' ψ hexp
      change ¬ Plancherel.SplitTorus.normalizedRealPart _ _ = 0
      rw [Plancherel.SplitTorus.normalizedRealPart_comp_points haL.isCentralSplitTorus.1.1
        ha'.isCentralSplitTorus.1.1 (Additive.ofMul f) ψ hopen]
      exact D.restrictReal_ne_zero_of_mem_nonnegCone (Additive.ofMul f) hf' presQ presM
        hmem hne)
  exact nonempty_selectedWeightPart_equiv (rationalPoints.map aL) hι _
    (I.obj (E.obj J)).isSmooth (SmoothRep.hom (I.map (E.map ι₀)))
    (SmoothRep.hom (I.map (E.map ι₁))) (SmoothRep.hom (I.map (E.map π₀)))
    (SmoothRep.hom (I.map (E.map π₁))) hsumI hinj h₀ h₁

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
