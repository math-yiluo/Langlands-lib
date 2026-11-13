import Langlands.Representation.LanglandsClassification.OppositeIntertwiningExponentComparison
import Langlands.Representation.Intertwining.ComaximalRestriction

/-! # A nonzero map into an opposite induction comes from the identity piece -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Intertwining

variable {H : Type*} [Group H] {B : Type*} [Monoid B]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {τ : Representation ℂ H W}

/-- If the action kernel of the target is comaximal with the action kernel of the quotient
by a subrepresentation `S`, then a nonzero intertwiner stays nonzero on `S`. -/
theorem comp_subtypeIntertwiner_ne_zero_of_comaximal (S : Subrepresentation ρ)
    (Φ : ρ.IntertwiningMap τ) (a : B →* H)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤)
    (hΦ : Φ ≠ 0) : Φ.comp (subtypeIntertwiner S) ≠ 0 := by
  intro hz
  apply hΦ
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h)
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv : v = Representation.asAlgebraHom (ρ.comp a) x v +
      Representation.asAlgebraHom (ρ.comp a) y v := by
    rw [← LinearMap.add_apply, ← map_add, hxy, map_one, Module.End.one_apply]
  have hyS := algebraAction_mem_of_quotientKernel S a y hy v
  have h0 : Φ (Representation.asAlgebraHom (ρ.comp a) y v) = 0 := by
    have := congrArg (fun f : S.toRepresentation.IntertwiningMap τ => f ⟨_, hyS⟩) hz
    exact this
  change Φ v = 0
  rw [hv, map_add, algebraAction_natural Φ a x v, (mem_groupAlgebraKernel_iff τ a x).mp hx, h0]
  simp

end Langlands.Intertwining

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

set_option backward.isDefEq.respectTransparency false in
/-- The identity piece in Renard VII.4.2 (ii). Let `(P = MN, σ, ψ)` be a Langlands triplet,
let `Q` be an actual parabolic opposite to `P` with the same Levi `M`, and let `ρ` be a
smooth representation of `M(k)` on which the split component acts through a character
`c` with the real part of `ψ`. If some intertwining map `i_P^G(σ ⊗ ψ) → i_Q^G(ρ)` is
nonzero, then some intertwining map `σ ⊗ ψ → ρ` of `M(k)`-representations is nonzero. -/
theorem exists_ne_zero_intertwiningMap_of_oppositeIntertwining :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Q U : GroupScheme (Spec (CommRingCat.of k)))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      lQ ≫ q = l ≫ p →
      pointImage p ⊓ pointImage q = pointImage (l ≫ p) →
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
        ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (c : rationalPoints A.toGrp →* ℂˣ),
          (∀ (t : rationalPoints A.toGrp) (x : ρ),
            ρ.representation (rationalPoints.map a t) x = (c t : ℂ) • x) →
          Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 c =
            leviUnramifiedRealPart l hl a ha ψ →
          ∀ t : ((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.IntertwiningMap
              ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ).representation,
            t ≠ 0 → ∃ F : τ.representation.IntertwiningMap ρ.representation, F ≠ 0 := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M N A p l r a hp hl hr hmul ha J f σ ψ
    Q U q lQ rQ hq hlQ hrQ hmulQ hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology ha
  intro τ ρ c hc hcre t ht
  let pres : ParabolicRootPresentation p l a := ⟨⟨T, i, ν, J, f⟩, hTrip.1⟩
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ a hq hlQ ha
  have hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hOpp
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  -- Frobenius reciprocity for `Q`.
  obtain ⟨e, -⟩ := leviFrobeniusReciprocity.{u, v, max u v} k G hG Q M U q lQ rQ
    hq hlQ hrQ hmulQ ((leviInductionFunctor p l r hp hr hl hmul).obj τ) ρ
  have hΦ : e t ≠ 0 := by
    intro h
    apply ht
    apply e.injective
    rw [h, map_zero]
  -- The identity piece.
  obtain ⟨eS⟩ := oppositeIdentitySupport k G hG P M N Q U p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ hLevi hOpp τ
  let S := (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)).obj τ
  -- The scalar action on `ρ`.
  have hscalar : ∀ b, (ρ.representation.comp (rationalPoints.map a)) b =
      (c b : ℂ) • (1 : Module.End ℂ ρ) := by
    intro b
    apply LinearMap.ext
    intro x
    exact hc b x
  have : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (ρ.representation.comp (rationalPoints.map a))) :=
    CentralActionQuotient.finite_actionQuotient_of_scalar _ (fun b => (c b : ℂ)) hscalar
  -- The nonidentity pieces of the regularity quotient.
  obtain ⟨m, c₀, z, hz, E, -⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U p l r hp hl hr hmul
      q lQ rQ hq hlQ hrQ hmulQ
  let z' : parabolicDoubleCosets p q → rationalPoints G := fun w => z (c₀.symm w)
  have hz' : ∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z' w) = w :=
    fun w => (hz _).trans (c₀.apply_symm_apply w)
  let E' : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
      (identityParabolicDoubleCoset p q) →
      GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ
        hq hrQ hlQ hmulQ (z' w) :=
    fun w _ => E (c₀.symm w)
  obtain ⟨n, cc, s, he⟩ := exists_pqRegularity_pieceFiltration.{u, v} k G hG
    P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hLevi.symm z' hz' E'
  let pieces := fun j : Fin n => (E' (cc j).val (cc j).property).pieceFunctor
  have hsep : ∀ (w : parabolicDoubleCosets p q)
      (hw : Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q))
      (E₀ : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ
        hq hrQ hlQ hmulQ (z' w)),
      groupAlgebraKernel ρ.representation (rationalPoints.map a) ⊔
        groupAlgebraKernel (E₀.pieceFunctor.obj τ).ρ (rationalPoints.map a) = ⊤ := by
    intro w hw E₀
    have : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
        ((E₀.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a))) :=
      E₀.finite_actionQuotient_piece_of_irreducible ha τ hirr hadm
    rw [sup_comm]
    apply (PQFiniteActionRegularity.sup_kernels_eq_top_iff
      ((E₀.pieceFunctor.obj τ).ρ.comp (rationalPoints.map a))
      (ρ.representation.comp (rationalPoints.map a))).mpr
    rw [Set.disjoint_left]
    intro χ hχE hχρ
    have hχc : χ = c :=
      CentralActionQuotient.eq_of_isGeneralizedEigencharacter_of_scalar _ c hscalar χ hχρ
    obtain ⟨A', a', g, ha', hg⟩ := E₀.exists_isSplitComponent_factor ha
    let := leviPointTopology E₀.l' E₀.hl'
    have hJ := arbitraryParabolicJacquetAdmissibility k M hl.isConnectedReductive
      E₀.P' E₀.M' E₀.N' E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hl' E₀.hr' E₀.hmul' τ hadm
    have hJ' : ((leviJacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj
        τ).IsAdmissible :=
      isAdmissible_comp_continuousMulEquiv
        ((jacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj τ).representation
        (leviPointsEquiv E₀.p' E₀.l' E₀.hp' E₀.hl') hJ
    have hz0 : DoubleCoset.mk (pointImage p) (pointImage q) (z' w) ≠
        DoubleCoset.mk (pointImage p) (pointImage q) 1 := by
      rw [hz' w]
      exact hw.2
    have hδ := E₀.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero pres
      hLevi hG D ψ hTrip.2.2.2 a' (Additive.ofMul g) hg hz0
    have hxQ := E₀.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone
      ha ha' (Additive.ofMul g) hg presQ
      (relativeRootNegation k G hG presQ.data.T presQ.data.i presQ.isCompatible.maximalSplit)
      σ ψ hTrip.2.2.1 hJ' χ hχE
    have hxP := pres.neg_mem_nonnegCone_of_opposite presQ hG hLevi hpoints hxQ
    have hne := pres.add_ne_zero_of_mem_nonnegCone hxP hδ.1 hδ.2
    apply hne
    rw [hχc, hcre]
    dsimp only [GeometricLemmaIntersectionDatum.unramifiedPieceDisplacement,
      leviUnramifiedRealPart]
    abel
  have hpiece : ∀ j, groupAlgebraKernel ρ.representation (rationalPoints.map a) ⊔
      groupAlgebraKernel ((pieces j).obj τ).ρ (rationalPoints.map a) = ⊤ :=
    fun j => hsep (cc j).val (cc j).property (E' (cc j).val (cc j).property)
  have hcomax : groupAlgebraKernel ρ.representation (rationalPoints.map a) ⊔
      pqRegularityKernel p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a τ = ⊤ := by
    apply (PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels s τ (rationalPoints.map a)
      pieces (fun j => (he j).some) _).mpr
    simpa only [Finset.mem_univ, iInf_pos] using
      (Ideal.sup_iInf_eq_top (s := Finset.univ)
        (I := groupAlgebraKernel ρ.representation (rationalPoints.map a))
        (J := fun j => groupAlgebraKernel ((pieces j).obj τ).ρ (rationalPoints.map a))
        (fun j _ => hpiece j))
  have hS := Intertwining.comp_subtypeIntertwiner_ne_zero_of_comaximal S (e t)
    (rationalPoints.map a) hcomax hΦ
  refine ⟨((e t).comp (Intertwining.subtypeIntertwiner S)).comp eS.symm.toIntertwiningMap, ?_⟩
  intro hzero
  apply hS
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun F : τ.representation.IntertwiningMap ρ.representation => F (eS x)) hzero
  change ((e t).comp (Intertwining.subtypeIntertwiner S)) (eS.symm (eS x)) = 0 at hx
  rw [eS.symm_apply_apply] at hx
  exact hx

end Langlands.Aubert.General.RepresentedParabolic
