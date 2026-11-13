import Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityProof
import Langlands.Representation.LanglandsClassification.OppositeJacquetInductionQuotient
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead
import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.NormalizedTemperedTwistExponent

/-! # The Langlands quotient among the irreducible subquotients (Renard VII.4.2): proof from
second adjointness

The exponent characterization of the Langlands quotient follows from second adjointness
(`LeviSecondAdjointnessStatement`), the proved opposite identity support, the proved
geometric-lemma filtration of the regularity quotient and the real-part separation of its
pieces. The entry theorem `langlandsQuotientExponentCharacterizationFromSecondAdjointness`
proves `LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Classification

universe uG uB uV uW uX uY

variable {G : Type uG} [Group G] {B : Type uB} [Monoid B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
  {ξ : Representation ℂ G X} {ηr : Representation ℂ G Y}

/-- Let `S ⊆ ρ` be a copy of an irreducible `τ` and let `c` be a group-algebra element
killing `ρ / S`. If `ηr` is a quotient of a subrepresentation `ξ` of `ρ` on which `c` acts
nontrivially, then `τ` maps nontrivially to `ηr`. -/
theorem exists_ne_zero_of_quotientKernel_action
    (hτ : τ.IsIrreducible) (S : Subrepresentation ρ) (e : S.toRepresentation.Equiv τ)
    (a : B →* G) (c : MonoidAlgebra ℂ B)
    (hc : c ∈ groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a)
    (incl : ξ.IntertwiningMap ρ) (hincl : Function.Injective incl)
    (κ : ξ.IntertwiningMap ηr) (hκ : Function.Surjective κ)
    (hcηr : Representation.asAlgebraHom (ηr.comp a) c ≠ 0) :
    ∃ j : τ.IntertwiningMap ηr, j ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, Representation.asAlgebraHom (ηr.comp a) c y ≠ 0 := by
    by_contra! h
    exact hcηr (LinearMap.ext h)
  obtain ⟨x, rfl⟩ := hκ y
  set x' := Representation.asAlgebraHom (ξ.comp a) c x with hx'
  have hκx' : κ x' ≠ 0 := by
    rw [hx', Intertwining.algebraAction_natural κ a c x]
    exact hy
  have hinclx' : incl x' ∈ S.toSubmodule := by
    rw [hx', Intertwining.algebraAction_natural incl a c x]
    exact Intertwining.algebraAction_mem_of_quotientKernel S a c hc (incl x)
  let T : Subrepresentation ξ :=
    { toSubmodule := S.toSubmodule.comap incl.toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        change incl (ξ g v) ∈ S.toSubmodule
        rw [incl.isIntertwining]
        exact S.apply_mem_toSubmodule g hv }
  let f₀ : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    { toLinearMap := incl.toLinearMap.restrict (p := T.toSubmodule) (q := S.toSubmodule)
        (fun _ hv => hv)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ incl g (v : X) }
  let f : T.toRepresentation.IntertwiningMap τ := e.toIntertwiningMap.comp f₀
  have hf_inj : Function.Injective f := by
    intro v w hvw
    have h1 : f₀ v = f₀ w := e.injective hvw
    apply Subtype.ext
    exact hincl (congrArg Subtype.val h1)
  let x'' : T.toSubmodule := ⟨x', hinclx'⟩
  have hx''0 : x'' ≠ 0 := by
    intro hz
    apply hκx'
    have h1 : x' = 0 := congrArg Subtype.val hz
    rw [h1, map_zero]
  have hf0 : f ≠ 0 := by
    intro hz
    apply hx''0
    apply hf_inj
    rw [hz, map_zero]
    rfl
  let := hτ
  have hf_surj : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf0
  let E := f.ofBijective ⟨hf_inj, hf_surj⟩
  refine ⟨(κ.comp (Intertwining.subtypeIntertwiner T)).comp E.symm.toIntertwiningMap, ?_⟩
  intro hz
  apply hκx'
  have h := congrArg (fun g : τ.IntertwiningMap ηr => g (E x'')) hz
  change κ ((E.symm (E x'') : T.toSubmodule) : X) = 0 at h
  rw [E.symm_apply_apply] at h
  exact h

/-- A nonzero intertwiner out of a representation on which `a` acts by the scalar
character `ω` makes `ω` a generalized eigencharacter of the target along `a`. -/
theorem isGeneralizedEigencharacter_of_ne_zero_of_scalar
    (a : B →* G) (ω : B →* ℂˣ) (hω : ∀ (t : B) (v : W), τ (a t) v = (ω t : ℂ) • v)
    (j : τ.IntertwiningMap ηr) (hj : j ≠ 0) :
    IsGeneralizedEigencharacter (ηr.comp a) ω := by
  obtain ⟨v, hv⟩ : ∃ v, j v ≠ 0 := by
    by_contra! h
    apply hj
    ext v
    exact h v
  refine isGeneralizedEigencharacter_of_eigenvector (ηr.comp a) ω hv (fun t => ?_)
  change ηr (a t) (j v) = _
  rw [← j.isIntertwining, hω, map_smul]

end Langlands.Classification

namespace Langlands

universe uB uV

/-- If the kernel of a scalar character does not meet the finite action quotient of a
commutative-group representation in a generalized character, the two ideals are
comaximal. -/
theorem sup_characterKernel_eq_top_of_not_isGeneralizedEigencharacter
    {B : Type uB} [CommGroup B] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ B V)
    [Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient ρ)]
    (χ : B →* ℂˣ) (hχ : ¬ IsGeneralizedEigencharacter ρ χ) :
    RingHom.ker (PQKernelCharacters.characterAlgebraHom χ) ⊔
      groupAlgebraKernel ρ (MonoidHom.id B) = ⊤ := by
  by_contra hne
  let chiHat := PQKernelCharacters.characterAlgebraHom χ
  have hsurj : Function.Surjective chiHat := fun z => ⟨algebraMap ℂ _ z, chiHat.commutes z⟩
  have hmax : (RingHom.ker chiHat).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have heq := hmax.eq_of_le hne le_sup_left
  have hle : groupAlgebraKernel ρ (MonoidHom.id B) ≤ RingHom.ker chiHat :=
    heq ▸ le_sup_right
  let ψ : PQFiniteActionRegularity.actionQuotient ρ →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ _ chiHat (fun c hc => RingHom.mem_ker.mp (hle hc))
  apply hχ
  have h := PQFiniteActionRegularity.generalizedCharacter_of_actionQuotient ρ ψ
  convert h using 1
  ext t
  change (χ t : ℂ) = chiHat (MonoidAlgebra.of ℂ B t)
  simp [chiHat, PQKernelCharacters.characterAlgebraHom]

end Langlands

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

set_option backward.isDefEq.respectTransparency false in
/-- For a Langlands triplet `(P, σ, ψ)` and the opposite parabolic `P̄`, no generalized
eigencharacter of the split component on a nonidentity geometric-lemma piece of
`r_{P̄}^G i_P^G(σ ⊗ ψ)` has normalized real part `ℜ(ψ)`. -/
theorem langlandsTripletOppositePiece_realPart_ne
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Pbar Ubar : GroupScheme (Spec (CommRingCat.of k)))
      (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Ubar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
      (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
      (hmulbar : IsIso (subgroupMultiplication lbar rbar)),
      lbar ≫ pbar = l ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) →
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
        haveI := hl.isConnectedReductive.isAffineHom
        letI := RationalPointFamily.splitComponentPointTopology ha
        ∀ z : parabolicDoubleCosets p pbar → rationalPoints G,
          (∀ w, DoubleCoset.mk (pointImage p) (pointImage pbar) (z w) = w) →
          ∀ (E : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage pbar) w
              (identityParabolicDoubleCoset p pbar) →
              GeometricLemmaIntersectionDatum p l r hp hr hl hmul pbar lbar rbar
                hpbar hrbar hlbar hmulbar (z w)),
            ∀ w (h : Geometric.BruhatLT (pointImage p) (pointImage pbar) w
                (identityParabolicDoubleCoset p pbar))
              (χ : rationalPoints A.toGrp →* ℂˣ),
              IsGeneralizedEigencharacter
                  (((E w h).pieceFunctor.obj τ).ρ.comp (rationalPoints.map a)) χ →
                Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠
                  leviUnramifiedRealPart l hl a ha ψ := by
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν R P M N A p l r a hp hl hr hmul ha J f σ ψ
    Q U q lQ rQ hq hlQ hrQ hmulQ hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology ha
  let pres : ParabolicRootPresentation p l a := ⟨⟨T, i, ν, J, f⟩, hTrip.1⟩
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence _ G hG Q M A q lQ a hq hlQ ha
  have hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hOpp
  intro τ z hz E w h χ hEigen hreal
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  set E₀ := E w h
  obtain ⟨A', a', g, ha', hg⟩ := E₀.exists_isSplitComponent_factor ha
  let := leviPointTopology E₀.l' E₀.hl'
  have hJ := arbitraryParabolicJacquetAdmissibility _ M hl.isConnectedReductive
    E₀.P' E₀.M' E₀.N' E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hl' E₀.hr' E₀.hmul' τ hadm
  have hJ' : ((leviJacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj
      τ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj τ).representation
      (leviPointsEquiv E₀.p' E₀.l' E₀.hp' E₀.hl') hJ
  have hz0 : DoubleCoset.mk (pointImage p) (pointImage q) (z w) ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1 := by
    rw [hz w]
    exact h.2
  have hδ := E₀.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero pres
    hLevi hG R ψ hTrip.2.2.2 a' (Additive.ofMul g) hg hz0
  have hxQ : E₀.temperedPieceRealPartOffset ha a' (Additive.ofMul g) ψ χ ∈ presQ.nonnegCone :=
    E₀.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone
      ha ha' (Additive.ofMul g) hg presQ
      (relativeRootNegation _ G hG presQ.data.T presQ.data.i presQ.isCompatible.maximalSplit)
      σ ψ hTrip.2.2.1 hJ' χ hEigen
  have hxP := pres.neg_mem_nonnegCone_of_opposite presQ hG hLevi hpoints hxQ
  have hne := pres.add_ne_zero_of_mem_nonnegCone hxP hδ.1 hδ.2
  apply hne
  dsimp only [leviUnramifiedRealPart] at hreal
  dsimp only [GeometricLemmaIntersectionDatum.temperedPieceRealPartOffset,
    GeometricLemmaIntersectionDatum.unramifiedPieceDisplacement, leviUnramifiedRealPart]
  rw [hreal]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- Renard VII.4.2, remark after (i), assuming second adjointness: an irreducible
subquotient `π` of `i_P^G(σ ⊗ ψ)` is a quotient exactly when `ℜ(ψ)` is the normalized real
part of a normalized exponent of `r_{P̄}^G(π)`. -/
theorem langlandsQuotientExponentCharacterization_of_secondAdjointness
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) :
    LanglandsQuotientExponentCharacterizationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hTrip hLevi hOpp
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology ha
  intro I π hπ hsub
  let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  obtain ⟨adj⟩ := hAdj k G hG P Pbar M U Ubar p l r hp hl hr hmul pbar lbar rbar
    hpbar hlbar hrbar hmulbar hLevi hOpp
  let Jb := leviJacquetFunctor.{u, max u v} pbar lbar rbar hpbar hrbar hlbar hmulbar
  constructor
  · rintro ⟨-, t, ht⟩
    let : Nontrivial π :=
      CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible π.representation hπ
    have ht0 : t ≠ 0 := by
      intro hz
      obtain ⟨x, hx⟩ := exists_ne (0 : π)
      obtain ⟨y, hy⟩ := ht x
      apply hx
      simpa only [hz, Representation.IntertwiningMap.coe_zero, Pi.zero_apply] using hy.symm
    obtain ⟨j, hj⟩ := exists_nonzero_oppositeJacquetMap p l r hp hl hr hmul
      pbar lbar rbar hpbar hlbar hrbar hmulbar adj τ π t ht0
    let ω := normalizedTemperedTwistSplitCharacter hl.isConnectedReductive a ha σ
      hTrip.2.2.1 hTrip.2.1 ψ.val.toMonoidHom
    exact ⟨ω.val, (isNormalizedJacquetExponent_iff_leviEigencharacter pbar lbar rbar
      hpbar hlbar hrbar hmulbar ha π ω.val).mpr
      (Classification.isGeneralizedEigencharacter_of_ne_zero_of_scalar _ ω.val
        ω.property.1 j hj), ω.property.2⟩
  · rintro ⟨χ, hχ, hreal⟩
    have hχ' : IsGeneralizedEigencharacter
        ((Jb.obj π).representation.comp (rationalPoints.map a)) χ :=
      (isNormalizedJacquetExponent_iff_leviEigencharacter pbar lbar rbar
        hpbar hlbar hrbar hmulbar ha π χ).mp hχ
    obtain ⟨m, c₀, z, hz, E, -⟩ :=
      representedGeometricLemma.{u, v} k G hG P M U Pbar M Ubar p l r hp hl hr hmul
        pbar lbar rbar hpbar hlbar hrbar hmulbar
    let z' : parabolicDoubleCosets p pbar → rationalPoints G := fun w => z (c₀.symm w)
    have hz' : ∀ w, DoubleCoset.mk (pointImage p) (pointImage pbar) (z' w) = w :=
      fun w => (hz _).trans (c₀.apply_symm_apply w)
    let E' : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage pbar) w
        (identityParabolicDoubleCoset p pbar) →
        GeometricLemmaIntersectionDatum p l r hp hr hl hmul pbar lbar rbar
          hpbar hrbar hlbar hmulbar (z' w) :=
      fun w _ => E (c₀.symm w)
    obtain ⟨n, cc, s, he⟩ := exists_pqRegularity_pieceFiltration.{u, v} k G hG
      P M U Pbar Ubar p l r hp hl hr hmul pbar lbar rbar hpbar hlbar hrbar hmulbar
      hLevi.symm z' hz' E'
    let pieces := fun j : Fin n => (E' (cc j).val (cc j).property).pieceFunctor
    let e : ∀ j, s.graded j ≅ pieces j := fun j => (he j).some
    have : ∀ j, Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
        (((pieces j).obj τ).ρ.comp (rationalPoints.map a))) := fun j =>
      (E' (cc j).val (cc j).property).finite_actionQuotient_piece_of_irreducible ha τ hirr hadm
    let chiHat := PQKernelCharacters.characterAlgebraHom χ
    have hpiece : ∀ j, RingHom.ker chiHat ⊔
        groupAlgebraKernel ((pieces j).obj τ).ρ (rationalPoints.map a) = ⊤ := fun j =>
      sup_characterKernel_eq_top_of_not_isGeneralizedEigencharacter
        (((pieces j).obj τ).ρ.comp (rationalPoints.map a)) χ (fun hE =>
          langlandsTripletOppositePiece_realPart_ne k G hG T i ν D P M U A p l r a
            hp hl hr hmul ha J f σ ψ Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar
            hLevi hOpp hTrip z' hz' E' (cc j).val (cc j).property χ hE hreal)
    have hinf : RingHom.ker chiHat ⊔
        (⨅ j, groupAlgebraKernel ((pieces j).obj τ).ρ (rationalPoints.map a)) = ⊤ := by
      simpa only [Finset.mem_univ, iInf_pos] using
        (Ideal.sup_iInf_eq_top (s := Finset.univ) (I := RingHom.ker chiHat)
          (J := fun j => groupAlgebraKernel ((pieces j).obj τ).ρ (rationalPoints.map a))
          (fun j _ => hpiece j))
    have htop : RingHom.ker chiHat ⊔
        pqRegularityKernel p l r hp hr hl hmul pbar lbar rbar hpbar hrbar hlbar hmulbar a τ =
          ⊤ :=
      (PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels s τ (rationalPoints.map a)
        pieces e (RingHom.ker chiHat)).mpr hinf
    obtain ⟨x, hx, c, hc, hxc⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
    have hc1 : chiHat c = 1 := by
      have h := congrArg chiHat hxc
      rw [map_add, RingHom.mem_ker.mp hx, zero_add, map_one] at h
      exact h
    obtain ⟨S₁, S₂, ⟨eπ⟩⟩ := hsub
    let incl := SmoothRep.hom (Jb.map (SmoothRep.subtype I S₁))
    have hincl : Function.Injective incl :=
      leviJacquetFunctor_map_injective pbar lbar rbar hpbar hlbar hrbar hmulbar _
        (SmoothRep.subtype_injective I S₁)
    let κ₀ : SmoothRep.subrepresentation I S₁ ⟶ π := SmoothRep.mkQ _ S₂ ≫ eπ.inv
    have hκ₀ : Function.Surjective (SmoothRep.hom κ₀) := by
      have h2 : Function.Surjective (SmoothRep.hom eπ.inv) := fun y =>
        ⟨SmoothRep.hom eπ.hom y, congrArg (fun g => SmoothRep.hom g y) eπ.hom_inv_id⟩
      exact h2.comp (SmoothRep.mkQ_surjective _ S₂)
    let κ := SmoothRep.hom (Jb.map κ₀)
    have hκ : Function.Surjective κ :=
      leviJacquet_map_surjective pbar lbar rbar hpbar hlbar hrbar hmulbar κ₀ hκ₀
    let eS := (oppositeIdentitySupport.{u, v} k G hG P M U Pbar Ubar p l r hp hl hr hmul
      pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp τ).some
    have hcη : Representation.asAlgebraHom
        ((Jb.obj π).representation.comp (rationalPoints.map a)) c ≠ 0 := by
      intro h0
      have hmem : c ∈ groupAlgebraKernel
          ((Jb.obj π).representation.comp (rationalPoints.map a)) (MonoidHom.id _) :=
        (mem_groupAlgebraKernel_iff _ _ c).mpr h0
      have h1 := RingHom.mem_ker.mp
        (PQKernelCharacters.kernel_le_characterKernel _ χ hχ' hmem)
      change chiHat c = 0 at h1
      rw [hc1] at h1
      exact one_ne_zero h1
    obtain ⟨jj, hjj⟩ := Classification.exists_ne_zero_of_quotientKernel_action hirr _ eS
      (rationalPoints.map a) c hc incl hincl κ hκ hcη
    let τ' := SmoothRep.universeLift.{u} τ
    let eτ := SmoothRep.universeLiftEquiv.{u} τ
    let j' := jj.comp eτ.symm.toIntertwiningMap
    have hj' : j' ≠ 0 := by
      intro hz0
      apply hjj
      ext y
      have hy := congrArg (fun g => g (eτ y)) hz0
      change jj (eτ.symm (eτ y)) = 0 at hy
      rw [eτ.symm_apply_apply] at hy
      exact hy
    obtain ⟨t', ht'⟩ := exists_surjective_leviInduction_of_nonzero_jacquetMap.{u, max u v}
      p l r hp hl hr hmul pbar lbar rbar hpbar hlbar hrbar hmulbar adj τ' π hπ j' hj'
    let eI := leviInductionEquivOfEquiv p l r hp hl hr hmul τ τ' eτ
    exact ⟨hπ, t'.comp eI.toIntertwiningMap, ht'.comp eI.surjective⟩

/-- Renard VII.4.2, remark after (i), follows from second adjointness (Renard VI.9.6,
(VI.9.6.1)) at the same universes. -/
theorem langlandsQuotientExponentCharacterizationFromSecondAdjointness :
    LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement.{u, v} :=
  langlandsQuotientExponentCharacterization_of_secondAdjointness

end Langlands.Aubert.General.RepresentedParabolic
