import Langlands.Representation.Plancherel.ParabolicIntertwiningAssembly
import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement
import Langlands.Representation.Plancherel.ParabolicRadicalUnimodularity
import Langlands.Representation.Plancherel.CompactIntegralSaturation

/-! # Reduction of the conditional intertwining theorem to its remaining inputs -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV uW

open Aubert.General Induction StandardIntertwining

/-- The remaining inputs of `ConditionalParabolicIntertwiningStatement`, over
exactly the same data: for every admissible finite-length inducing
representation, the squared-modulus compatibility of the two actual radicals,
and one threshold `R` such that the actual standard integral converges on the
whole source at every parameter of the region `C R`, with local integrable
domination of the compact integrands on `C R`. -/
def ConditionalParabolicIntertwiningInputs : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
      (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
      (a : A.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P') (q : Q ⟶ G) (v : V ⟶ Q)
      (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
      (_hLevi : l ≫ p = l' ≫ p')
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
      (_hQ : (Dynamic.parabolic
        (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
      (_hv : LeviSubgroup.IsGeometricUnipotentRadical v),
      letI : Mono r.data.i.hom.hom.left :=
        r.isCompatible.maximalSplit.isSplitSubtorus.mono
      letI : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
        let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
        let := r.isCompatible.levi.isClosedSubgroup.mono
        let := r.isCompatible.parabolic.isClosedSubgroup.mono
        have : Mono (a ≫ l ≫ p).hom.hom.left := by
          change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
          infer_instance
        exact mono_of_mono_fac
          (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
      ∀ [Fintype (relativeWeylGroup r.data.i)],
        let B := weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i
        let C := parabolicPointUnramifiedIntertwiningRegion r B n q v
        let Ppt := (SubgroupFunctor.range p).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let P'pt := (SubgroupFunctor.range p').carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let Mpt := parabolicLeviPointSubgroup p l
        let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt) (hU : IsClosed (Upt : Set (rationalPoints G)))
          (h' : IsSemidirectDecomposition P'pt Mpt U'pt)
          (hU' : IsClosed (U'pt : Set (rationalPoints G)))
          (hP : IsClosed (Ppt : Set (rationalPoints G)))
          (hP' : IsClosed (P'pt : Set (rationalPoints G)))
          (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
          (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (hr : Continuous h.projection) (hr' : Continuous h'.projection),
          let ν := parabolicLeviRationalNormCharacters r
          let hν := continuous_parabolicLeviRationalNormCharacters r
          let hM := isClosed_parabolicLeviPointSubgroup r
          ∀ [MeasurableSpace U'pt] [BorelSpace U'pt]
            [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
            [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
            [BorelSpace (QuotientSpace (U := Upt) U'pt)]
            (qν : Measure (QuotientSpace (U := Upt) U'pt))
            (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
            [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
            [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
            (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
            (π : SmoothRep.{0, u, uV} ℂ Mpt),
            π.IsAdmissible → π.HasFiniteLength →
            ∃ (_hsq : SquaredModulusCompatibility h hU h' hU') (R : ℝ),
              (∀ χ : C R, domain h hU U'pt
                (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) ∧
              ∀ (hδ : IsUnimodularModulus Upt hU),
                CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr π U'pt qν (C R)

/-- The conditional intertwining theorem follows from its remaining inputs.
Radical unimodularity, nonemptiness and openness of the region, openness of
the orbit region, compact rationality and representative naturality are
supplied by published results and by `ParabolicIntertwiningAssembly`. -/
theorem conditionalParabolicIntertwiningStatement_of_inputs
    (H : ConditionalParabolicIntertwiningInputs.{u, uV}) :
    ConditionalParabolicIntertwiningStatement.{u, uV, uW} := by
  intro F _ _ _ _ G hG _ _ _ A M P P' Q U U' V _ _ p l p' l' a n n' q v r r' hLevi hn hn' hQ hv
    _ B C Ppt P'pt Mpt Upt U'pt h hU h' hU' hP hP' K hK hPK hP'K hr hr' ν hν hM
    _ _ _ _ _ _ qν μU' μI _ _ _ _ _ _ hqν π hadm hfin
  have Hd := H F G hG A M P P' Q U U' V p l p' l' a n n' q v r r' hLevi hn hn' hQ hv
    h hU h' hU' hP hP' K hK hPK hP'K hr hr' qν μU' μI hqν π hadm hfin
  obtain ⟨hsq, R, hfullC, hdom⟩ := Hd
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hG.isSeparated
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
    let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := r.isCompatible.levi.isClosedSubgroup.mono
    let := r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ l ≫ p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac
      (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
  have hδ : IsUnimodularModulus Upt hU := parabolicRadical_isUnimodular F G hG A M P U p l a n r hn hU
  have hδ' : IsUnimodularModulus U'pt hU' :=
    parabolicRadical_isUnimodular F G hG A M P' U' p' l' a n' r' hn' hU'
  have hCne : (C R).Nonempty :=
    parabolicPointUnramifiedIntertwiningRegion_nonempty r r' hLevi hn hQ hv B
      (weylInducedCharacterForm_nondegenerate _ _ _ _) R
  have hCopen : IsOpen (C R) := isOpen_parabolicPointUnramifiedIntertwiningRegion r B n q v R
  refine ⟨hδ, hδ', hsq, R, ?_⟩
  exact parabolicLevi_intertwiningConclusion_of_dominated r r' hLevi hn hn' rfl rfl rfl
    h hU hδ K hP hK hPK hr h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hsq π hadm hfin (C R)
    ⟨hCne, hCopen, hfullC, compactIntegralLocallyDominatedOn_saturation h hU hδ K hP hK hPK ν hν
      hr π U'pt qν hCopen (hdom hδ)⟩

end Langlands.Plancherel
