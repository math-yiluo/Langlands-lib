import Langlands.Representation.Plancherel.ParabolicIntertwiningReduction
import Langlands.Representation.Plancherel.ParabolicIntertwiningCharacterDecay
import Langlands.Representation.Plancherel.ParabolicLeviModerateGrowth

/-! # The conditional intertwining theorem from growth, squared modulus and character decay -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Plancherel

universe u uV uW

open Aubert.General Induction StandardIntertwining

/-- **Squared-modulus input.** For two parabolic root presentations with a common Levi and their
actual unipotent radicals, the moduli of the two radicals multiply to the square of the modulus
of their intersection on the actual Levi points. -/
def ParabolicSquaredModulusInput : Prop :=
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
      (M P P' U U' : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
      (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
      (a : A.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P')
      (_r : ParabolicRootPresentation p l a) (_r' : ParabolicRootPresentation p' l' a)
      (_hLevi : l ≫ p = l' ≫ p')
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n'),
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
        [MeasurableSpace U'pt] [BorelSpace U'pt]
        [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)],
        SquaredModulusCompatibility h hU h' hU'

/-- **Character-decay input.** Over the data of `ConditionalParabolicIntertwiningStatement` up to
a compact open subgroup `K` with `G(F) = Ppt K`, there is a closed representation `ρ₀` of `G`
such that on the host regions `C R` the weights `δ^{1/2} χ` at Levi components decay along
`Ū(F) ∩ U'(F)` faster than any power of the height (`ParabolicOppositeCharacterDecay`). -/
def ParabolicCharacterDecayInput : Prop :=
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
      (r : ParabolicRootPresentation p l a) (_r' : ParabolicRootPresentation p' l' a)
      (_hLevi : l ≫ p = l' ≫ p')
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
      (_hQ : (Dynamic.parabolic
        (CommGroupScheme.groupHom (-_r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
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
        let Mpt := parabolicLeviPointSubgroup p l
        let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt) (hU : IsClosed (Upt : Set (rationalPoints G)))
          (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
          (_hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G)),
          ∃ (N : ℕ) (ρ₀ : MatrixRepresentation G (Fin (N + 1))),
            letI : Nonempty (Fin (N + 1)) := ⟨0⟩
            IsClosedSubgroup ρ₀ ∧ ParabolicOppositeCharacterDecay r (U'pt := U'pt) h hU K ρ₀ C

/-- **The remaining inputs from growth, squared modulus and character decay.** -/
theorem conditionalParabolicIntertwiningInputs_of_characterDecay
    (hgrowth : RationalFiniteLengthModerateGrowthStatement.{u, uV})
    (hsq : ParabolicSquaredModulusInput.{u})
    (hdecay : ParabolicCharacterDecayInput.{u}) :
    ConditionalParabolicIntertwiningInputs.{u, uV} := by
  intro F _ _ _ _ G hG _ _ _ A M P P' Q U U' V _ _ p l p' l' a n n' q v r r' hLevi hn hn' hQ hv
    _ B C Ppt P'pt Mpt Upt U'pt h hU h' hU' hP hP' K hK hPK hP'K hr hr' ν hν hM
    _ _ _ _ _ _ qν μU' μI _ _ _ _ _ _ hqν π hadm hfin
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨N, ρ₀, hρ₀, hchar⟩ := hdecay F G hG A M P P' Q U U' V p l p' l' a n n' q v r r'
    hLevi hn hn' hQ hv h hU K hK hPK
  have hsq' : SquaredModulusCompatibility h hU h' hU' :=
    hsq F G hG A M P P' U U' p l p' l' a n n' r r' hLevi hn hn' h hU h' hU'
  have : Nonempty (Fin (N + 1)) := ⟨0⟩
  have hcone := parabolicOppositeConeDecay_of_characterDecay r hn rfl rfl h hU K hK ρ₀ hρ₀ C hchar
  have hgr := parabolicLevi_exists_coefficientGrowth r hgrowth ρ₀ hρ₀ π hadm hfin
  obtain ⟨R, hfull, hdom⟩ := exists_region_convergence_domination_of_coneDecay r r' hLevi hn hn'
    rfl rfl rfl h hU h' hU' hP K hK hPK hr qν μU' μI hqν hsq' ρ₀ hρ₀ C hcone π hadm hgr
  exact ⟨hsq', R, hfull, hdom⟩

/-- **The conditional intertwining theorem from growth, squared modulus and character decay.**
Together with `conditionalParabolicIntertwiningStatement_of_inputs`, the three named inputs give
the exact host proposition. -/
theorem conditionalParabolicIntertwiningStatement_of_characterDecay
    (hgrowth : RationalFiniteLengthModerateGrowthStatement.{u, uV})
    (hsq : ParabolicSquaredModulusInput.{u})
    (hdecay : ParabolicCharacterDecayInput.{u}) :
    ConditionalParabolicIntertwiningStatement.{u, uV, uW} :=
  conditionalParabolicIntertwiningStatement_of_inputs
    (conditionalParabolicIntertwiningInputs_of_characterDecay hgrowth hsq hdecay)

end Langlands.Plancherel
