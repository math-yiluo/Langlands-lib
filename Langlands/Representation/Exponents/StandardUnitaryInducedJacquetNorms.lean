import Langlands.Representation.Exponents.LiteralUnitaryInducedJacquetNorms
import Langlands.Representation.Jacquet.StandardComponentScheme
import Langlands.Representation.Jacquet.StandardConstantTermFixedLevel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality

/-! # Finite exponent norms for the original actual standard induced family -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

universe uG uV uA

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]

/-- Equal literal parabolic, Levi and radical subgroups identify normalized
induction on the same source carrier. -/
def normalizedInductionSubgroupCongrEquiv {P M U P' M' U' : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set H))
    (eP : P = P') (eM : M = M') (eU : U = U')
    (σ : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj σ).representation.Equiv
      (((normalizedInductionFunctor h' hU').obj
        (SmoothRep.pullback (RepresentedParabolic.subgroupCongrContinuous eM).symm σ)).representation) := by
  cases eP
  cases eM
  cases eU
  apply normalizedInductionEquivOfEquiv h hU
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun _ => rfl)

/-- Equal radical and Levi subgroups, with the unchanged component map,
identify the normalized Jacquet actions on that component. -/
def normalizedJacquetComponentCongrEquiv
    {N L N' L' : Subgroup H} {A : Type uA} [Group A]
    (hN : IsClosed (N : Set H)) (hLN : L ≤ Subgroup.normalizer N)
    (hN' : IsClosed (N' : Set H)) (hLN' : L' ≤ Subgroup.normalizer N')
    (eN : N = N') (eL : L = L') (j : A →* L) (j' : A →* L')
    (hj : (MulEquiv.subgroupCongr eL).toMonoidHom.comp j = j')
    (ρ : SmoothRep.{0, uG, uV} ℂ H) :
    Representation.Equiv
      ((((normalizedJacquetFunctor N L hN hLN).obj ρ).representation).comp j)
      ((((normalizedJacquetFunctor N' L' hN' hLN').obj ρ).representation).comp j') := by
  cases eN
  cases eL
  have heq : j = j' := by
    ext a
    exact congrArg (fun f : A →* L => (f a : H)) hj
  subst j'
  exact Representation.Equiv.refl _

end Langlands.Aubert.General

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

open RepresentedParabolic

set_option maxHeartbeats 1600000 in
/-- The normalized Jacquet module used by the original standard constant term
has a fixed finite set of exponent norms at a specified component point across
all unitary twists of the original admissible irreducible source. -/
theorem exists_finite_standardUnitaryInducedJacquet_exponentNorms
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible) (t : rationalPoints A.toGrp) :
    ∃ R : Set ℝ≥0, R.Finite ∧
      ∀ ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            (((standardOrdinaryJacquetObject (i := i) (ν := ν)
              (J := RationalPointFamily.rootSet i ν J)
              ((normalizedInductionFunctor
                (isSemidirectDecomposition_standard hG hi hν
                  (RationalPointFamily.rootSet_subset i ν I))
                (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))).obj
                (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)))).representation).comp
                  (standardComponentHom hA)) χ → ‖(χ t : ℂ)‖₊ ∈ R := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨hp, hl, hr, hmul⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter hG hi hν I
  obtain ⟨hq, hlQ, hrQ, hmulQ⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter hG hi hν J
  let p := Standard.parabolicHom i ν (RationalPointFamily.rootSet i ν I)
  let l := Standard.leviToParabolic i ν (RationalPointFamily.rootSet i ν I)
  let r := Standard.unipotentToParabolic i ν (RationalPointFamily.rootSet i ν I)
  let pQ := Standard.parabolicHom i ν (RationalPointFamily.rootSet i ν J)
  let lQ := Standard.leviToParabolic i ν (RationalPointFamily.rootSet i ν J)
  let rQ := Standard.unipotentToParabolic i ν (RationalPointFamily.rootSet i ν J)
  have eP : pointImage p = standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I) :=
    congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_parabolicHom i ν (RationalPointFamily.rootSet i ν I)).2
  have eM : pointImage (l ≫ p) = standardLeviPoints i ν (RationalPointFamily.rootSet i ν I) := by
    dsimp only [l, p]
    rw [Standard.leviToParabolic_comp]
    exact congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν (RationalPointFamily.rootSet i ν I)).2
  have eU : pointImage (r ≫ p) = standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I) :=
    standard_unipotent_pointImage i ν I
  have eMQ : pointImage (lQ ≫ pQ) =
      standardLeviPoints i ν (RationalPointFamily.rootSet i ν J) := by
    dsimp only [lQ, pQ]
    rw [Standard.leviToParabolic_comp]
    exact congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν (RationalPointFamily.rootSet i ν J)).2
  have eUQ : pointImage (rQ ≫ pQ) =
      standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J) :=
    standard_unipotent_pointImage i ν J
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let c := subgroupCongrContinuous eM
  let e := leviPointsEquiv p l hp hl
  let e₀ := RationalPointFamily.leviRationalPointHomeomorph i ν I
  have he : ∀ m, c (e m) = e₀ m := by
    intro m
    apply Subtype.ext
    change rationalPoints.map (l ≫ p) m =
      rationalPoints.map (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)) m
    dsimp only [l, p]
    rw [Standard.leviToParabolic_comp]
  have he' : ∀ m, e₀ (e.symm m) = c m := fun m => by
    rw [← he, e.apply_symm_apply]
  let τ₁ := SmoothRep.pullback c τ
  let σ := SmoothRep.pullback e τ₁
  have hσadm : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv τ₁.representation e
      (isAdmissible_comp_continuousMulEquiv τ.representation c hτadm)
  have hσirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff τ₁.representation e).mpr
      ((isIrreducible_comp_continuousMulEquiv_iff τ.representation c).mpr hτirr)
  let a := standardComponentSchemeHom (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν J) q
  let R := unitaryInducedJacquetExponentNormSet p l r hp hl hr hmul
    pQ lQ rQ hq hlQ hrQ hmulQ (a := a) σ t
  refine ⟨R, unitaryInducedJacquetExponentNormSet_finite
    p l r hp hl hr hmul pQ lQ rQ hq hlQ hrQ hmulQ hG
      (isSplitComponent_standardComponentSchemeHom hA) σ hσadm
      (SmoothRep.hasFiniteLength_of_isIrreducible hσirr) t, ?_⟩
  intro ψ hψ χ hχ
  let νM := fun z : rationalCharacters (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)) =>
    (rationalNormCharacters _ z).toMul
  let ψ₀ := (unramifiedCharactersHomeomorph e₀ νM).symm ψ
  have hψ₀ : ∀ m, ‖(ψ₀.val m : ℂ)‖ = 1 := fun m => hψ (e₀ m)
  let ψ₁ := unramifiedCharactersHomeomorph e νM ψ₀
  let h := isSemidirectDecomposition_standard hG hi hν
    (RationalPointFamily.rootSet_subset i ν I)
  let hU := isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)
  let ρ := (normalizedInductionFunctor h hU).obj
    (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
  let hrep := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hUrep := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let eSrc : (τ₁.twist ψ₁.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ₁)).representation.Equiv
      (SmoothRep.pullback (subgroupCongrContinuous eM.symm).symm
        (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))).representation := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ τ) ?_
    intro m
    ext y
    change (ψ.val (e₀ (e.symm m)) : ℂ) • τ.representation (c m) y =
      (ψ.val (c m) : ℂ) • τ.representation (c m) y
    rw [he']
  let eInd := (normalizedInductionEquivOfEquiv hrep hUrep eSrc).trans
    (normalizedInductionSubgroupCongrEquiv h hU hrep hUrep eP.symm eM.symm eU.symm _).symm
  let E₁ := literalJacquetInductionComponentTwistEquiv
    p l r hp hl hr hmul pQ lQ rQ hq hlQ hrQ hmulQ a τ₁ ψ₀
  let E₂ := Cohomology.HyperextAbutment.equivComp
    (SmoothRep.equivOfIso ((jacquetFunctor pQ lQ rQ hq hrQ hlQ hmulQ).mapIso
      (SmoothRep.mkIso eInd))) (splitComponentPointsMap (lQ ≫ pQ) a)
  have hj : (MulEquiv.subgroupCongr eMQ).toMonoidHom.comp
      (splitComponentPointsMap (lQ ≫ pQ) a) = standardComponentHom hA := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change rationalPoints.map (lQ ≫ pQ) (rationalPoints.map a x) =
      (standardComponentHom hA x : rationalPoints G)
    have hh := congrArg Subtype.val (leviPointsEquiv_map_standardComponentSchemeHom hA x)
    simpa only [Standard.leviPointsEquiv_val, lQ, pQ,
      Standard.leviToParabolic_comp] using hh
  let E₃ := normalizedJacquetComponentCongrEquiv
    (isClosed_pointImage_comp pQ rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
    (pointImage_le_normalizer pQ lQ rQ hrQ)
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    eUQ eMQ (splitComponentPointsMap (lQ ≫ pQ) a) (standardComponentHom hA) hj ρ
  let E₄ := Cohomology.HyperextAbutment.equivComp
    (standardNormalizedJacquetOrdinaryEquiv (i := i) (ν := ν)
      (J := RationalPointFamily.rootSet i ν J) ρ) (standardComponentHom hA)
  have hχ₀ := (isGeneralizedEigencharacter_iff_of_equiv
    (((E₁.trans E₂).trans E₃).trans E₄) χ).mpr hχ
  exact ⟨ψ₀, hψ₀, χ, hχ₀, rfl⟩

end Langlands.HarishChandraSchwartz
