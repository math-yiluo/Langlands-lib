import Langlands.GroupScheme.Absolute.RegularCocharacterBaseChange
import Langlands.GroupScheme.Absolute.RegularCocharacterParabolic
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Absolute.RankOneSolvableProof

/-! # Borel subgroups from regular cocharacters

The three clauses of `RegularCocharacterBorelStatement`, assembled from the conditional lemmas of
`RegularCocharacterMaximal`, `RegularCocharacterParabolic` and `RegularCocharacterBaseChange`.
`isBorelSubgroup_of_isRepresentedBy_parabolic` and `regularCocharacterBorelStatement_of_inputs`
take structure statements as hypotheses. The solvability lemmas use only Library proofs. The
last two theorems take only relative-root negation or only root-datum existence, respectively. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Clause 1, conditional on structure inputs.** Let `G` be connected reductive over a field,
`j : T ⟶ G` a maximal torus with `T` split, `ν` a regular cocharacter of `T` and `i : B ⟶ G` a
closed subgroup representing `P(ν ≫ j)`. If `B` is solvable, then `i` is a Borel subgroup. -/
theorem isBorelSubgroup_of_isRepresentedBy_parabolic (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) (hNeg : RelativeRootNegationStatement.{u})
    (hobs : RankOneSolvableObstructionStatement.{u}) (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (ν : cocharacterLattice T) (i : B ⟶ G) (hic : IsClosedSubgroup i)
    (hrep : haveI := hG.isAffineHom
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (hsol : IsSolvableGroupScheme B) : IsBorelSubgroup i := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have hneg := neg_mem_roots_of_relativeRootNegation hNeg hG hT j hj
  -- The torus factors through `B`.
  have hjP : SubgroupFunctor.range j ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) :=
    (range_le_centralizer_groupHom_comp j ν).trans (Dynamic.centralizer_le_parabolic _)
  obtain ⟨fT, hfT⟩ : ∃ fT : T.toGrp ⟶ B, fT ≫ i = j := ⟨_, hrep.liftOfLE_comp j hjP⟩
  refine ⟨hic, (hSm k G _ B i).1 hrep, ((hCo k G _ B i).2 inferInstance).1 hrep, hsol, ?_⟩
  intro B' i' f hi'c hsm hco hsol' hf
  have hj' : (fT ≫ f) ≫ i' = j := by rw [Category.assoc, hf, hfT]
  exact isIso_of_comp_eq_of_isRepresentedBy_parabolic hLie hSm hEq hT j ν hneg i hic hrep i' f
    hi'c (hobs k G hG T j hT hj B' i' (fT ≫ f) hi'c hsm hco hsol' hj') hf

/-- For a split maximal torus `j` of a connected reductive group and a regular cocharacter `ν`,
the dynamic centralizer of `ν ≫ j` is the image of `T`, by the Library proofs
`genericCentralizer` and `maximalTorusCentralizer`. -/
theorem centralizer_comp_eq_range_of_isRegular (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom
      IsRegularCocharacter j ν) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j) = SubgroupFunctor.range j := by
  have := hG.isAffineHom
  rw [genericCentralizer k G hG T j (hj.isMaximalSplitTorus hT) ν hν,
    maximalTorusCentralizer k G hG T j hj]

/-- **Solvability input for clause 1.** Let `G` be connected reductive over a field,
`j : T ⟶ G` a maximal torus with `T` split, `ν` a regular cocharacter and `i : B ⟶ G`
representing `P(ν ≫ j)`. Then `B` is solvable: `Z(ν ≫ j)` is the image of `T`
(`centralizer_comp_eq_range_of_isRegular`), and
`isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_le_range` applies. -/
theorem isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom
      IsRegularCocharacter j ν) (i : B ⟶ G)
    (hrep : haveI := hG.isAffineHom
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i) :
    IsSolvableGroupScheme B := by
  have := hG.isAffineHom
  have := hG.smooth
  exact isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_le_range _
    (centralizer_comp_eq_range_of_isRegular hG hT j hj ν hν).le hrep

/-- **`RegularCocharacterBorelStatement`, conditional on structure inputs.** The hypotheses are
the published statements listed below, and `hsolv`: over every field, a closed subgroup
representing `P(ν ≫ j)` for a regular cocharacter `ν` of a split maximal torus `j` of a connected
reductive group is solvable. -/
theorem regularCocharacterBorelStatement_of_inputs (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) (hNeg : RelativeRootNegationStatement.{u})
    (hobs : RankOneSolvableObstructionStatement.{u}) (hBC : BorelConjugacyStatement.{u})
    (hTC : MaximalTorusConjugacyStatement.{u})
    (hFE : ConnectedReductiveFieldExtensionStatement.{u})
    (hMT : MaximalTorusBaseChangeStatement.{u})
    (hsolv : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus j →
        haveI := hG.isAffineHom
        ∀ ν : cocharacterLattice T, IsRegularCocharacter j ν →
          ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsClosedSubgroup i →
            (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i →
              IsSolvableGroupScheme B) :
    RegularCocharacterBorelStatement.{u} := by
  have h1 : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus j →
        haveI := hG.isAffineHom
        ∀ ν : cocharacterLattice T, IsRegularCocharacter j ν →
          ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsClosedSubgroup i →
            (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i →
              IsBorelSubgroup i :=
    fun k _ G hG T j hT hj ν hν B i hic hrep =>
      isBorelSubgroup_of_isRepresentedBy_parabolic hLie hSm hCo hEq hNeg hobs hG hT j hj ν i hic
        hrep (hsolv k G hG T j hT hj ν hν B i hic hrep)
  intro k _ G hG T j hT hj
  exact ⟨h1 k G hG T j hT hj,
    regularCocharacterBorel_parabolic_eq_iff hLie hSm hCo hEq hG j hT,
    fun B i f hB hf => exists_isRegular_isRepresentedBy_of_isBorelSubgroup hLie hSm hCo hNeg hobs
      hBC hTC hFE hMT (fun K _ _ => h1 K) hG hT j hj i f hB hf⟩

/-- **`RegularCocharacterBorelStatement` from relative-root negation.** The Library
proofs `dynamicLie`, `dynamicSmooth`, `dynamicConnected`, `lieSubgroupEquality`,
`rankOneSolvableObstruction`, `connectedReductiveFieldExtensionStatement`, `borelConjugacy`,
`maximalTorusConjugacy` and `maximalTorusBaseChange` are used directly, and solvability of the
parabolic comes from `isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular`. -/
theorem regularCocharacterBorelStatement_of_relativeRootNegation
    (hNeg : RelativeRootNegationStatement.{u}) : RegularCocharacterBorelStatement.{u} :=
  regularCocharacterBorelStatement_of_inputs dynamicLie dynamicSmooth dynamicConnected
    lieSubgroupEquality hNeg rankOneSolvableObstruction borelConjugacy maximalTorusConjugacy
    connectedReductiveFieldExtensionStatement maximalTorusBaseChange
    fun _ _ _ hG _ j hT hj ν hν _ i _ hrep =>
      isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular hG hT j hj ν hν i hrep

/-- **`RegularCocharacterBorelStatement` from root-datum existence.** `RootDatumExistenceStatement`
implies `RelativeRootNegationStatement` by the Library reduction
`relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus`, whose other two inputs
are the Library proofs `connectedReductiveFieldExtensionStatement` and `maximalTorusBaseChange`. -/
theorem regularCocharacterBorelStatement_of_rootDatumExistence
    (hRD : RootDatumExistenceStatement.{u}) : RegularCocharacterBorelStatement.{u} :=
  regularCocharacterBorelStatement_of_relativeRootNegation
    (relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus hRD
      connectedReductiveFieldExtensionStatement maximalTorusBaseChange)

end Langlands.GroupScheme
