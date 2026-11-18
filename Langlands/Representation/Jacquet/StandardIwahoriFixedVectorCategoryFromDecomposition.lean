import Langlands.Representation.Jacquet.StandardIwahoriFixedVectorCategoryFromInputs
import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionAssembly

/-! # Renard VI.10.6 Proposition (i) from the Bernstein decomposition and the criterion -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.CuspidalSupport
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

/-- Renard VI.10.6, the step of the proof of the Proposition: at a compact open subgroup `K`,
contained and normal in `K₀`, with an Iwahori decomposition along every standard parabolic,
two irreducible smooth representations with the same inertial support both have or both lack
nonzero `K`-fixed vectors. Conditional form: the Bernstein decomposition at carrier universe
`max uF uV` (which gives uniqueness of inertial support) and the standard-representative
criterion are explicit premises; VI.5.4 is not used. -/
theorem standardIwahoriBernsteinFixedVectorVisibility_of_decomposition
    (hBernstein : BernsteinDecompositionStatement.{uF, max uF uV})
    (hCrit : StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}) :
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
        (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
        (hν : IsGenericCocharacter i ν)
        (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
        (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
        (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
          ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
        (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
        (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
        (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
          HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
            (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)),
        letI : T2Space F := BruhatTits.localField_t2Space F
        letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
        letI : NonarchimedeanGroup (rationalPoints G) :=
          Plancherel.rationalPoints_nonarchimedeanGroup G
        bernsteinFixedVectorVisibility.{uF, uV} i ν (standardBernsteinFamily i ν hG hi hν) K := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  exact bernsteinFixedVectorVisibility_of_uniqueness_of_necessity i ν
    (standardBernsteinFamily i ν hG hi hν) K hstandard hK hIwahori
    (bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero.{uF, uV} i ν
      (standardBernsteinFamily i ν hG hi hν)
      (hBernstein F G S i ν (standardBernsteinFamily i ν hG hi hν)).2)
    (fun a ha => (hCrit F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal
      hIwahori a).mp ha)

/-- Renard VI.10.6 Proposition (i), conditional form: the VI.7.2 Bernstein decomposition at
carrier universes `uV` and `max uF uV`, and the standard-representative criterion, are
explicit premises. -/
theorem standardIwahoriFixedVectorBlockDecomposition_of_decomposition
    (hBernstein : BernsteinDecompositionStatement.{uF, uV})
    (hBernsteinSat : BernsteinDecompositionStatement.{uF, max uF uV})
    (hCrit : StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}) :
    StandardIwahoriFixedVectorBlockDecompositionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  intro family V
  have hvis := standardIwahoriBernsteinFixedVectorVisibility_of_decomposition.{uF, uV}
    hBernsteinSat hCrit F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  exact ⟨isCoproductOfFixedClasses_of_fixedVectorGenerated i ν family K
      (hBernstein F G S i ν family).1 V,
    fixedVectorGenerated_of_isCoproductOfFixedClasses i ν family K hK hvis V⟩

set_option linter.defProp false in
/-- The reduction of Renard VI.10.6 Proposition (i) to the Bernstein decomposition and the
standard-representative criterion, as a declaration whose type is the implication. -/
def standardIwahoriFixedVectorBlockDecompositionOfDecomposition :
    BernsteinDecompositionStatement.{uF, uV} →
    BernsteinDecompositionStatement.{uF, max uF uV} →
    StandardRepresentativeFixedVectorCriterionStatement.{uF, uV} →
      StandardIwahoriFixedVectorBlockDecompositionStatement.{uF, uV} :=
  standardIwahoriFixedVectorBlockDecomposition_of_decomposition

end Langlands.Jacquet
