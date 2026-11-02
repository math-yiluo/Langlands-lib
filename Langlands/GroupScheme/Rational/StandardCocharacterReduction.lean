import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.StandardCocharacterStatement

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Local

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))

/-- The three dynamic subgroup functors are constant among the standard
cocharacters for this face. This property includes no existence assertion. -/
def StandardCocharacterDynamicComparison : Prop :=
  ∀ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta →
    ∀ eta : cocharacterLattice T, IsStandardCocharacter i ν J eta →
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
        Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ∧
      Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) =
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)

/-- A pointwise intersection of a constant standard family agrees with each
of its members on every test scheme. -/
theorem StandardCocharacterDynamicComparison.standard_eq_dynamic
    (h : StandardCocharacterDynamicComparison i ν J)
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) :
    standardParabolic i ν J = Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ∧
    standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ∧
    standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) := by
  refine ⟨le_antisymm (standardParabolic_le_dynamicParabolic i ν hzeta) ?_,
    le_antisymm (standardLevi_le_dynamicCentralizer i ν hzeta) ?_,
    le_antisymm (standardUnipotent_le_dynamicUnipotent i ν hzeta) ?_⟩
  · intro U g hg
    rw [mem_standardParabolic]
    intro eta heta
    simpa only [(h zeta hzeta eta heta).1] using hg
  · intro U g hg
    rw [mem_standardLevi]
    intro eta heta
    simpa only [(h zeta hzeta eta heta).2.1] using hg
  · intro U g hg
    rw [mem_standardUnipotent]
    intro eta heta
    simpa only [(h zeta hzeta eta heta).2.2] using hg

/-- Pairwise dynamic comparison is precisely agreement of the choice-free
intersections with every standard cocharacter. -/
theorem standardCocharacterDynamicComparison_iff :
    StandardCocharacterDynamicComparison i ν J ↔
      ∀ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta →
        standardParabolic i ν J = Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ∧
        standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ∧
        standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) := by
  refine ⟨fun h _ hzeta => h.standard_eq_dynamic i ν J hzeta, ?_⟩
  intro h zeta hzeta eta heta
  exact ⟨(h zeta hzeta).1.symm.trans (h eta heta).1,
    (h zeta hzeta).2.1.symm.trans (h eta heta).2.1,
    (h zeta hzeta).2.2.symm.trans (h eta heta).2.2⟩

/-- The relative-root-system hypothesis supplies the negation closure needed
to compare the root signs of any two standard cocharacters. -/
theorem HasRelativeRootSystem.standardCocharacters_haveSameRelativeRootSigns
    [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    {zeta eta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (heta : IsStandardCocharacter i ν J eta) :
    HaveSameRelativeRootSigns i zeta eta :=
  hzeta.haveSameRelativeRootSigns i ν hν
    (fun _ hα => hroot.neg_mem_relativeRoots i hT hα) heta

/-- An explicit sign-to-dynamic comparison, together with the root-system
realization, gives the local comparison needed by the standard intersections. -/
theorem HasRelativeRootSystem.standardCocharacterDynamicComparison
    [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hsign : ∀ zeta eta : cocharacterLattice T,
      HaveSameRelativeRootSigns i zeta eta →
        Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    StandardCocharacterDynamicComparison i ν J := by
  intro zeta hzeta eta heta
  exact hsign zeta eta
    (hroot.standardCocharacters_haveSameRelativeRootSigns i ν J hT hν hzeta heta)

end Local

/-- Existence alone follows from the exact general root-system statement,
independently of any dynamic comparison. -/
theorem exists_standardCocharacter_of_relativeRootSystemStatement
    (hroot : RelativeRootSystemStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν J hJ
  exact (hroot k G hG T i hi).exists_standardCocharacter i ν
    hi.isSplitSubtorus.1 hν J hJ

/-- Conditional assembly of the unchanged exact target. Both structural inputs
are explicit; this theorem does not prove either of them. -/
theorem standardCocharacterStatement_of_relativeRootSystem_of_signs
    (hroot : RelativeRootSystemStatement.{u})
    (hsign : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
      letI := hG.isAffineHom
      ∀ zeta eta : cocharacterLattice T, HaveSameRelativeRootSigns i zeta eta →
        Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    StandardCocharacterStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν J hJ
  have hR := hroot k G hG T i hi
  have hT := hi.isSplitSubtorus.1
  refine ⟨hR.exists_standardCocharacter i ν hT hν J hJ, ?_⟩
  intro zeta hzeta
  exact (hR.standardCocharacterDynamicComparison i ν J hT hν
    (hsign k G hG T i hi)).standard_eq_dynamic i ν J hzeta

end Langlands.GroupScheme
