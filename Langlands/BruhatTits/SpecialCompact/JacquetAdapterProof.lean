import Langlands.BruhatTits.SpecialCompact.JacquetAdapterStatement
import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.GroupScheme.Rational.StandardCocharacterReduction

/-! # The actual Jacquet adapter, conditional on the retained algebraic prerequisite -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

/-- For a single standard parabolic, the simultaneous basis and one actual
standard cocharacter supply the whole Levi-cofinal Jacquet predicate. -/
theorem SimultaneousStandardBasisAt.hasIwahoriContractionBasis
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {zeta : cocharacterLattice S} (hzeta : IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Langlands.Jacquet.HasIwahoriContractionBasis
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨B, hB, hBJ⟩ := hBasis
  obtain ⟨hLevi, A, q, hA, hmembers⟩ := hBJ J hJ
  let g := hA.strictElement i ν hi hzeta
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hA.strictElement_spec i ν hi hzeta
  intro L
  obtain ⟨K, hK, hKL⟩ := hLevi.exists_intersection_le L
  have hopen := (hB.1 K hK).2.2.1
  refine ⟨⟨K, hopen⟩, (hB.1 K hK).2.2.2, hKL, g, ?_⟩
  exact isIwahoriContraction_of_contractionAndCofinality hopen
    (hmembers K hK).1 (hmembers K hK).2 hgM hgCA hgplus hgstrict

/-- The existing standard-cocharacter statement supplies the only algebraic
existence input needed by the topological adapter. -/
theorem simultaneousBasisJacquetAdapter_of_standardCocharacterStatement
    (hstandard : StandardCocharacterStatement.{u}) :
    SimultaneousBasisJacquetAdapterStatement.{u} := by
  intro F _ _ _ _ G hG S i hi
  have := hG.isAffineHom
  intro ν hν K0 hBasis J hJ
  obtain ⟨zeta, hzeta⟩ := (hstandard F G hG S i hi ν hν J hJ).1
  exact hBasis.hasIwahoriContractionBasis i ν hi hJ hzeta

/-- The relative-root-system statement suffices: no sign-to-dynamic comparison
is used. This theorem retains the root-system statement as an explicit input. -/
theorem simultaneousBasisJacquetAdapter_of_relativeRootSystemStatement
    (hroot : RelativeRootSystemStatement.{u}) :
    SimultaneousBasisJacquetAdapterStatement.{u} := by
  intro F _ _ _ _ G hG S i hi
  have := hG.isAffineHom
  intro ν hν K0 hBasis J hJ
  obtain ⟨zeta, hzeta⟩ :=
    exists_standardCocharacter_of_relativeRootSystemStatement hroot
      F G hG S i hi ν hν J hJ
  exact hBasis.hasIwahoriContractionBasis i ν hi hJ hzeta

end Langlands.BruhatTits.SpecialCompact
