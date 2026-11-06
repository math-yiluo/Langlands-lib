import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.Representation.Exponents.NormalizedIwahoriEigenCoefficient

/-! # Point-specific Jacquet contraction bases from a simultaneous standard basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- One compatible component, chosen before every strict element and every
open subgroup, supplies point-specific cofinal Jacquet contractions. -/
def HasStandardPointwiseIwahoriBasis (J : Set (characterLattice S)) : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
    IsCompatibleStandardSplitComponent i ν J A q ∧
      ∀ g ∈ standardComponentCAstrict i ν J q,
        Langlands.Jacquet.HasIwahoriContractionBasisAt
          (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
          (standardOppositeUnipotentPoints i ν J) g

/-- All strict elements of the same compatible component work throughout the
inherited basis. No existence of a strict element is required for this step. -/
theorem SimultaneousStandardBasisAt.hasStandardPointwiseIwahoriBasis
    {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    HasStandardPointwiseIwahoriBasis i ν J := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨B, hB, hBJ⟩ := hBasis
  obtain ⟨hLevi, A, q, hA, hmembers⟩ := hBJ J hJ
  refine ⟨A, q, hA, ?_⟩
  rintro g ⟨x, hx, rfl⟩
  have hgM := hA.map_mem_standardLeviPoints i ν x
  have hgCA : rationalPoints.map (q ≫ i) x ∈ standardComponentCA i q :=
    ⟨x, hx.1, rfl⟩
  have hgplus : rationalPoints.map (q ≫ i) x ∈
      standardComponentCAplus i ν J q :=
    ⟨x, ⟨hx.1, fun α hα => (hx.2 α hα).le⟩, rfl⟩
  have hgstrict : rationalPoints.map (q ≫ i) x ∈
      standardComponentCAstrict i ν J q := ⟨x, hx, rfl⟩
  intro L
  obtain ⟨K, hK, hKL⟩ := hLevi.exists_intersection_le L
  have hopen := (hB.1 K hK).2.2.1
  refine ⟨⟨K, hopen⟩, (hB.1 K hK).2.2.2, hKL, ?_⟩
  exact isIwahoriContraction_of_contractionAndCofinality hopen
    (hmembers K hK).1 (hmembers K hK).2 hgM hgCA hgplus hgstrict

/-- A supplied standard cocharacter makes the fixed-element conclusion
nonvacuous. The element is chosen before every open subgroup of the Levi. -/
theorem SimultaneousStandardBasisAt.exists_iwahoriContractionBasisAt
    (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {zeta : cocharacterLattice S} (hzeta : IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∃ g : rationalPoints G,
      Langlands.Jacquet.HasIwahoriContractionBasisAt
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardOppositeUnipotentPoints i ν J) g := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨A, q, hA, hpoints⟩ := hBasis.hasStandardPointwiseIwahoriBasis i ν hJ
  exact ⟨hA.strictElement i ν hi hzeta,
    hpoints _ (hA.strictElement_spec i ν hi hzeta).2.2.2⟩

end Langlands.BruhatTits.SpecialCompact
