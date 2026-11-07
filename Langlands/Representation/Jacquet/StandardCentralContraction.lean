import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints

/-! # Central strict contraction elements for one actual standard parabolic -/

noncomputable section

universe uF

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type uF} [Field F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- Every point of the compatible split component commutes with the actual
standard Levi subgroup, after applying the specified ambient point map. -/
theorem IsCompatibleStandardSplitComponent.map_commute_standardLeviPoints
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (x : rationalPoints A.toGrp) {m : rationalPoints G}
    (hm : m ∈ standardLeviPoints i ν J) :
    m * rationalPoints.map (q ≫ i) x = rationalPoints.map (q ≫ i) x * m := by
  obtain ⟨_, M, j, a, hj, _, _, ha, hcompat⟩ := hA
  have hc := ha.splitComponentLeviPointsMap_mem_center i ν J j hj x
  have hcomm := congrArg (fun z : standardLeviPoints i ν J => (z : rationalPoints G))
    (Subgroup.mem_center_iff.mp hc ⟨m, hm⟩)
  change m * rationalPoints.map j (rationalPoints.map a x) =
    rationalPoints.map j (rationalPoints.map a x) * m at hcomm
  have hpoint : rationalPoints.map j (rationalPoints.map a x) =
      rationalPoints.map (q ≫ i) x := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : A.toGrp ⟶ G => rationalPoints.map f x) hcompat
  rwa [hpoint] at hcomm

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A component-lattice element, viewed in the standard Levi, is central.
The proof does not need a basis of open subgroups. -/
theorem IsCompatibleStandardSplitComponent.mem_center_of_mem_standardComponentCA
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    {g : rationalPoints G} (hgM : g ∈ standardLeviPoints i ν J)
    (hg : g ∈ standardComponentCA i q) :
    (⟨g, hgM⟩ : standardLeviPoints i ν J) ∈
      Subgroup.center (standardLeviPoints i ν J) := by
  apply Subgroup.mem_center_iff.mpr
  intro m
  apply Subtype.ext
  obtain ⟨x, _, rfl⟩ := hg
  exact hA.map_commute_standardLeviPoints i ν x m.property

/-- The already chosen strict element, packaged in the center of the same
actual standard Levi. This construction precedes the choice of an open subgroup. -/
def IsCompatibleStandardSplitComponent.centralStrictElement
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    Subgroup.center (standardLeviPoints i ν J) :=
  ⟨⟨hA.strictElement i ν hi hzeta, (hA.strictElement_spec i ν hi hzeta).1⟩,
    hA.mem_center_of_mem_standardComponentCA i ν
      (hA.strictElement_spec i ν hi hzeta).1 (hA.strictElement_spec i ν hi hzeta).2.1⟩

@[simp] theorem IsCompatibleStandardSplitComponent.centralStrictElement_val
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    ((hA.centralStrictElement i ν hi hzeta : standardLeviPoints i ν J) : rationalPoints G) =
      hA.strictElement i ν hi hzeta := rfl

/-- The central strict element satisfies the existing Jacquet contraction
predicate for each supplied pointwise standard basis member. -/
theorem IsCompatibleStandardSplitComponent.centralStrictElement_isIwahoriContraction
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (K : OpenSubgroup (rationalPoints G)),
    StandardParabolicBasisMember i ν J q K.toSubgroup →
    Langlands.Jacquet.IsIwahoriContraction K
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardOppositeUnipotentPoints i ν J)
      ((hA.centralStrictElement i ν hi hzeta : standardLeviPoints i ν J) :
        rationalPoints G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro K hBasis
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hA.strictElement_spec i ν hi hzeta
  exact isIwahoriContraction_of_contractionAndCofinality K.isOpen hBasis.1 hBasis.2
    hgM hgCA hgplus hgstrict

end Langlands.BruhatTits.SpecialCompact
