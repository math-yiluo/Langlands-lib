import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Opposite dynamic parabolics with the exact standard rational-point Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Precomposition by inversion on the multiplicative group. -/
def inverseCocharacter (χ : (Gm S).toGrp ⟶ G) : (Gm S).toGrp ⟶ G :=
  CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ

/-- The inverse cocharacter evaluates to the inverse on every test scheme. -/
theorem comp_inverseCocharacter (χ : (Gm S).toGrp ⟶ G)
    {Q : Over S} (x : Q ⟶ (Gm S).X) :
    x ≫ (inverseCocharacter χ).hom.hom = (x ≫ χ.hom.hom)⁻¹ := by
  simp only [inverseCocharacter, Grp.comp_hom_hom, Gm.powerHom_apply,
    ← Category.assoc, Gm.comp_zsmul_id, zpow_neg_one, GrpObj.inv_comp]

@[simp] theorem inverseCocharacter_inverseCocharacter (χ : (Gm S).toGrp ⟶ G) :
    inverseCocharacter (inverseCocharacter χ) = χ := by
  apply hom_ext_points
  intro Q x
  rw [comp_inverseCocharacter, comp_inverseCocharacter, inv_inv]

/-- A cocharacter and its inverse have the same centralizer on all test schemes. -/
@[simp] theorem centralizer_inverseCocharacter (χ : (Gm S).toGrp ⟶ G) :
    centralizer (inverseCocharacter χ) = centralizer χ := by
  apply SubgroupFunctor.ext
  intro Q
  apply Subgroup.ext
  intro g
  rw [mem_centralizer, mem_centralizer, orbit, orbit, comp_inverseCocharacter]
  let a := snd Q (Gm S).X ≫ χ.hom.hom
  let b := fst Q (Gm S).X ≫ g
  have hc (c d : Q ⊗ (Gm S).X ⟶ G.X) :
      c * d * c⁻¹ = d ↔ Commute c d := mul_inv_eq_iff_eq_mul
  simpa only [inv_inv] using
    (hc a⁻¹ b).trans (Commute.inv_left_iff.trans (hc a b).symm)

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- The identity-test dynamic parabolic of the inverse inducing cocharacter. -/
def oppositeParabolic (ζ : cocharacterLattice T) : Subgroup (RationalPoint k G.X) :=
  (Dynamic.parabolic (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i))).carrier
    (Over.mk (𝟙 _))

/-- The identity-test dynamic contraction group of the inverse inducing cocharacter. -/
def oppositeUnipotent (ζ : cocharacterLattice T) : Subgroup (RationalPoint k G.X) :=
  (Dynamic.unipotent (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i))).carrier
    (Over.mk (𝟙 _))

variable [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- Every standard cocharacter gives an opposite decomposition with the exact
published standard Levi, without an additional decomposition premise. -/
theorem opposite_isSemidirectDecomposition
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    IsSemidirectDecomposition (oppositeParabolic i ζ) (levi i ν I)
      (oppositeUnipotent i ζ) := by
  have := hG.isSeparated
  have hM := ((hStandard k G hG T i hi ν hν (rootSet i ν I)
    (rootSet_subset i ν I)).2 ζ hζ).2.1
  change IsSemidirectDecomposition
    ((Dynamic.parabolic (Dynamic.inverseCocharacter
      (CommGroupScheme.groupHom ζ ≫ i))).carrier (Over.mk (𝟙 _)))
    ((standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)))
    ((Dynamic.unipotent (Dynamic.inverseCocharacter
      (CommGroupScheme.groupHom ζ ≫ i))).carrier (Over.mk (𝟙 _)))
  rw [hM, ← Dynamic.centralizer_inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)]
  exact dynamic_isSemidirectDecomposition _ _

/-- The opposite contraction subgroup is closed in the canonical point topology.
Its closed representative is constructed by the published affine dynamic API. -/
theorem isClosed_oppositeUnipotent [TopologicalSpace k] [T2Space k]
    (ζ : cocharacterLattice T) :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    IsClosed (oppositeUnipotent i ζ : Set (RationalPoint k G.X)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isClosed_rationalPoint_subgroup k
    (Dynamic.unipotent (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)))
    (Dynamic.Affine.unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _)

/-- The local-field instance supplies the coefficient Hausdorff property internally. -/
theorem isClosed_oppositeUnipotent_localField [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ζ : cocharacterLattice T) :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    IsClosed (oppositeUnipotent i ζ : Set (RationalPoint k G.X)) := by
  let : T2Space k := Langlands.BruhatTits.localField_t2Space k
  exact isClosed_oppositeUnipotent i ζ

end Langlands.Aubert.General.RationalPointFamily
