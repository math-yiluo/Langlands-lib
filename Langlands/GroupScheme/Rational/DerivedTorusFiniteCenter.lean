import Langlands.GroupScheme.Rational.DerivedTorusCentralProduct
import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # The full finite centre from an actual derived-torus central complement -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    {e : T ⟶ S} {i : S.toGrp ⟶ G}

namespace DerivedTorusCentralComplement

variable (C : DerivedTorusCentralComplement e i) (d : D ⟶ G)

include C

/-- Only finite type and quasi-compactness of the subgroup are needed for flatness. -/
theorem flat_centralProduct_of_finiteType
    [Smooth G.X.hom] [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    Flat (C.centralProduct d).hom.hom.left := by
  let : Smooth C.torus.X.hom := C.isSplit.smooth
  let : IsAffineHom C.torus.X.hom := C.isSplit.isAffineHom
  let : LocallyOfFiniteType (C.torus.toGrp ⊗ D).X.hom := by
    change LocallyOfFiniteType
      (Limits.pullback.fst C.torus.X.hom D.X.hom ≫ C.torus.X.hom)
    let : LocallyOfFiniteType (Limits.pullback.fst C.torus.X.hom D.X.hom) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    infer_instance
  let : QuasiCompact (C.torus.toGrp ⊗ D).X.hom := by
    change QuasiCompact
      (Limits.pullback.fst C.torus.X.hom D.X.hom ≫ C.torus.X.hom)
    let : QuasiCompact (Limits.pullback.fst C.torus.X.hom D.X.hom) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    infer_instance
  let : Surjective (C.centralProduct d).hom.hom.left :=
    C.surjective_centralProduct d j hsquare hproduct
  exact flat_of_surjective (C.centralProduct d)

/-- The prescribed central multiplication is an epimorphism on all test schemes. -/
theorem epi_subgroupProductMap
    [Smooth G.X.hom] [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    Epi (subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d) := by
  let : Flat (C.centralProduct d).hom.hom.left :=
    C.flat_centralProduct_of_finiteType d j hsquare hproduct
  let : Surjective (C.centralProduct d).hom.hom.left :=
    C.surjective_centralProduct d j hsquare hproduct
  let : Epi (C.centralProduct d).hom.hom.left := Flat.epi_of_flat_of_surjective _
  rw [← C.centralProduct_hom d]
  exact Over.epi_of_epi_left _

/-- For an actual derived subgroup, smoothness and affineness supply the source conditions. -/
theorem epi_subgroupProductMap_of_derived
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    Epi (subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth D.X.hom :=
    hd.smooth_of_connected hG.smooth hG.isAffineHom hG.connectedSpace
  let : IsAffineHom D.X.hom := hd.1.isAffineHom
  exact C.epi_subgroupProductMap d j hsquare hproduct

/-- The full derived centre is the inverse image of the full ambient centre. -/
theorem center_eq_comap_of_derived
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    center D = (center G).comap d := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Epi (subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d) :=
    C.epi_subgroupProductMap_of_derived d hG hd j hsquare hproduct
  exact center_eq_comap_of_epi_subgroupProductMap _ C.isCentral d hd.1

/-- The finite ambient-centre preimage supplies the entire finite derived centre. -/
theorem hasFiniteCenter_of_derived
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) : HasFiniteCenter D := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Epi (subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d) :=
    C.epi_subgroupProductMap_of_derived d hG hd j hsquare hproduct
  obtain ⟨Z, z, hz, hpreimage, hfinite⟩ :=
    derivedCentralIntersectionFiniteness k G D d hG hd
  exact hasFiniteCenter_of_finite_center_preimage_of_epi_subgroupProductMap
    _ C.isCentral d hd.1 Z z hz hpreimage hfinite

/-- Construct an actual finite representative and inclusion of the full derived centre. -/
def finiteDerivedCenter
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) : FiniteCenter D := by
  let h := C.hasFiniteCenter_of_derived d hG hd j hsquare hproduct
  exact ⟨h.choose, h.choose_spec.choose,
    h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2⟩

/-- A supplied complement and product surjectivity make the actual derived subgroup semisimple. -/
theorem isSemisimple_of_derived
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) : IsSemisimple D :=
  ⟨hd.isConnectedReductive hG,
    (C.finiteDerivedCenter d hG hd j hsquare hproduct).hasFiniteCenter⟩

end DerivedTorusCentralComplement

/-- An actual ambient root datum and compatible maximal split tori suffice for
semisimplicity once the actual subgroup/torus multiplication is surjective. -/
theorem IsDerivedSubgroup.isSemisimple_of_rootDatum_product
    [IsAffineHom G.X.hom]
    (d : D ⟶ G) (hd : IsDerivedSubgroup d) (hG : IsConnectedReductive G)
    (e : T ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hj : IsMaximalSplitTorus j)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    {J : Type v} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
    (hP : IsRootDatumOf i P)
    (hproduct : Surjective (subgroupProductMap d i).left) : IsSemisimple D :=
  (derivedTorusCentralComplement e j i d hG hd hi hj hsquare hP).isSemisimple_of_derived
    d hG hd j hsquare hproduct

end Langlands.GroupScheme
