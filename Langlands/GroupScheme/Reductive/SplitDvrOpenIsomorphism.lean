import Langlands.GroupScheme.Reductive.SplitOpenGenericIsomorphism
import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Generically equal reductive open subgroups over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitOpenGenericIsomorphism

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G) [Mono f.hom.hom.left]
    [IsOpenImmersion f.hom.hom.left]
    [hgeneric : IsIso ((baseChange (Spec.algebraMap R K)).map f)]
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)

include hM hi hmax hgeneric

/-- The original map is an isomorphism on the canonical residue-field fibre. -/
theorem closedResidueField_isIso :
    IsIso ((baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).map f) := by
  let k := IsLocalRing.ResidueField R
  let l := AlgebraicClosure k
  let : IsLocalHom (algebraMap R k) :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  let : IsLocalHom (algebraMap R l) := by
    rw [IsScalarTower.algebraMap_eq R k l]
    exact RingHom.isLocalHom_comp _ _
  have hk : algebraBaseMap R l (IsLocalRing.closedPoint l) =
      IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint (algebraMap R l)
  have hl : IsIso ((baseChange (algebraBaseMap R l)).map f) := by
    rw [← closedFieldIso_hom (K := K) hM f I i hi hmax l hk]
    infer_instance
  have hcomp : IsIso ((baseChange (algebraBaseMap k l)).map
      ((baseChange (algebraBaseMap R k)).map f)) := by
    apply (TorusIsomorphismLocus.isIso_comp_baseChange_iff
      (algebraBaseMap R k) (algebraBaseMap k l) f).mp
    rw [splitTorus.algebraBaseMap_scalarTower (R := R) (A := k) (B := l)]
    exact hl
  let := hcomp
  exact TorusExistence.isIso_of_isIso_baseChange l
    ((baseChange (algebraBaseMap R k)).map f)

end Local

section Dvr

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G) [Mono f.hom.hom.left]
    [IsOpenImmersion f.hom.hom.left]
    [hgeneric : IsIso ((baseChange (Spec.algebraMap R K)).map f)]
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)

include hM hi hmax hgeneric

/-- Over a DVR the supplied generic and derived closed-fibre isomorphisms
make the original reductive open-subgroup map an isomorphism. -/
theorem isIso_of_dvr : IsIso f := by
  let : Smooth M.X.hom := hM.smooth
  have hclosed := closedResidueField_isIso (K := K) hM f I i hi hmax
  let := hclosed
  have : IsIso f.hom.hom :=
    Langlands.AlgebraicGeometry.isIso_of_generic_special (K := K) f.hom.hom
      ⟨inferInstanceAs (IsIso ((baseChange (Spec.algebraMap R K)).map f).hom.hom),
        inferInstanceAs
          (IsIso ((baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).map f).hom.hom)⟩
  have : IsIso f.hom.hom.left := inferInstance
  exact TorusIsomorphismLocus.isIso_of_underlying f

/-- The actual isomorphism over the DVR, with its original forward map. -/
def dvrIso : M ≅ G := by
  let := isIso_of_dvr (K := K) hM f I i hi hmax
  exact asIso f

@[simp]
theorem dvrIso_hom : (dvrIso (K := K) hM f I i hi hmax).hom = f := rfl

end Dvr

end Langlands.GroupScheme.SplitOpenGenericIsomorphism
