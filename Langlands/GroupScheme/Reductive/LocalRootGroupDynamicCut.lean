import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Root subgroups as dynamic intersections over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

/-- The intersection of the centralizer of `mu` and the positive dynamic
subgroup of `nu`, both computed in the ambient group. -/
def dynamicCut : SubgroupFunctor G :=
  Dynamic.centralizer (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu) ≫ i) ⊓
  Dynamic.unipotent (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu) ≫ i)

variable [IsAffineHom G.X.hom]

/-- A point satisfying both dynamic conditions factors through any polynomial
coordinate of the actual dynamic root group. -/
theorem dynamicCut_le_range_rootMap (x : coordU i mu nu)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y') :
    dynamicCut i mu nu ≤ SubgroupFunctor.range (rootMap i mu nu x hx hadd) := by
  intro T g hg
  obtain ⟨z, hz⟩ := exists_centralizer_point i mu hg.1
  have hUz := mem_unipotent_of i mu nu hg.2 hz
  obtain ⟨y, hy⟩ : ∃ y, y ≫ (jU i mu nu).hom.hom = z := by
    rw [← SubgroupFunctor.mem_range, (Corepresented.isRepresentedBy_unipotentHom _).2]
    exact hUz
  rw [SubgroupFunctor.mem_range]
  refine ⟨y ≫ (gaIsoU i mu nu x hx hadd).inv.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, rootMap, Iso.inv_hom_id_assoc, incl,
    Grp.comp_hom_hom, ← Category.assoc, hy, Grp.comp_hom_hom, ← Category.assoc,
    hz, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

variable [Smooth G.X.hom] [IsLocalRing R] [DecidableEq I]

/-- Fixed-root equivariant field fibres identify the actual root functor with
the dynamic intersection, including over rings with nilpotents. -/
theorem subgroup_eq_dynamicCut_of_fibres (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I a) = dynamicCut i mu nu := by
  obtain ⟨x, hxd, hx⟩ := exists_coordinate_of_flat i mu nu hd fun K _ _ => by
    obtain ⟨Φ, hΦ⟩ := hfib K
    exact ⟨_, Φ, hΦ, by
      rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, had]⟩
  have hadd : ∀ (T : Over (Spec (CommRingCat.of R))) (y y' : T ⟶ (Uc i mu nu).X),
      coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' :=
    fun _ => coordX_mul_of_homogeneous i mu nu hd hxd hx.2
  have ha := isHomogeneous_of_equivariantFibres i mu nu hd hxd hx had hfib
  have hequiv := rootMap_equivariant_of_isHomogeneous i mu nu x hx hadd ha
  have hrep := isRepresentedBy_rootMap i mu nu x hx hadd a hequiv ha0 hd had
  apply le_antisymm
  · intro T g hg
    exact ⟨subgroup_le_centralizer i mu a ha0 T hg,
      subgroup_le_unipotent i nu a hd had T hg⟩
  · rw [← hrep.2]
    exact dynamicCut_le_range_rootMap i mu nu x hx hadd

/-- A supplied actual root parametrization also represents the dynamic
intersection under the fixed-root fibre hypotheses. -/
theorem isRepresentedBy_dynamicCut_of_fibres (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a)
    {v : Ga R ⟶ G} (hv : IsRootParametrization i a v) :
    (dynamicCut i mu nu).IsRepresentedBy v := by
  rw [← subgroup_eq_dynamicCut_of_fibres i mu nu a ha0 hd had hfib]
  exact hv.represents

/-- The points of a supplied root parametrization are precisely the ambient
points satisfying both dynamic conditions, on every test scheme. -/
def dynamicCutPointsEquiv (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a)
    {v : Ga R ⟶ G} (hv : IsRootParametrization i a v)
    (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (Ga R).X) ≃* (dynamicCut i mu nu).carrier T :=
  (isRepresentedBy_dynamicCut_of_fibres i mu nu a ha0 hd had hfib hv).pointsEquiv T

/-- The comparison sends a point to its image under the given root map. -/
theorem dynamicCutPointsEquiv_apply_coe (a : I → ℤ)
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a)
    {v : Ga R ⟶ G} (hv : IsRootParametrization i a v)
    (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ (Ga R).X) :
    (dynamicCutPointsEquiv i mu nu a ha0 hd had hfib hv T y : T ⟶ G.X) =
      y ≫ v.hom.hom :=
  rfl

end Langlands.GroupScheme.LocalRootGroup
