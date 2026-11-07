import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCommonTorus
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! The actual dynamic Levi projection preserves a closed adapted orbit stabilizer. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometric

universe u

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : P ⟶ G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (w : rationalPoints G)

local instance orbitProjectionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))
local notation "S" => SubgroupFunctor.carrier (SubgroupFunctor.range p) T₀
local notation "Q" => SubgroupFunctor.carrier (Dynamic.parabolic χ) T₀
local notation "L" => SubgroupFunctor.carrier (Dynamic.centralizer χ) T₀
local notation "d" => Aubert.General.dynamic_isSemidirectDecomposition χ T₀

omit [IsAffineHom G.X.hom] in
private theorem mem_conjugateRange_iff (x : rationalPoints G) :
    x ∈ (SubgroupFunctor.range (p ≫ (G.innerIso w).hom)).carrier T₀ ↔
      w⁻¹ * x * w ∈ S := by
  change x ∈ (rationalPoints.map (p ≫ (G.innerIso w).hom)).range ↔ _
  rw [rationalPoints_range_comp_innerIso]
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

/-- A common maximal split torus in the conjugate source parabolic and the
output centralizer places the actual output cocharacter in that parabolic. -/
theorem range_cocharacter_le_conjugateParabolic_of_commonTorus
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (i : A.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (hcentral : SubgroupFunctor.range i ≤ Dynamic.centralizer χ)
    (hsource : SubgroupFunctor.range i ≤
      SubgroupFunctor.range (p ≫ (G.innerIso w).hom)) :
    SubgroupFunctor.range χ ≤ SubgroupFunctor.range (p ≫ (G.innerIso w).hom) := by
  obtain ⟨ξ, hξ⟩ := hi.exists_cocharacter_factor_of_centralizing χ hcentral
  intro X x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hξ, Grp.comp_hom_hom, ← Category.assoc]
  exact hsource X (SubgroupFunctor.mem_range.mpr ⟨t ≫ (CommGroupScheme.groupHom ξ).hom.hom, rfl⟩)

variable (hp : IsParabolicSubgroup p)
  (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range (p ≫ (G.innerIso w).hom))

include hp hχ in
/-- The target limit lies back in the actual full orbit stabilizer. The
geometric hypothesis concerns only containment of the output cocharacter. -/
theorem orbitStabilizer_projection_mem
    (x : orbitStabilizer S Q w) :
    (d).projection (x : Q) ∈ orbitStabilizer S L w := by
  let C := SubgroupFunctor.range (p ≫ (G.innerIso w).hom)
  have hc : IsClosedSubgroup (p ≫ (G.innerIso w).hom) :=
    (hp.comp_iso (G.innerIso w)).isClosedSubgroup
  let : IsClosedImmersion (p ≫ (G.innerIso w).hom).hom.hom.left := hc
  have hrep : C.IsRepresentedBy (p ≫ (G.innerIso w).hom) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hstable : (AutomorphicAction.conjugation χ).IsStable C := by
    intro X t g hg
    rw [AutomorphicAction.conjugation_act]
    have ht : t ≫ χ.hom.hom ∈ C.carrier X :=
      hχ X (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
    exact (C.carrier X).mul_mem ((C.carrier X).mul_mem ht hg) ((C.carrier X).inv_mem ht)
  have hx0 := x.property
  change w⁻¹ * ((x : Q) : rationalPoints G) * (w⁻¹)⁻¹ ∈ S at hx0
  have hx : ((x : Q) : rationalPoints G) ∈ C.carrier T₀ :=
    (mem_conjugateRange_iff p w _).mpr (by simpa only [inv_inv] using hx0)
  have hl := (Dynamic.hasLimit_limit χ (x : Q)).mem_of_isClosedSubgroup_of_isStable
    χ hrep hc hstable hx
  change w⁻¹ * (((d).projection (x : Q) : L) : rationalPoints G) * (w⁻¹)⁻¹ ∈ S
  rw [inv_inv, Aubert.General.dynamic_projection_eq_limitHom]
  exact (mem_conjugateRange_iff p w _).mp hl

/-- The actual target Levi section over the intersection subgroup already
lands in the original orbit stabilizer. -/
theorem orbitStabilizer_section_mem (x : orbitStabilizer S L w) :
    Subgroup.inclusion (d).levi_le (x : L) ∈ orbitStabilizer S Q w :=
  x.property

include hp hχ in
/-- The full stabilizer's image under the actual target projection is
exactly the original source-parabolic intersection with the output Levi. -/
theorem orbitStabilizer_map_projection :
    (orbitStabilizer S Q w).map (d).projection = orbitStabilizer S L w := by
  apply le_antisymm
  · rintro x ⟨q, hq, rfl⟩
    exact orbitStabilizer_projection_mem p χ w hp hχ ⟨q, hq⟩
  · intro x hx
    exact ⟨Subgroup.inclusion (d).levi_le x,
      orbitStabilizer_section_mem p χ w ⟨x, hx⟩, (d).projection_levi x⟩

/-- The literal stages subgroup is the preimage of the intersection in the
output Levi under the original dynamic projection. -/
def rationalOrbitStages : Subgroup Q :=
  (orbitStabilizer S L w).comap (d).projection

@[simp]
theorem orbitStabilizer_comap_dynamicSection :
    (orbitStabilizer S Q w).comap (Subgroup.inclusion (d).levi_le) =
      orbitStabilizer S L w := rfl

@[simp]
theorem rationalOrbitStages_comap_dynamicSection :
    (rationalOrbitStages p χ w).comap (Subgroup.inclusion (d).levi_le) =
      orbitStabilizer S L w := by
  ext x
  change (d).projection (Subgroup.inclusion (d).levi_le x) ∈ orbitStabilizer S L w ↔ _
  have hx : (d).projection (Subgroup.inclusion (d).levi_le x) = x :=
    (d).projection_levi x
  rw [hx]

theorem rationalOrbitStages_section_mem
    (x : (rationalOrbitStages p χ w).comap (Subgroup.inclusion (d).levi_le)) :
    Subgroup.inclusion (d).levi_le (x : L) ∈ orbitStabilizer S Q w := by
  have hx : (x : L) ∈ orbitStabilizer S L w := by
    simpa only [rationalOrbitStages_comap_dynamicSection] using x.property
  exact orbitStabilizer_section_mem p χ w ⟨x, hx⟩

theorem ker_projection_le_rationalOrbitStages :
    (d).projection.ker ≤ rationalOrbitStages p χ w := by
  intro x hx
  change (d).projection x ∈ orbitStabilizer S L w
  rw [show (d).projection x = 1 from hx]
  exact (orbitStabilizer S L w).one_mem

include hp hχ in
/-- The actual full stabilizer lies in the stages subgroup, with no assumed
stabilizer-decomposition or representation comparison conclusion. -/
theorem orbitStabilizer_le_rationalOrbitStages :
    orbitStabilizer S Q w ≤ rationalOrbitStages p χ w := by
  intro x hx
  exact orbitStabilizer_projection_mem p χ w hp hχ ⟨x, hx⟩

end Langlands.Geometric
