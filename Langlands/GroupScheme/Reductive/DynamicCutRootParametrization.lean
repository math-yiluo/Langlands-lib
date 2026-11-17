import Langlands.GroupScheme.Reductive.LocalRootGroupDynamicCut
import Langlands.GroupScheme.Reductive.RelativeRootGroupFibre
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism

/-! # Supplied root coordinates identify dynamic root groups over arbitrary rings -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The canonical dynamic inclusion is a closed subgroup over every base ring. -/
theorem isClosedSubgroup_incl : IsClosedSubgroup (incl i mu nu) := by
  have : IsClosedImmersion (jU i mu nu).hom.hom.left :=
    Corepresented.isClosedSubgroup_unipotentHom (unipCochar i mu nu)
  have : IsClosedImmersion (jZ i mu).hom.hom.left :=
    Corepresented.isClosedSubgroup_centralizerHom (centCochar i mu)
  change IsClosedImmersion (incl i mu nu).hom.hom.left
  dsimp only [incl, Grp.comp_hom_hom, Over.comp_left]
  infer_instance

/-- The canonical inclusion represents the intersection of the two actual
ambient dynamic subgroup functors over every base ring. -/
theorem isRepresentedBy_dynamicCut_incl :
    (dynamicCut i mu nu).IsRepresentedBy (incl i mu nu) := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · have : IsClosedImmersion (incl i mu nu).hom.hom.left := isClosedSubgroup_incl i mu nu
    exact Over.mono_of_mono_left _
  · rintro T g ⟨y, rfl⟩
    change y ≫ (incl i mu nu).hom.hom ∈ (dynamicCut i mu nu).carrier T
    have hy : y ≫ (jU i mu nu).hom.hom ∈
        (Dynamic.unipotent (unipCochar i mu nu)).carrier T := by
      rw [← (Corepresented.isRepresentedBy_unipotentHom _).2]
      exact ⟨y, rfl⟩
    have hz : y ≫ (jU i mu nu).hom.hom ≫ (jZ i mu).hom.hom ∈
        (Dynamic.centralizer (centCochar i mu)).carrier T := by
      rw [← (Corepresented.isRepresentedBy_centralizerHom _).2]
      exact ⟨y ≫ (jU i mu nu).hom.hom, rfl⟩
    have hc := Dynamic.centralizer_le_comap (centCochar i mu)
      (AffineCoordinates.groupSchemeIso G).hom T hz
    have hu := Dynamic.unipotent_le_comap (unipCochar i mu nu)
      (jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom) T hy
    simp only [SubgroupFunctor.mem_comap] at hc hu
    have hcchar : centCochar i mu ≫ (AffineCoordinates.groupSchemeIso G).hom =
        CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i := by
      simp only [centCochar_eq, modelTorus, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have huchar : unipCochar i mu nu ≫ (jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom) =
        CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ i := by
      rw [unipCochar, Category.assoc, ← Category.assoc (torusZ i mu), torusZ_comp]
      simp only [modelTorus, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hcchar] at hc
    rw [huchar] at hu
    constructor
    · change y ≫ (incl i mu nu).hom.hom ∈ (Dynamic.centralizer
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i)).carrier T
      simpa only [incl, Grp.comp_hom_hom, Category.assoc] using hc
    · change y ≫ (incl i mu nu).hom.hom ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ i)).carrier T
      simpa only [incl, Grp.comp_hom_hom, Category.assoc] using hu
  · intro T g hg
    obtain ⟨z, hz⟩ := exists_centralizer_point i mu hg.1
    have hUz := mem_unipotent_of i mu nu hg.2 hz
    obtain ⟨y, hy⟩ : ∃ y, y ≫ (jU i mu nu).hom.hom = z := by
      rw [← SubgroupFunctor.mem_range, (Corepresented.isRepresentedBy_unipotentHom _).2]
      exact hUz
    refine ⟨y, ?_⟩
    change y ≫ (incl i mu nu).hom.hom = g
    rw [incl, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, hy,
      ← Category.assoc, hz, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

variable (a : I → ℤ) (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
  (had : ∑ j, a j * nu j = d)
  {v : Ga R ⟶ G} (hv : IsRootParametrization i a v)

/-- A supplied root map factors through the dynamic root group. -/
def rootToDynamic : Ga R ⟶ Uc i mu nu :=
  hv.represents.restrictionHom (isRepresentedBy_dynamicCut_incl i mu nu) (𝟙 G)
    (by
      rw [SubgroupFunctor.comap_id]
      intro T x hx
      exact ⟨subgroup_le_centralizer i mu a ha0 T hx,
        subgroup_le_unipotent i nu a hd had T hx⟩)

/-- The factorization recovers the given root map. -/
theorem rootToDynamic_comp : rootToDynamic i mu nu a ha0 hd had hv ≫ incl i mu nu = v := by
  unfold rootToDynamic
  rw [SubgroupFunctor.IsRepresentedBy.restrictionHom_comp, Category.comp_id]

/-- The factorization of a supplied root coordinate is an isomorphism on
every field fibre carrying the prescribed equivariant coordinate. -/
theorem isIso_baseChange_rootToDynamic
    (hfib : HasEquivariantFibres i mu nu a)
    (K : Type u) [Field K] [Algebra R K] :
    IsIso ((GroupScheme.baseChange (algebraBaseMap R K)).map
      (rootToDynamic i mu nu a ha0 hd had hv)) := by
  obtain ⟨Φ, hΦ⟩ := hfib K
  have hΦrep := isRootParametrization_fibreRootMap i mu nu K a Φ hΦ ha0 hd had
  have hvK := isRootParametrization_baseChangeRoot K i a v hv
  let e := hvK.represents.isoOfIsRepresentedBy hΦrep.represents
  have he : e.hom ≫ fibreRootMap i mu nu K Φ = baseChangeRoot K v :=
    hvK.represents.isoOfIsRepresentedBy_hom_comp hΦrep.represents
  have heq : (GroupScheme.baseChange (algebraBaseMap R K)).map
        (rootToDynamic i mu nu a ha0 hd had hv) =
      (gaIso (R := R) K).hom ≫ e.hom ≫ Φ.hom := by
    apply SubgroupFunctor.IsRepresentedBy.hom_ext
      ((isRepresentedBy_dynamicCut_incl i mu nu).baseChange (algebraBaseMap R K))
    rw [← Functor.map_comp, rootToDynamic_comp]
    symm
    simp only [Category.assoc]
    rw [← fibreRootMap_eq, he, baseChangeRoot,
      Iso.hom_inv_id_assoc]
  rw [heq]
  infer_instance

variable [Smooth G.X.hom]

/-- Smoothness and the actual field-fibre comparisons identify the supplied
root coordinate with the dynamic root group over the whole base ring. -/
theorem isIso_rootToDynamic (hfib : HasEquivariantFibres i mu nu a) :
    IsIso (rootToDynamic i mu nu a ha0 hd had hv) := by
  have : Smooth (Ga R).X.hom := Corepresented.smooth_groupScheme_iff.mpr inferInstance
  have : Smooth (Uc i mu nu).X.hom := smooth_Uc i mu nu
  have hIso : IsIso (rootToDynamic i mu nu a ha0 hd had hv).hom.hom := by
    apply Langlands.AlgebraicGeometry.isIso_of_residueField_fibres
    intro s
    let K := (Spec (CommRingCat.of R)).residueField s
    let : Algebra R K :=
      (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
    have hb : algebraBaseMap R K = (Spec (CommRingCat.of R)).fromSpecResidueField s :=
      Spec.map_preimage _
    have := isIso_baseChange_rootToDynamic i mu nu a ha0 hd had hv hfib K
    have h : IsIso ((Over.pullback (algebraBaseMap R K)).map
        (rootToDynamic i mu nu a ha0 hd had hv).hom.hom) :=
      inferInstanceAs (IsIso ((Grp.forget _).map
        ((GroupScheme.baseChange (algebraBaseMap R K)).map
          (rootToDynamic i mu nu a ha0 hd had hv))))
    rwa [hb] at h
  have : IsIso (rootToDynamic i mu nu a ha0 hd had hv).hom.hom := hIso
  let e : Ga R ≅ Uc i mu nu :=
    Grp.mkIso' (asIso (rootToDynamic i mu nu a ha0 hd had hv).hom.hom)
  change IsIso e.hom
  infer_instance

include ha0 hd had hv in
/-- A supplied root parametrization identifies its actual root subgroup
with the dynamic intersection over an arbitrary ring. -/
theorem subgroup_eq_dynamicCut_of_parametrization
    (hfib : HasEquivariantFibres i mu nu a) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I a) = dynamicCut i mu nu := by
  have := isIso_rootToDynamic i mu nu a ha0 hd had hv hfib
  rw [← hv.represents.2, ← rootToDynamic_comp i mu nu a ha0 hd had hv]
  exact (SubgroupFunctor.range_iso_comp
    (asIso (rootToDynamic i mu nu a ha0 hd had hv)) (incl i mu nu)).trans
      (isRepresentedBy_dynamicCut_incl i mu nu).2

include ha0 hd had hv in
/-- The supplied root map also represents the actual dynamic intersection
on every test scheme. -/
theorem isRepresentedBy_dynamicCut_of_parametrization
    (hfib : HasEquivariantFibres i mu nu a) :
    (dynamicCut i mu nu).IsRepresentedBy v := by
  rw [← subgroup_eq_dynamicCut_of_parametrization i mu nu a ha0 hd had hv hfib]
  exact hv.represents

end Langlands.GroupScheme.LocalRootGroup
