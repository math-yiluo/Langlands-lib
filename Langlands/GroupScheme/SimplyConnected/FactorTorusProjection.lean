import Langlands.GroupScheme.SimplyConnected.FactorMaximalTorus
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.SplitOfDomination

/-! # Factor torus projections defined over the original field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace TorusImage

/-- An actual closed torus image, retaining its dominant factor map over the
original field, without requiring the source torus to split there. -/
structure DominantFactorization {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (φ : T.toGrp ⟶ G) where
  image : CommGroupScheme (Spec (CommRingCat.of k))
  factor : T.toGrp ⟶ image.toGrp
  inclusion : image.toGrp ⟶ G
  isTorus : IsTorus image.toGrp
  isClosedSubgroup : IsClosedSubgroup inclusion
  factor_comp : factor ≫ inclusion = φ
  dominant : IsSchemeTheoreticallyDominant factor.hom.hom.left

namespace DominantFactorization

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G B : GroupScheme (Spec (CommRingCat.of k))} {φ : T.toGrp ⟶ G}
  (F : DominantFactorization φ)

/-- Dominance extends closed-subgroup containment to the entire actual image. -/
theorem range_le_iff (b : B ⟶ G) (hb : IsClosedSubgroup b) :
    SubgroupFunctor.range φ ≤ SubgroupFunctor.range b ↔
      SubgroupFunctor.range F.inclusion ≤ SubgroupFunctor.range b := by
  let : IsSchemeTheoreticallyDominant F.factor.hom.hom.left := F.dominant
  simpa only [F.factor_comp] using
    (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      F.factor F.inclusion b hb)

/-- Factor the actual torus image through a containing closed subgroup. -/
def closedFactor (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) : F.image.toGrp ⟶ B := by
  let : IsClosedImmersion b.hom.hom.left := hb
  let hr : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨Over.mono_of_mono_left _, rfl⟩
  exact hr.factorHom F.inclusion ((F.range_le_iff b hb).mp hφ)

theorem closedFactor_comp (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) :
    F.closedFactor b hb hφ ≫ b = F.inclusion := by
  unfold closedFactor
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

theorem closedFactor_isClosedSubgroup (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) :
    IsClosedSubgroup (F.closedFactor b hb hφ) := by
  apply IsClosedSubgroup.of_comp hb
  rw [F.closedFactor_comp]
  exact F.isClosedSubgroup

end DominantFactorization
end TorusImage

/-- The actual schematic image supplies the torus factorization over the
original field, even when that torus is not split over this field. -/
def IsTorus.dominantFactorization {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hT : IsTorus T.toGrp) (φ : T.toGrp ⟶ G) : TorusImage.DominantFactorization φ := by
  let : QuasiCompact T.toGrp.X.hom := hT.quasiCompact
  have : QuasiCompact (φ.hom.hom.left ≫ G.X.hom) := by
    simpa only [Over.w φ.hom.hom] using (inferInstance : QuasiCompact T.toGrp.X.hom)
  let : QuasiCompact φ.hom.hom.left := QuasiCompact.of_comp φ.hom.hom.left G.X.hom
  have hI := hT.isTorus_schematicImage φ
  let I : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image φ with comm := hI.isCommMonObj }
  exact {
    image := I
    factor := SchematicImage.projection φ
    inclusion := SchematicImage.inclusion φ
    isTorus := hI
    isClosedSubgroup := inferInstanceAs
      (IsClosedImmersion (SchematicImage.inclusion φ).hom.hom.left)
    factor_comp := SchematicImage.projection_inclusion φ
    dominant := inferInstance }

namespace SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G)
  (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)

/-- An actual compatible maximal torus and a dominant projection onto it,
both defined over the original field. -/
structure FactorTorusProjection (i : D.Index) extends CompatibleNormalMaximalTorus (D.inclusion i) t where
  projection : T.toGrp ⟶ torus.toGrp
  projection_comp : projection ≫ subgroupHom = t ≫ D.projection i
  projection_section : CommGroupScheme.groupHom torusHom ≫ projection = 𝟙 torus.toGrp
  dominant : IsSchemeTheoreticallyDominant projection.hom.hom.left

include hG ht

/-- Construct a maximal torus over the original field of each actual product factor inside the
specified ambient maximal torus. -/
theorem nonempty_factorTorusProjection (i : D.Index) :
    Nonempty (D.FactorTorusProjection t i) := by
  let φ := t ≫ D.projection i ≫ D.inclusion i
  let F := ht.1.dominantFactorization φ
  have hself : torusCentralizer t = SubgroupFunctor.range t :=
    maximalTorusCentralizer k G hG T t ht
  have hφT : SubgroupFunctor.range φ ≤ SubgroupFunctor.range t := by
    rw [← hself]
    intro U x hx
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V a y
    have hc := (Commute.all (a ≫ z) y).map
      ((yonedaGrp.map (t ≫ D.projection i)).app (op V)).hom
    change Commute ((a ≫ z) ≫ (t ≫ D.projection i).hom.hom)
      (y ≫ (t ≫ D.projection i).hom.hom) at hc
    have hproj : Commute ((a ≫ z) ≫ (t ≫ D.projection i).hom.hom)
        ((y ≫ t.hom.hom) ≫ (D.projection i).hom.hom) := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hc
    have hprod := (D.commute_inclusion_iff i
      ((a ≫ z) ≫ (t ≫ D.projection i).hom.hom) (y ≫ t.hom.hom)).mpr hproj
    simpa only [φ, Grp.comp_hom_hom, Category.assoc] using hprod
  have hφi : SubgroupFunctor.range φ ≤ SubgroupFunctor.range (D.inclusion i) := by
    intro U x hx
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨z ≫ (t ≫ D.projection i).hom.hom, by
      simp only [φ, Grp.comp_hom_hom, Category.assoc]⟩
  let s := F.closedFactor t ht.2.1 hφT
  let j := F.closedFactor (D.inclusion i) (D.isClosedSubgroup_inclusion i) hφi
  have hs : s ≫ t = F.inclusion := F.closedFactor_comp t ht.2.1 hφT
  have hj : j ≫ D.inclusion i = F.inclusion :=
    F.closedFactor_comp (D.inclusion i) (D.isClosedSubgroup_inclusion i) hφi
  have hjclosed : IsClosedSubgroup j :=
    F.closedFactor_isClosedSubgroup (D.inclusion i) (D.isClosedSubgroup_inclusion i) hφi
  have hsclosed : IsClosedSubgroup s := F.closedFactor_isClosedSubgroup t ht.2.1 hφT
  let : IsClosedImmersion (D.inclusion i).hom.hom.left := D.isClosedSubgroup_inclusion i
  let : Mono (D.inclusion i).hom.hom := Over.mono_of_mono_left _
  let : Mono (D.inclusion i) := by
    exact (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono (D.inclusion i).hom.hom))
  have hp : F.factor ≫ j = t ≫ D.projection i := by
    apply (cancel_mono (D.inclusion i)).mp
    rw [Category.assoc, hj, F.factor_comp]
    rfl
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono j := (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono j.hom.hom))
  have hsection : s ≫ F.factor = 𝟙 F.image.toGrp := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hp, ← Category.assoc, hs, ← hj, Category.assoc,
      D.inclusion_projection, Category.comp_id, Category.id_comp]
  have hcent : torusCentralizer (T := F.image) j ≤ SubgroupFunctor.range j := by
    intro U x hx
    have hxt : x ≫ (D.inclusion i).hom.hom ∈ (torusCentralizer t).carrier U := by
      intro V a y
      have hc := hx V a (y ≫ F.factor.hom.hom)
      have hyp : (y ≫ F.factor.hom.hom) ≫ j.hom.hom =
          (y ≫ t.hom.hom) ≫ (D.projection i).hom.hom := by
        simpa only [Grp.comp_hom_hom, Category.assoc] using
          congrArg (fun f => y ≫ f.hom.hom) hp
      have hproj : Commute (a ≫ x) ((y ≫ t.hom.hom) ≫ (D.projection i).hom.hom) :=
        hyp ▸ hc
      have hprod := (D.commute_inclusion_iff i (a ≫ x) (y ≫ t.hom.hom)).mpr hproj
      simpa only [Category.assoc] using hprod
    rw [hself] at hxt
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hxt
    refine SubgroupFunctor.mem_range.mpr ⟨z ≫ F.factor.hom.hom, ?_⟩
    have he := congrArg (fun w => w ≫ (D.projection i).hom.hom) hz
    have he' : (z ≫ t.hom.hom) ≫ (D.projection i).hom.hom = x := by
      simpa only [D.inclusion_projection_points_self] using he
    calc
      _ = z ≫ (F.factor ≫ j).hom.hom := by simp only [Grp.comp_hom_hom, Category.assoc]
      _ = z ≫ (t ≫ D.projection i).hom.hom := congrArg (fun f => z ≫ f.hom.hom) hp
      _ = x := by simpa only [Grp.comp_hom_hom, Category.assoc] using he'
  have hjmax : IsMaximalTorus (T := F.image) j := by
    refine ⟨F.isTorus, hjclosed, ?_⟩
    intro M m f hM hm hfm
    let : IsClosedImmersion m.hom.hom.left := hm
    let : Mono m.hom.hom := Over.mono_of_mono_left _
    let : Mono m := (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono m.hom.hom))
    have hmj : SubgroupFunctor.range m ≤ SubgroupFunctor.range j := by
      apply le_trans ?_ hcent
      intro U x hx
      obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      intro V a y
      have hc := (Commute.all (a ≫ z) (y ≫ f.hom.hom)).map
        ((yonedaGrp.map m).app (op V)).hom
      change Commute ((a ≫ z) ≫ m.hom.hom) ((y ≫ f.hom.hom) ≫ m.hom.hom) at hc
      simpa only [Category.assoc, ← Grp.comp_hom_hom, hfm] using hc
    let hr : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
    let g := hr.factorHom m hmj
    have hgj : g ≫ j = m := hr.factorHom_comp m hmj
    have hfg : f ≫ g = 𝟙 _ := by
      apply (cancel_mono j).mp
      rw [Category.assoc, hgj, hfm, Category.id_comp]
    have hgf : g ≫ f = 𝟙 _ := by
      apply (cancel_mono m).mp
      rw [Category.assoc, hfm, hgj, Category.id_comp]
    exact ⟨⟨g, hfg, hgf⟩⟩
  exact ⟨{
    torus := F.image
    subgroupHom := j
    torusHom := Additive.ofMul s
    isMaximalTorus := hjmax
    isClosedSubgroup := hsclosed
    comp_eq := hs.trans hj.symm
    projection := F.factor
    projection_comp := hp
    projection_section := hsection
    dominant := F.dominant }⟩

/-- Choose the compatible factor torus and its original-field projection. -/
def factorTorusProjection (i : D.Index) : D.FactorTorusProjection t i :=
  Classical.choice (D.nonempty_factorTorusProjection hG t ht i)

end SimplyConnectedAlmostSimpleProduct
end Langlands.GroupScheme
