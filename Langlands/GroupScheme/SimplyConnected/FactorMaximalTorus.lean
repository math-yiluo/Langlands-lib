import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductUniqueness
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.CompatibleNormalTorus

/-! # Split maximal tori in the actual product factors of a prescribed split pair -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (D : SimplyConnectedAlmostSimpleProduct G)

/-- Commutation with a point of one factor is detected by the corresponding
projection of the other point. -/
theorem commute_inclusion_iff (i : D.Index)
    {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ (D.factor i).X) (y : U ⟶ G.X) :
    Commute (x ≫ (D.inclusion i).hom.hom) y ↔
      Commute x (y ≫ (D.projection i).hom.hom) := by
  constructor
  · intro h
    have he := congrArg (fun z => z ≫ (D.projection i).hom.hom) h.eq
    exact (commute_iff_eq _ _).mpr (by
      simpa only [MonObj.mul_comp, D.inclusion_projection_points_self] using he)
  · intro h
    apply (commute_iff_eq _ _).mpr
    apply D.points_ext
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [MonObj.mul_comp, D.inclusion_projection_points_self] using h.eq
    · simp only [MonObj.mul_comp, D.inclusion_projection_points_ne i j hij, one_mul, mul_one]

variable [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)

/-- The actual factor maximal torus has a compatible ambient-torus inclusion
and a split projection from that ambient torus. -/
structure FactorMaximalTorus (i : D.Index) extends CompatibleNormalMaximalTorus (D.inclusion i) t where
  split : IsSplitTorus torus.toGrp
  projection : T.toGrp ⟶ torus.toGrp
  projection_comp : projection ≫ subgroupHom = t ≫ D.projection i
  projection_section : CommGroupScheme.groupHom torusHom ≫ projection = 𝟙 torus.toGrp

include hG hT ht

/-- Construct a split maximal torus of each actual product factor inside the
specified ambient split maximal torus. -/
theorem nonempty_factorMaximalTorus (i : D.Index) :
    Nonempty (D.FactorMaximalTorus t i) := by
  let φ := t ≫ D.projection i ≫ D.inclusion i
  let F := hT.dominantFactorization φ
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
    (F.isSplitSubtorus_closedFactor (D.inclusion i) (D.isClosedSubgroup_inclusion i) hφi).2
  have hsclosed : IsClosedSubgroup s := (F.isSplitSubtorus_closedFactor t ht.2.1 hφT).2
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
    refine ⟨F.isSplitSubtorus.1.isTorus, hjclosed, ?_⟩
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
    split := F.isSplitSubtorus.1
    projection := F.factor
    projection_comp := hp
    projection_section := hsection }⟩

/-- The chosen actual compatible split maximal torus of a product factor. -/
def factorMaximalTorus (i : D.Index) : D.FactorMaximalTorus t i :=
  Classical.choice (D.nonempty_factorMaximalTorus hG t hT ht i)

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
