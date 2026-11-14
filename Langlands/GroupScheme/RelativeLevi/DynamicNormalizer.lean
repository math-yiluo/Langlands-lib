import Langlands.GroupScheme.Rational.DynamicLeviConjugacyReduction
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Self-normalization of a complement to a dynamic unipotent subgroup -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicLeviConjugacy

section Base

variable {S : Scheme.{u}} {G P L : GroupScheme S}
    (l : L ⟶ P) (q : P ⟶ L) (hlq : l ≫ q = 𝟙 L)

include hlq in
/-- The retraction identifies all normalizer points with points of the section
when the section is self-normalizing. The inverse is the original section map. -/
def normalizerPointsEquivOfRetraction
    (hN : (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l)
    (T : Over S) : (SubgroupFunctor.range l).normalizer.carrier T ≃* (T ⟶ L.X) where
  toFun g := (g : T ⟶ P.X) ≫ q.hom.hom
  invFun a := ⟨a ≫ l.hom.hom, SubgroupFunctor.le_normalizer _ T ⟨a, rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    have hg : (g : T ⟶ P.X) ∈ (SubgroupFunctor.range l).carrier T := by
      simpa only [hN] using g.2
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hg
    change ((g : T ⟶ P.X) ≫ q.hom.hom) ≫ l.hom.hom = g
    rw [← hy, Category.assoc y l.hom.hom q.hom.hom,
      hom_hom_comp_hom_hom l q hlq, Category.comp_id]
  right_inv a := by
    change (a ≫ l.hom.hom) ≫ q.hom.hom = a
    rw [Category.assoc, hom_hom_comp_hom_hom l q hlq, Category.comp_id]
  map_mul' g h := by
    change ((g : T ⟶ P.X) * (h : T ⟶ P.X)) ≫ q.hom.hom =
      ((g : T ⟶ P.X) ≫ q.hom.hom) * ((h : T ⟶ P.X) ≫ q.hom.hom)
    exact MonObj.mul_comp _ _ _

include hlq in
/-- A normalizing point in the kernel of a retraction centralizes its section. -/
theorem mem_centralizer_of_mem_normalizer_of_retraction
    {T : Over S} {n : T ⟶ P.X}
    (hn : n ∈ (SubgroupFunctor.range l).normalizer.carrier T)
    (hnq : n ≫ q.hom.hom = 1) :
    n ∈ (SubgroupFunctor.range l).centralizer.carrier T := by
  rintro V a x ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := (hn V a (y ≫ l.hom.hom) ⟨y, rfl⟩).1
  change z ≫ l.hom.hom = (a ≫ n) * (y ≫ l.hom.hom) * (a ≫ n)⁻¹ at hz
  have hq : (a ≫ n) ≫ q.hom.hom = 1 := by
    rw [Category.assoc, hnq, MonObj.comp_one]
  have hzy : z = y := by
    have h := congrArg (· ≫ q.hom.hom) hz
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      hom_hom_comp_hom_hom l q hlq, Category.comp_id, hq,
      one_mul, inv_one, mul_one] using h
  rw [hzy] at hz
  exact (mul_inv_eq_iff_eq_mul).mp hz.symm

variable {χ : (Gm S).toGrp ⟶ G} {j : P ⟶ G}
    (hj : (Dynamic.parabolic χ).IsRepresentedBy j)
    (hker : ∀ (T : Over S) (x : T ⟶ P.X),
      x ≫ q.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T)

include hlq hker in
set_option maxHeartbeats 800000 in
/-- A kernel point normalizing the section is trivial once a unipotent point
transports the dynamic cocharacter into that section. -/
theorem eq_one_of_mem_normalizer_of_retraction [IsSeparated G.X.hom]
    {u : Over.mk (𝟙 S) ⟶ G.X}
    (hu : u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)))
    (hμ : χ ≫ (G.innerIso u).hom = (parabolicCocharacter χ hj ≫ q) ≫ l ≫ j)
    {T : Over S} {n : T ⟶ P.X}
    (hn : n ∈ (SubgroupFunctor.range l).normalizer.carrier T)
    (hnq : n ≫ q.hom.hom = 1) : n = 1 := by
  have : Mono j.hom.hom := hj.1
  have hc := mem_centralizer_of_mem_normalizer_of_retraction l q hlq hn hnq
  have hzP : n ∈
      (Dynamic.centralizer ((parabolicCocharacter χ hj ≫ q) ≫ l)).carrier T := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer]
    intro V a t
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      hc V a ((t ≫ (parabolicCocharacter χ hj ≫ q).hom.hom) ≫ l.hom.hom)
        ⟨_, rfl⟩
  have hz := Dynamic.centralizer_le_comap
    ((parabolicCocharacter χ hj ≫ q) ≫ l) j T hzP
  rw [SubgroupFunctor.mem_comap] at hz
  have he : (G.innerIso u).inv.hom.hom ≫ (G.innerIso u).hom.hom.hom = 𝟙 G.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  have hzn : n ≫ j.hom.hom ≫ (G.innerIso u).inv.hom.hom ∈
      (Dynamic.centralizer χ).carrier T := by
    rw [Dynamic.centralizer_eq_comap_of_iso χ (G.innerIso u), hμ,
      SubgroupFunctor.mem_comap]
    simp only [Category.assoc, he, Category.comp_id]
    exact hz
  have hnU : n ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T := (hker T n).1 hnq
  have hcu : G.constantPoint u T ∈ (Dynamic.unipotent χ).carrier T :=
    (Dynamic.unipotent χ).comp_mem _ hu
  have hUn : n ≫ j.hom.hom ≫ (G.innerIso u).inv.hom.hom ∈
      (Dynamic.unipotent χ).carrier T := by
    rw [← Category.assoc n j.hom.hom (G.innerIso u).inv.hom.hom,
      ← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv]
    exact mul_mem (mul_mem (inv_mem hcu) hnU) (inv_mem (inv_mem hcu))
  have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
    (fun _ _ _ _ hl hl' => hl.unique χ hl') hzn hUn
  have hnG : n ≫ j.hom.hom = 1 := by
    have h := congrArg (· ≫ (G.innerIso u).hom.hom.hom) h1
    simpa only [Category.assoc, he, Category.comp_id, MonObj.one_comp] using h
  exact (cancel_mono j.hom.hom).mp (hnG.trans (MonObj.one_comp _).symm)

include hlq hker in
/-- A section whose retraction kernel is the dynamic unipotent subgroup is
self-normalizing, provided the dynamic cocharacter is unipotently conjugate into
the section. This assertion holds on all test schemes over an arbitrary base. -/
theorem normalizer_eq_range_of_retraction [IsSeparated G.X.hom]
    {u : Over.mk (𝟙 S) ⟶ G.X}
    (hu : u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)))
    (hμ : χ ≫ (G.innerIso u).hom = (parabolicCocharacter χ hj ≫ q) ≫ l ≫ j) :
    (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l := by
  refine le_antisymm (fun T g hg => ?_) (SubgroupFunctor.le_normalizer _)
  let a := g ≫ q.hom.hom
  let n := (a ≫ l.hom.hom)⁻¹ * g
  have hn : n ∈ (SubgroupFunctor.range l).normalizer.carrier T :=
    mul_mem (inv_mem (SubgroupFunctor.le_normalizer _ T ⟨a, rfl⟩)) hg
  have hnq : n ≫ q.hom.hom = 1 := by
    simp only [n, a, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      hom_hom_comp_hom_hom l q hlq, Category.comp_id, inv_mul_cancel]
  have h1 := eq_one_of_mem_normalizer_of_retraction l q hlq hj hker hu hμ hn hnq
  change (a ≫ l.hom.hom)⁻¹ * g = 1 at h1
  exact ⟨a, (inv_mul_eq_one.mp h1)⟩

end Base

end DynamicLeviConjugacy

end Langlands.GroupScheme
