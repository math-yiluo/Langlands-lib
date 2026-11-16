import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent

/-! # Quotienting a sectioned extension without changing its kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SectionedQuotientExtension

variable {S : Scheme.{u}} {U B T Z P D : GroupScheme S}
    (i : U ⟶ B) (p : B ⟶ T) (t : T ⟶ B) (z : Z ⟶ T)
    (qB : B ⟶ P) (qT : T ⟶ D)
    (ht : t ≫ p = 𝟙 T)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hB : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (z ≫ t)) qB)
    (hT : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) qT)

include hp in
private theorem kernel_point {V : Over S} (x : V ⟶ U.X) :
    (x ≫ i.hom.hom) ≫ p.hom.hom = 1 := by
  apply (mem_range_kernelι_iff p _).mp
  rw [hp.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩

include ht hB hT in
/-- The composite to the smaller quotient kills the whole kernel of `qB`. -/
theorem kills_kernel : kernelι qB ≫ (p ≫ qT) = 0 := by
  apply Grp.hom_ext
  change (kernelι qB).hom.hom ≫ (p ≫ qT).hom.hom = 1
  have hk : (kernelι qB).hom.hom ∈
      (SubgroupFunctor.range (z ≫ t)).carrier (kernel qB).X := by
    rw [← hB.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hk
  rw [← hx, Grp.comp_hom_hom, Grp.comp_hom_hom, Category.assoc,
    Category.assoc, ← Category.assoc t.hom.hom p.hom.hom qT.hom.hom,
    ← Grp.comp_hom_hom t p, ht]
  simp only [Grp.id_hom_hom, Category.id_comp]
  rw [← Category.assoc]
  apply (mem_range_kernelι_iff qT _).mp
  rw [hT.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩

/-- The homomorphism on the two supplied quotients. -/
def hom : P ⟶ D :=
  letI := hB.1
  letI := hB.2.1
  letI := hB.2.2.1
  FppfHomDescent.hom qB (p ≫ qT) (kills_kernel p t z qB qT ht hB hT)

@[reassoc]
theorem fac : qB ≫ hom p t z qB qT ht hB hT = p ≫ qT := by
  let := hB.1
  let := hB.2.1
  let := hB.2.2.1
  exact FppfHomDescent.fac qB (p ≫ qT) _

include ht hB hT in
/-- The commuting quotient square uniquely determines the descended map. -/
theorem unique (r : P ⟶ D) (hr : qB ≫ r = p ≫ qT) :
    r = hom p t z qB qT ht hB hT := by
  let := hB.1
  let := hB.2.1
  let := hB.2.2.1
  exact FppfHomDescent.unique qB (p ≫ qT) _ r hr

variable [Mono i.hom.hom]

include ht hp hB in
/-- The original kernel still embeds after quotienting the section factor. -/
theorem inclusion_point_eq_one {V : Over S} (x : V ⟶ U.X)
    (hx : x ≫ (i ≫ qB).hom.hom = 1) : x = 1 := by
  have hxk : x ≫ i.hom.hom ∈
      (SubgroupFunctor.range (z ≫ t)).carrier V := by
    rw [← hB.2.2.2, mem_range_kernelι_iff]
    simpa only [Grp.comp_hom_hom, Category.assoc] using hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxk
  have hz : y ≫ z.hom.hom = 1 := by
    have he := congrArg (fun f : V ⟶ B.X => f ≫ p.hom.hom) hy
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom t p, ht, Grp.id_hom_hom, Category.comp_id,
      kernel_point i p hp x] at he
    exact he
  have hxi : x ≫ i.hom.hom = 1 := by
    rw [← hy, Grp.comp_hom_hom, ← Category.assoc, hz, MonObj.one_comp]
  apply (cancel_mono i.hom.hom).mp
  simpa only [MonObj.one_comp] using hxi

include ht hp hB in
/-- Monicity is on the underlying schemes over the unchanged base. -/
theorem inclusion_mono : Mono (i ≫ qB).hom.hom := by
  constructor
  intro V x y hxy
  have he : (x⁻¹ * y) ≫ (i ≫ qB).hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
  exact inv_mul_eq_one.mp
    (inclusion_point_eq_one i p t z qB ht hp hB (x⁻¹ * y) he)

include ht hp hB hT in
/-- The descended map has exactly the original kernel, on all relative tests. -/
theorem kernel_eq :
    SubgroupFunctor.range (kernelι (hom p t z qB qT ht hB hT)) =
      SubgroupFunctor.range (i ≫ qB) := by
  let r := hom p t z qB qT ht hB hT
  let : Flat qB.hom.hom.left := hB.1
  let : Surjective qB.hom.hom.left := hB.2.1
  let : LocallyOfFinitePresentation qB.hom.hom.left := hB.2.2.1
  let : Mono (i ≫ qB).hom.hom := inclusion_mono i p t z qB ht hp hB
  have hs : qB.hom.hom ≫ r.hom.hom = p.hom.hom ≫ qT.hom.hom := by
    exact congrArg (fun f => f.hom.hom) (fac p t z qB qT ht hB hT)
  apply le_antisymm
  · intro V x hx
    have hxr : x ≫ r.hom.hom = 1 :=
      (mem_range_kernelι_iff r x).mp hx
    let W : Over S :=
      Over.mk (pullback.fst x.left qB.hom.hom.left ≫ V.hom)
    let v : W ⟶ V :=
      Over.homMk (pullback.fst x.left qB.hom.hom.left) rfl
    let b : W ⟶ B.X :=
      Over.homMk (pullback.snd x.left qB.hom.hom.left) (by
        rw [← Over.w qB.hom.hom, ← Category.assoc, ← pullback.condition,
          Category.assoc, Over.w x]
        rfl)
    have hvb : v ≫ x = b ≫ qB.hom.hom :=
      Over.OverMorphism.ext pullback.condition
    have hvf : Flat v.left := by
      change Flat (pullback.fst _ _)
      infer_instance
    have hvs : Surjective v.left := by
      change Surjective (pullback.fst _ _)
      infer_instance
    have hvl : LocallyOfFinitePresentation v.left := by
      change LocallyOfFinitePresentation (pullback.fst _ _)
      infer_instance
    apply SubgroupFunctor.isFppfLocal_range (i ≫ qB) V W v hvf hvs hvl x
    have hbp : b ≫ p.hom.hom ∈ (SubgroupFunctor.range z).carrier W := by
      rw [← hT.2.2.2, mem_range_kernelι_iff]
      rw [Category.assoc, ← hs, ← Category.assoc, ← hvb,
        Category.assoc, hxr, MonObj.comp_one]
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hbp
    let a : W ⟶ B.X := y ≫ (z ≫ t).hom.hom
    have hap : a ≫ p.hom.hom = b ≫ p.hom.hom := by
      dsimp only [a]
      rw [Grp.comp_hom_hom, Category.assoc, Category.assoc,
        ← Grp.comp_hom_hom t p, ht, Grp.id_hom_hom, Category.comp_id, hy]
    have haq : a ≫ qB.hom.hom = 1 := by
      apply (mem_range_kernelι_iff qB a).mp
      rw [hB.2.2.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    have hc : b * a⁻¹ ∈ (SubgroupFunctor.range i).carrier W := by
      rw [← hp.2.2.2, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
        hap, mul_inv_cancel]
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hc
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨u, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hu, MonObj.mul_comp,
      GrpObj.inv_comp, haq, inv_one, mul_one, ← hvb]
  · intro V x hx
    obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [mem_range_kernelι_iff, Grp.comp_hom_hom, Category.assoc, Category.assoc,
      hs, ← Category.assoc, ← Category.assoc, kernel_point i p hp u,
      MonObj.one_comp]

include ht hp hB hT in
/-- Quotienting the section factor gives an fppf quotient with unchanged
kernel group `U`. -/
theorem isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (i ≫ qB))
      (hom p t z qB qT ht hB hT) := by
  let r := hom p t z qB qT ht hB hT
  let : Flat qB.hom.hom.left := hB.1
  let : Surjective qB.hom.hom.left := hB.2.1
  let : LocallyOfFinitePresentation qB.hom.hom.left := hB.2.2.1
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  let : LocallyOfFinitePresentation p.hom.hom.left := hp.2.2.1
  let : Flat qT.hom.hom.left := hT.1
  let : Surjective qT.hom.hom.left := hT.2.1
  let : LocallyOfFinitePresentation qT.hom.hom.left := hT.2.2.1
  have hs : qB.hom.hom.left ≫ r.hom.hom.left =
      p.hom.hom.left ≫ qT.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (fac p t z qB qT ht hB hT)
  let : Flat (qB.hom.hom.left ≫ r.hom.hom.left) := by rw [hs]; infer_instance
  let : Surjective (qB.hom.hom.left ≫ r.hom.hom.left) := by rw [hs]; infer_instance
  let : LocallyOfFinitePresentation (qB.hom.hom.left ≫ r.hom.hom.left) := by
    rw [hs]
    infer_instance
  exact ⟨Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      qB.hom.hom.left r.hom.hom.left,
    Surjective.of_comp qB.hom.hom.left r.hom.hom.left,
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      qB.hom.hom.left r.hom.hom.left,
    kernel_eq i p t z qB qT ht hp hB hT⟩

include ht hp hB hT in
/-- When the quotient target is separated, the unchanged kernel embeds as a
closed subgroup. -/
theorem inclusion_isClosedSubgroup [IsSeparated D.X.hom] :
    IsClosedSubgroup (i ≫ qB) := by
  let r := hom p t z qB qT ht hB hT
  let : Mono (i ≫ qB).hom.hom := inclusion_mono i p t z qB ht hp hB
  let hi : (SubgroupFunctor.range (i ≫ qB)).IsRepresentedBy (i ≫ qB) :=
    ⟨inferInstance, rfl⟩
  let hk : (SubgroupFunctor.range (i ≫ qB)).IsRepresentedBy (kernelι r) :=
    ⟨inferInstance, kernel_eq i p t z qB qT ht hp hB hT⟩
  let e : U ≅ kernel r := hi.isoOfIsRepresentedBy hk
  have he : e.hom ≫ kernelι r = i ≫ qB :=
    hi.isoOfIsRepresentedBy_hom_comp hk
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso e.hom.hom.hom.left := (Over.forget S).map_isIso e.hom.hom.hom
  change IsClosedImmersion (i ≫ qB).hom.hom.left
  rw [← he]
  change IsClosedImmersion (e.hom.hom.hom.left ≫ (kernelι r).hom.hom.left)
  infer_instance

end Langlands.GroupScheme.SectionedQuotientExtension
