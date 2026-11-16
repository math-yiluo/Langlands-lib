import Langlands.GroupScheme.AutomorphicActionSubgroupQuotient
import Langlands.GroupScheme.RelativeParabolicQuotientProof
import Langlands.GroupScheme.HomogeneousQuotientFactorization
import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.RepresentabilityTransfer

/-! # Actual adjoint-action Borel stabilizers over a ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G A B : GroupScheme S}

/-- Central points normalize every subgroup functor on every refinement. -/
theorem center_le_normalizer (F : SubgroupFunctor G) : center G ≤ F.normalizer := by
  apply le_trans _ (centralizer_le_normalizer F)
  intro T x hx V t g _
  exact hx V t g

variable (i : B ⟶ G) [Mono i.hom.hom] (q : G ⟶ A)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (F : SubgroupFunctor A) (hF : F.IsFppfLocal)
    (hpre : F.comap q = range i)
    {Q : Over S} (projection : G.X ⟶ Q)
    (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ projection = h ≫ projection ↔ g⁻¹ * h ∈ (range i).carrier T)
    (r : A.X ⟶ Q) (hr : q.hom.hom ≫ r = projection)

omit [Mono i.hom.hom] in
include hF hpre hfib hr in
/-- The subgroup is the identity fibre of any compatible descended coset map. -/
theorem mem_iff_descendedCoset_eq {T : Over S} (x : T ⟶ A.X) :
    x ∈ F.carrier T ↔ x ≫ r = toUnit T ≫ HomogeneousQuotient.identityCoset G projection := by
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let p : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let g : V ⟶ G.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have hp : p ≫ x = g ≫ q.hom.hom := Over.OverMorphism.ext pullback.condition
  have hpf : Flat p.left := by change Flat (pullback.fst _ _); infer_instance
  have hps : Surjective p.left := by change Surjective (pullback.fst _ _); infer_instance
  have hpl : LocallyOfFinitePresentation p.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  let : Flat p.left := hpf
  let : Surjective p.left := hps
  let : LocallyOfFinitePresentation p.left := hpl
  let : Epi p := Over.epi_of_epi_left p
  have hm : p ≫ x ∈ F.carrier V ↔ g ∈ (range i).carrier V := by
    rw [hp]
    change g ∈ (F.comap q).carrier V ↔ _
    rw [hpre]
  have he : g ≫ projection = toUnit V ≫ HomogeneousQuotient.identityCoset G projection ↔
      g ∈ (range i).carrier V := by
    rw [HomogeneousQuotient.identityCoset, ← Category.assoc, MonObj.comp_one]
    simpa only [inv_one, one_mul] using (eq_comm.trans (hfib V 1 g))
  have hc : p ≫ (x ≫ r) = g ≫ projection := by
    rw [← Category.assoc, hp, Category.assoc, hr]
  constructor
  · intro hx
    apply (cancel_epi p).mp
    rw [hc, comp_toUnit_assoc]
    exact he.mpr (hm.mp (F.comp_mem p hx))
  · intro hx
    apply hF T V p hpf hps hpl x
    apply hm.mpr
    apply he.mp
    rw [← hc, hx, comp_toUnit_assoc]

omit [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left] in
/-- A represented subgroup with the specified full inverse image has an actual
cartesian quotient square. -/
theorem isPullback_of_comap_range
    {P : GroupScheme S} (j : P ⟶ A) [Mono j.hom.hom]
    (qB : B ⟶ P) (hsquare : i ≫ q = qB ≫ j)
    (hpre : (range j).comap q = range i) :
    IsPullback i.hom.hom qB.hom.hom q.hom.hom j.hom.hom := by
  have hs : i.hom.hom ≫ q.hom.hom = qB.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsquare
  have hmem (c : PullbackCone q.hom.hom j.hom.hom) :
      c.fst ∈ (range i).carrier c.pt := by
    rw [← hpre]
    change c.fst ≫ q.hom.hom ∈ (range j).carrier c.pt
    exact mem_range.mpr ⟨c.snd, c.condition.symm⟩
  let liftPoint := fun (c : PullbackCone q.hom.hom j.hom.hom) =>
    Classical.choose (mem_range.mp (hmem c))
  have hfst (c : PullbackCone q.hom.hom j.hom.hom) :
      liftPoint c ≫ i.hom.hom = c.fst :=
    Classical.choose_spec (mem_range.mp (hmem c))
  refine ⟨⟨hs⟩, ⟨PullbackCone.IsLimit.mk _ liftPoint hfst ?_ ?_⟩⟩
  · intro c
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, ← hs, ← Category.assoc, hfst, c.condition]
  · intro c m hm _
    apply (cancel_mono i.hom.hom).mp
    exact hm.trans (hfst c).symm

/-- The exact subgroup quotient and its represented inclusion. -/
structure QuotientSubgroupData where
  group : GroupScheme S
  inclusion : group ⟶ A
  projection : B ⟶ group
  represents : F.IsRepresentedBy inclusion
  square : i ≫ q = projection ≫ inclusion
  isPullback : IsPullback i.hom.hom projection.hom.hom q.hom.hom inclusion.hom.hom
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.hom.hom.left
  closed : IsClosedSubgroup inclusion

omit [Mono i.hom.hom] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left] in
/-- The quotient projection has exactly the ambient kernel restricted to the subgroup. -/
theorem QuotientSubgroupData.kernel_eq (d : QuotientSubgroupData i q F) :
    range (kernelι d.projection) = (range (kernelι q)).comap i := by
  let : Mono d.inclusion.hom.hom := d.represents.1
  have hs : i.hom.hom ≫ q.hom.hom =
      d.projection.hom.hom ≫ d.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) d.square
  ext T x
  rw [mem_range_kernelι_iff, mem_comap, mem_range_kernelι_iff]
  constructor
  · intro hx
    rw [Category.assoc, hs, ← Category.assoc, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono d.inclusion.hom.hom).mp
    rw [MonObj.one_comp, Category.assoc, ← hs, ← Category.assoc, hx]

include hF hpre hfib hr in
/-- Construct the actual quotient subgroup from a compatible map to a separated coset space. -/
def quotientSubgroupDataOfCosetMap [IsSeparated Q.hom] :
    QuotientSubgroupData i q F := by
  let c := toUnit A.X ≫ HomogeneousQuotient.identityCoset G projection
  let jZ : equalizer r c ⟶ A.X := equalizer.ι r c
  have hmem (T : Over S) (x : T ⟶ A.X) :
      x ∈ F.carrier T ↔ ∃ y : T ⟶ equalizer r c, y ≫ jZ = x := by
    rw [mem_iff_descendedCoset_eq i q F hF hpre projection hfib r hr x]
    constructor
    · intro hx
      exact ⟨equalizer.lift x (by simpa only [c, comp_toUnit_assoc] using hx),
        equalizer.lift_ι _ _⟩
    · rintro ⟨y, rfl⟩
      change (y ≫ equalizer.ι r c) ≫ r = _
      rw [Category.assoc, equalizer.condition, ← Category.assoc]
      simp only [c, comp_toUnit_assoc]
  let P := F.representingGroupScheme jZ hmem
  let j : P ⟶ A := F.representingHom jZ hmem
  have hj : F.IsRepresentedBy j := F.isRepresentedBy_representingHom jZ hmem
  let : Mono j.hom.hom := hj.1
  have hp : (range j).comap q = range i := by rw [hj.2, hpre]
  have hle : range (i ≫ q) ≤ F := by
    intro T x hx
    obtain ⟨b, rfl⟩ := mem_range.mp hx
    have hb : b ≫ i.hom.hom ∈ (range i).carrier T := mem_range.mpr ⟨b, rfl⟩
    rw [← hpre] at hb
    exact hb
  let qB : B ⟶ P := hj.factorHom (i ≫ q) hle
  have hs : i ≫ q = qB ≫ j := (hj.factorHom_comp (i ≫ q) hle).symm
  have hpb := isPullback_of_comap_range i q j qB hs hp
  have hpb' : IsPullback i.hom.hom.left qB.hom.hom.left q.hom.hom.left
      j.hom.hom.left := hpb.map (Over.forget S)
  refine ⟨P, j, qB, hj, hs, hpb, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hpb' inferInstance
  · exact MorphismProperty.of_isPullback (P := @Surjective) hpb' inferInstance
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb'
      inferInstance
  · change IsClosedImmersion j.hom.hom.left
    rw [F.representingHom_hom jZ hmem]
    exact AlgebraicGeometry.isClosedImmersion_equalizer_ι_left r c

end SubgroupFunctor

section Borel

variable {R : Type u} [CommRing R]
    {G B A : GroupScheme (Spec (CommRingCat.of R))}
    {i : B ⟶ G} (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)

include hi hG in
/-- A relative Borel contains the full scheme-theoretic center. -/
theorem IsRelativeBorelSubgroup.center_le : center G ≤ SubgroupFunctor.range i := by
  rw [← hi.normalizer_eq hG]
  exact SubgroupFunctor.center_le_normalizer _

variable (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))

include hi hG hq ha in
private theorem adjointStabilizerData_nonempty :
    Nonempty (SubgroupFunctor.QuotientSubgroupData i q
      (a.subgroupStabilizer (SubgroupFunctor.range i))) := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  obtain ⟨Q, projection, hQ, hf, hs, hc, hfib⟩ :=
    RelativeParabolicQuotient.existence R G B i hG
      hi.isRelativeParabolicSubgroup.smooth
      (relativeParabolicClosed _ G B i hG hi.isRelativeParabolicSubgroup)
      (fun k _ _ => (hi.fieldPoint hG (Spec.algebraMap R k)).isParabolicSubgroup)
  let : IsProper Q.hom := hQ
  have hkernel : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i := by
    rw [hq.2.2.2]
    exact hi.center_le hG
  let r := HomogeneousQuotientFactorization.desc q (SubgroupFunctor.range i)
    projection hfib hkernel
  have hr : q.hom.hom ≫ r = projection :=
    HomogeneousQuotientFactorization.fac_desc q (SubgroupFunctor.range i)
      projection hfib hkernel
  refine ⟨?_⟩
  apply SubgroupFunctor.quotientSubgroupDataOfCosetMap i q
    (a.subgroupStabilizer (SubgroupFunctor.range i))
    (a.isFppfLocal_subgroupStabilizer (SubgroupFunctor.isFppfLocal_range i))
    _ projection hfib r hr
  rw [a.subgroupStabilizer_comap_of_restrict_eq_conjugation q ha, hi.normalizer_eq hG]

/-- Construct the Borel quotient by the center as an actual closed adjoint-action
stabilizer, with an fppf quotient projection and cartesian square. -/
def IsRelativeBorelSubgroup.adjointStabilizerData :
    SubgroupFunctor.QuotientSubgroupData i q
      (a.subgroupStabilizer (SubgroupFunctor.range i)) :=
  Classical.choice (adjointStabilizerData_nonempty hi hG q hq a ha)

end Borel

end Langlands.GroupScheme
