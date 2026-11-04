import Langlands.GroupScheme.Absolute.TriangularCoordinateKernelEmbeddings
import Langlands.GroupScheme.LinearKernelTower
import Langlands.GroupScheme.ActionDescent

/-! # Descending character-linear conjugation on actual quotient kernels -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearKernelTower

variable {S : Scheme.{u}} {E Q : GroupScheme S}

/-- Actual conjugation on a supplied monic normal subgroup. -/
def normalConjugation {H K : GroupScheme S} (i : K ⟶ H)
    [Mono i.hom.hom] (hn : (SubgroupFunctor.range i).IsNormal) :
    AutomorphicAction H K :=
  AutomorphicAction.ofNormalizedConjugation i (𝟙 H)
    (fun T g x _ hx => hn T g x (Subgroup.mem_top g) hx)

theorem normalConjugation_comp {H K : GroupScheme S} (i : K ⟶ H)
    [Mono i.hom.hom] (hn : (SubgroupFunctor.range i).IsNormal)
    {T : Over S} (g : T ⟶ H.X) (x : T ⟶ K.X) :
    (normalConjugation i hn).act g x ≫ i.hom.hom =
      g * (x ≫ i.hom.hom) * g⁻¹ := by
  simpa only [AutomorphicAction.act, normalConjugation,
    AutomorphicAction.ofNormalizedConjugation, Grp.id_hom_hom, Category.comp_id] using
    SubgroupFunctor.lift_comp_normalizedConjugation_comp i (𝟙 H)
      (fun T g x _ hx => hn T g x (Subgroup.mem_top g) hx) g x

/-- The full kernel is normalized by its whole actual source. -/
theorem kernel_isNormalizedBy_source (p : E ⟶ Q) :
    (SubgroupFunctor.range (kernelι p)).IsNormalizedBy (SubgroupFunctor.range (𝟙 E)) := by
  intro T g x _ hx
  apply (mem_range_kernelι_iff p _).mpr
  have hx0 := (mem_range_kernelι_iff p x).mp hx
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx0, mul_one,
    mul_inv_cancel]

/-- The actual conjugation action of the source on its full scheme kernel. -/
def kernelConjugation (p : E ⟶ Q) : AutomorphicAction E (kernel p) :=
  AutomorphicAction.ofNormalizedConjugation (kernelι p) (𝟙 E)
    (kernel_isNormalizedBy_source p)

theorem kernelConjugation_comp (p : E ⟶ Q) {T : Over S}
    (g : T ⟶ E.X) (x : T ⟶ (kernel p).X) :
    (kernelConjugation p).act g x ≫ (kernelι p).hom.hom =
      g * (x ≫ (kernelι p).hom.hom) * g⁻¹ := by
  simpa only [AutomorphicAction.act, kernelConjugation,
    AutomorphicAction.ofNormalizedConjugation, Grp.id_hom_hom, Category.comp_id] using
    SubgroupFunctor.lift_comp_normalizedConjugation_comp
      (kernelι p) (𝟙 E) (kernel_isNormalizedBy_source p) g x

/-- A commuting square into an actual kernel transports conjugation whenever
the source action is actual ambient conjugation. -/
theorem kernelConjugation_act_lift {H K : GroupScheme S}
    (p : E ⟶ Q) (s : H ⟶ E) (i : K ⟶ H) (r : K ⟶ kernel p)
    (hs : r ≫ kernelι p = i ≫ s) (b : AutomorphicAction H K)
    (hb : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      b.act h x ≫ i.hom.hom = h * (x ≫ i.hom.hom) * h⁻¹)
    {T : Over S} (h : T ⟶ H.X) (x : T ⟶ K.X) :
    (kernelConjugation p).act (h ≫ s.hom.hom) (x ≫ r.hom.hom) =
      b.act h x ≫ r.hom.hom := by
  apply (cancel_mono (kernelι p).hom.hom).mp
  have hs' : r.hom.hom ≫ (kernelι p).hom.hom = i.hom.hom ≫ s.hom.hom :=
    congrArg (fun f => f.hom.hom) hs
  calc
    _ = (h ≫ s.hom.hom) * ((x ≫ r.hom.hom) ≫ (kernelι p).hom.hom) *
        (h ≫ s.hom.hom)⁻¹ := kernelConjugation_comp p _ _
    _ = (h * (x ≫ i.hom.hom) * h⁻¹) ≫ s.hom.hom := by
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
        Category.assoc, hs', ← Category.assoc]
    _ = (b.act h x ≫ r.hom.hom) ≫ (kernelι p).hom.hom := by
      rw [Category.assoc, hs', ← Category.assoc, hb]

variable {k : Type u} [Field k]
  {D : CommGroupScheme (Spec (CommRingCat.of k))}
  {E Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed additive embedding that intertwines source conjugation with a
character yields the actual descended diagonal action, by fpqc descent. -/
theorem isCharacterLinearKernel_of_conjugation
    (q : E ⟶ D.toGrp) (p : E ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (a : kernel p ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (ha : IsClosedSubgroup a) (χ : characterLattice D)
    (he : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X)
      (x : T ⟶ (kernel p).X),
      (kernelConjugation p).act g x ≫ a.hom.hom =
        (VectorGroup.weightAction (n := 1) χ).act (g ≫ q.hom.hom) (x ≫ a.hom.hom)) :
    IsCharacterLinearKernel D q p := by
  have : IsClosedImmersion a.hom.hom.left := ha
  have : Mono a.hom.hom := Over.mono_of_mono_left _
  have hk : (kernelConjugation p).KernelActsTrivially q := by
    intro T z x
    apply (cancel_mono a.hom.hom).mp
    rw [AutomorphicAction.restrict_act, he]
    have hz : (z ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 :=
      (kernelPointsEquiv q T z).property
    rw [hz, AutomorphicAction.act_one_left]
  let b := AutomorphicAction.quotientAction (kernelConjugation p) q hk
  refine ⟨a, χ, b, ha, ?_, ?_⟩
  · intro T g x
    rw [show b.act (g ≫ q.hom.hom) x = (kernelConjugation p).act g x from
      AutomorphicAction.quotientAction_act_lift _ _ _ g x]
    exact kernelConjugation_comp p g x
  · intro T d x
    apply AutomorphicAction.hom_ext_of_local_quotient_lift q d
    intro V f g hfg
    rw [← Category.assoc, AutomorphicAction.naturality, AutomorphicAction.naturality,
      ← Category.assoc, hfg]
    rw [show b.act (g ≫ q.hom.hom) (f ≫ x) =
      (kernelConjugation p).act g (f ≫ x) from
      AutomorphicAction.quotientAction_act_lift _ _ _ g (f ≫ x), he]

/-- Character equivariance can be checked on the original group and original
normal subgroup, after independently lifting both variables fpqc locally. -/
theorem isCharacterLinearKernel_of_local_lifts
    {H K : GroupScheme (Spec (CommRingCat.of k))}
    (q : E ⟶ D.toGrp) (p : E ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (s : H ⟶ E)
    [QuasiCompact s.hom.hom.left] [Flat s.hom.hom.left] [Surjective s.hom.hom.left]
    (i : K ⟶ H) (r : K ⟶ kernel p)
    [QuasiCompact r.hom.hom.left] [Flat r.hom.hom.left] [Surjective r.hom.hom.left]
    (hs : r ≫ kernelι p = i ≫ s) (b : AutomorphicAction H K)
    (hb : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      b.act h x ≫ i.hom.hom = h * (x ≫ i.hom.hom) * h⁻¹)
    (a : kernel p ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (ha : IsClosedSubgroup a) (χ : characterLattice D)
    (he : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      (b.act h x ≫ r.hom.hom) ≫ a.hom.hom =
        (VectorGroup.weightAction (n := 1) χ).act
          ((h ≫ s.hom.hom) ≫ q.hom.hom) ((x ≫ r.hom.hom) ≫ a.hom.hom)) :
    IsCharacterLinearKernel D q p := by
  apply isCharacterLinearKernel_of_conjugation q p a ha χ
  intro T g x
  apply AutomorphicAction.hom_ext_of_local_quotient_lift s g
  intro V f h hfg
  rw [← Category.assoc, AutomorphicAction.naturality, AutomorphicAction.naturality,
    ← Category.assoc, hfg]
  apply AutomorphicAction.hom_ext_of_local_quotient_lift r (f ≫ x)
  intro W t y hty
  rw [← Category.assoc, AutomorphicAction.naturality, AutomorphicAction.naturality,
    ← Category.assoc, hty, ← Category.assoc]
  rw [kernelConjugation_act_lift p s i r hs b hb]
  have hty' : t ≫ f ≫ x ≫ a.hom.hom = y ≫ r.hom.hom ≫ a.hom.hom := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ a.hom.hom) hty
  rw [hty']
  simpa only [Category.assoc] using he W (t ≫ h) y

end Langlands.GroupScheme.LinearKernelTower

namespace Langlands.GroupScheme.TriangularLayer.QuotientTerm

open LinearKernelTower

variable {k : Type u} [Field k]
  {D : CommGroupScheme (Spec (CommRingCat.of k))}
  {H K : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType K.X.hom] [IsAffineHom K.X.hom]
  {F E : SubgroupFunctor H} (A : QuotientTerm F) (B : QuotientTerm E)
  (hEF : E ≤ F) {i : K ⟶ H} [Mono i.hom.hom]
  (hi : F.IsRepresentedBy i) (hn : (SubgroupFunctor.range i).IsNormal)

include hi in
/-- A character-equivariant coordinate on the original normal subgroup gives
a character-linear full kernel for the actual quotient comparison. Image
existence and the quotient objects remain explicit. -/
theorem isCharacterLinearKernel_of_coordinate
    (himage : AffineHomImageStatement.{u})
    (q : B.quotient ⟶ D.toGrp)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (c : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (hc : SubgroupFunctor.range (kernelι c) = E.comap i)
    (χ : characterLattice D)
    (he : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      (normalConjugation i hn).act h x ≫ c.hom.hom =
        (VectorGroup.weightAction (n := 1) χ).act
          ((h ≫ B.hom.hom.hom) ≫ q.hom.hom) (x ≫ c.hom.hom)) :
    IsCharacterLinearKernel D q (comparison A B hEF) := by
  obtain ⟨a, ha, hca⟩ := exists_kernelEmbedding A B hEF hi himage c hc
  have hpb := (kernelRestriction_isPullback A B hEF hi).map
    (Over.forget (Spec (CommRingCat.of k)))
  have : QuasiCompact (kernelRestriction A B hEF hi).hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : QuasiCompact B.hom.hom.hom.left)
  have hr := kernelRestriction_isFppfQuotient A B hEF hi
  have := hr.1
  have := hr.2.1
  apply isCharacterLinearKernel_of_local_lifts q (comparison A B hEF)
    B.hom i (kernelRestriction A B hEF hi) (kernelRestriction_comp A B hEF hi)
    (normalConjugation i hn) (fun _ h x => normalConjugation_comp i hn h x) a ha χ
  intro T h x
  have hca' : (kernelRestriction A B hEF hi).hom.hom ≫ a.hom.hom = c.hom.hom :=
    congrArg (fun f => f.hom.hom) hca
  simpa only [Category.assoc, hca'] using he T h x

end Langlands.GroupScheme.TriangularLayer.QuotientTerm
