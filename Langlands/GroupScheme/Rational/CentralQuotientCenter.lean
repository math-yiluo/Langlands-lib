import Langlands.GroupScheme.Rational.CentralTorusQuotientNoTorus
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Reductive.FiniteCenterReflection
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # The centre of the quotient by a largest central torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A flat surjective homomorphism sends every central homomorphism to a central one. -/
theorem IsCentral.comp_flat_surjective {S : Scheme.{u}}
    {A G Q : GroupScheme S} {i : A ⟶ G} (hi : IsCentral i) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] : IsCentral (i ≫ q) := by
  intro U x V a y
  let P : Over S := pullback y q.hom.hom
  let p : P ⟶ V := pullback.fst y q.hom.hom
  let r : P ⟶ G.X := pullback.snd y q.hom.hom
  have hpb : IsPullback p.left r.left y.left q.hom.hom.left :=
    (IsPullback.of_hasPullback y q.hom.hom).map (Over.forget S)
  let : Flat p.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  let : Surjective p.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  let : Epi p.left := Flat.epi_of_flat_of_surjective _
  have h := ((hi U x P (p ≫ a) r).map
    ((yonedaGrp.map q).app (Opposite.op P)).hom).eq
  change (((p ≫ a) ≫ (x ≫ i.hom.hom)) ≫ q.hom.hom) * (r ≫ q.hom.hom) =
    (r ≫ q.hom.hom) * (((p ≫ a) ≫ (x ≫ i.hom.hom)) ≫ q.hom.hom) at h
  have hp : p ≫ y = r ≫ q.hom.hom := pullback.condition
  change (a ≫ (x ≫ (i ≫ q).hom.hom)) * y = y * (a ≫ (x ≫ (i ≫ q).hom.hom))
  apply Over.OverMorphism.ext
  apply (cancel_epi p.left).mp
  have h' : p ≫ ((a ≫ (x ≫ (i ≫ q).hom.hom)) * y) =
      p ≫ (y * (a ≫ (x ≫ (i ≫ q).hom.hom))) := by
    simpa only [MonObj.comp_mul, Grp.comp_hom_hom, Category.assoc, hp] using h
  exact congrArg (fun f => f.left) h'

variable {k : Type u} [Field k]

/-- Every torus homomorphism to the full centre of this quotient vanishes. -/
theorem IsLargestCentralSubtorus.quotient_center_torus_hom_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} {z : Z.toGrp ⟶ G}
    (hz : IsLargestCentralSubtorus z)
    {Q : GroupScheme (Spec (CommRingCat.of k))} [Smooth Q.X.hom] [IsAffineHom Q.X.hom]
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    {C : GroupScheme (Spec (CommRingCat.of k))} {c : C ⟶ Q}
    (hc : IsSchemeTheoreticCenter c)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (f : T.toGrp ⟶ C) : f = 0 := by
  let : IsClosedImmersion c.hom.hom.left := hc.1
  let : IsAffineHom C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  let : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  let : QuasiCompact T.toGrp.X.hom := hT.quasiCompact
  have : QuasiCompact (f.hom.hom.left ≫ C.X.hom) := by
    rw [Over.w]
    infer_instance
  let : QuasiCompact f.hom.hom.left := QuasiCompact.of_comp _ C.X.hom
  have hT' := hT.isTorus_schematicImage f
  let T' : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image f with comm := hT'.isCommMonObj }
  let i : T'.toGrp ⟶ C := SchematicImage.inclusion f
  let p : T.toGrp ⟶ T'.toGrp := SchematicImage.projection f
  have hi : IsClosedSubgroup i :=
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion f).hom.hom.left)
  have hp : p ≫ i = f := SchematicImage.projection_inclusion f
  have hzero : i ≫ c = 0 := hz.central_torus_quotient_eq_zero q hq (i ≫ c)
    hT' (hi.comp hc.1) (hc.isCentral.comp i)
  apply hc.isRepresentedBy.hom_ext
  rw [← hp, Category.assoc, hzero, comp_zero, zero_comp]

/-- Vanishing of torus maps to the base-changed quotient centre proves greatestness
of the original central torus after extension. -/
theorem IsLargestCentralSubtorus.baseChange_of_quotient_center
    {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} {z : Z.toGrp ⟶ G}
    (hz : IsLargestCentralSubtorus z)
    {Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    {C : GroupScheme (Spec (CommRingCat.of k))} {c : C ⟶ Q}
    (hc : IsSchemeTheoreticCenter c)
    (hC : ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj C, f = 0) :
    IsLargestCentralSubtorus (Z := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map z) := by
  let b := algebraBaseMap k K
  let F := GroupScheme.baseChange b
  have hqK := hq.baseChange b
  let : Flat (F.map q).hom.hom.left := hqK.1
  let : Surjective (F.map q).hom.hom.left := hqK.2.1
  have hcK := hc.baseChange b
  refine ⟨hz.isTorus.baseChange, hz.isClosedSubgroup.baseChange b,
    hz.isCentral.baseChange b, ?_⟩
  intro T a hT _ha hac
  have hcentral : IsCentral (a ≫ F.map q) := hac.comp_flat_surjective (F.map q)
  have hle : SubgroupFunctor.range (a ≫ F.map q) ≤ center (F.obj Q) :=
    (isCentral_iff_range_le_center _).mp hcentral
  have hzero : a ≫ F.map q = 0 := by
    rw [← hcK.isRepresentedBy.factorHom_comp (a ≫ F.map q) hle,
      hC T hT (hcK.isRepresentedBy.factorHom (a ≫ F.map q) hle), zero_comp]
  have hker : SubgroupFunctor.range (kernelι (F.map q)) = SubgroupFunctor.range (F.map z) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hqK.2.2.2
  intro U x hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hker, mem_range_kernelι_iff, ← hy, Category.assoc, ← Grp.comp_hom_hom, hzero]
  exact MonObj.comp_one _

end Langlands.GroupScheme
