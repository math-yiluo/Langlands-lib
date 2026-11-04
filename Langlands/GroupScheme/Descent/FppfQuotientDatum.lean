import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Descent.Data

/-! # The canonical descent datum on a supplied fppf quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace FppfQuotientDiagram

variable {S : Scheme.{u}} {G G' G'' N N' N'' Q Q' Q'' : GroupScheme S}
    {i : N ⟶ G} {i' : N' ⟶ G'} {i'' : N'' ⟶ G''}
    {q : G ⟶ Q} {q' : G' ⟶ Q'} {q'' : G'' ⟶ Q''}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') q')

include hq hq' in
/-- A square of subgroup inclusions carries the first quotient kernel to the second. -/
theorem kernel_comp (a : G ⟶ G') (b : N ⟶ N') (h : i ≫ a = b ≫ i') :
    kernelι q ≫ (a ≫ q') = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ (a ≫ q').hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  apply (mem_range_kernelι_iff q' _).mp
  rw [hq'.2.2.2]
  have hi : (kernelι q).hom.hom ∈ (SubgroupFunctor.range i).carrier (kernel q).X := by
    rw [← hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hi
  refine SubgroupFunctor.mem_range.mpr ⟨x ≫ b.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, ← h, Grp.comp_hom_hom,
    ← Category.assoc, hx]

/-- The actual map of quotients induced by a commuting subgroup square. -/
def map [QuasiCompact q.hom.hom.left]
    (a : G ⟶ G') (b : N ⟶ N') (h : i ≫ a = b ≫ i') : Q ⟶ Q' :=
  letI := hq.1
  letI := hq.2.1
  FpqcHomDescent.hom q (a ≫ q') (kernel_comp hq hq' a b h)

@[reassoc]
theorem map_fac [QuasiCompact q.hom.hom.left]
    (a : G ⟶ G') (b : N ⟶ N') (h : i ≫ a = b ≫ i') :
    q ≫ map hq hq' a b h = a ≫ q' := by
  have := hq.1
  have := hq.2.1
  exact FpqcHomDescent.fac q (a ≫ q') (kernel_comp hq hq' a b h)

/-- Isomorphisms on ambient groups and represented kernels induce an actual
isomorphism of quotients. -/
def iso [QuasiCompact q.hom.hom.left] [QuasiCompact q'.hom.hom.left]
    (a : G ≅ G') (b : N ≅ N') (h : i ≫ a.hom = b.hom ≫ i') : Q ≅ Q' where
  hom := map hq hq' a.hom b.hom h
  inv := map hq' hq a.inv b.inv (by
    apply (cancel_mono a.hom).mp
    rw [Category.assoc, a.inv_hom_id, Category.comp_id, Category.assoc,
      h, b.inv_hom_id_assoc])
  hom_inv_id := by
    apply FppfQuotientComparison.hom_ext hq
    rw [← Category.assoc, map_fac, Category.assoc, map_fac, ← Category.assoc,
      a.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply FppfQuotientComparison.hom_ext hq'
    rw [← Category.assoc, map_fac, Category.assoc, map_fac, ← Category.assoc,
      a.inv_hom_id, Category.id_comp, Category.comp_id]

@[reassoc]
theorem iso_fac [QuasiCompact q.hom.hom.left] [QuasiCompact q'.hom.hom.left]
    (a : G ≅ G') (b : N ≅ N') (h : i ≫ a.hom = b.hom ≫ i') :
    q ≫ (iso hq hq' a b h).hom = a.hom ≫ q' := map_fac hq hq' a.hom b.hom h

end FppfQuotientDiagram

namespace Descent

variable {B S T : Scheme.{u}} {p : S ⟶ B}
    {G N Q : GroupScheme S} (D : Datum p G) (E : Datum p N)
    (i : N ⟶ G) (q : G ⟶ Q)
    (hi : Compatible E D i)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)

include hq in
private theorem quotient_baseChange (b : T ⟶ S) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map i))
      ((baseChange b).map q) := by
  simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b

variable [QuasiCompact q.hom.hom.left]

private instance quotient_qc (b : T ⟶ S) :
    QuasiCompact ((baseChange b).map q).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) b q.hom.hom inferInstance

/-- The uniquely induced isomorphism of the two overlap quotients. -/
def quotientOverlap : OverlapIso p Q :=
  FppfQuotientDiagram.iso (quotient_baseChange i q hq (fst p))
    (quotient_baseChange i q hq (snd p)) D.overlap E.overlap hi

@[reassoc]
theorem quotientOverlap_fac :
    (baseChange (fst p)).map q ≫ (quotientOverlap D E i q hi hq).hom =
      D.overlap.hom ≫ (baseChange (snd p)).map q :=
  FppfQuotientDiagram.iso_fac _ _ _ _ _

/-- The overlap factor equation remains true on every refinement, expressed
using direct pullbacks on both sides. -/
theorem pullHom_quotientOverlap_fac (a : T ⟶ Overlap p) {r s : T ⟶ S}
    (hr : a ≫ fst p = r) (hs : a ≫ snd p = s) :
    (baseChange r).map q ≫ pullHom a hr hs (quotientOverlap D E i q hi hq).hom =
      pullHom a hr hs D.overlap.hom ≫ (baseChange s).map q := by
  have h := congrArg (fun f => pullHom a hr hs f) (quotientOverlap_fac D E i q hi hq)
  rw [pullHom_comp a hr hr hs, pullHom_comp a hr hs hs, pullHom_map, pullHom_map] at h
  exact h

/-- The quotient overlap satisfies the cocycle because it does so after the
surjective quotient from the ambient group on the triple overlap. -/
theorem quotientOverlap_cocycle : Cocycle (quotientOverlap D E i q hi hq) := by
  change pullHom (p12 p) rfl rfl _ ≫ pullHom (p23 p) (p23_fst p) rfl _ =
    pullHom (p13 p) (p13_fst p) (p13_snd p) _
  apply FppfQuotientComparison.hom_ext (hq.baseChange (p1 p))
  rw [← Category.assoc, pullHom_quotientOverlap_fac, Category.assoc,
    pullHom_quotientOverlap_fac, ← Category.assoc]
  have hc := D.cocycle
  change pullHom (p12 p) rfl rfl _ ≫ pullHom (p23 p) (p23_fst p) rfl _ =
    pullHom (p13 p) (p13_fst p) (p13_snd p) _ at hc
  rw [hc, pullHom_quotientOverlap_fac]

/-- The actual descent datum induced on a supplied fppf quotient by compatible
data on its ambient group and represented kernel. -/
def quotientDatum : Datum p Q where
  overlap := quotientOverlap D E i q hi hq
  cocycle := quotientOverlap_cocycle D E i q hi hq

/-- The quotient homomorphism respects the induced datum. -/
theorem compatible_quotientDatum : Compatible D (quotientDatum D E i q hi hq) q :=
  quotientOverlap_fac D E i q hi hq

end Descent
end Langlands.GroupScheme
