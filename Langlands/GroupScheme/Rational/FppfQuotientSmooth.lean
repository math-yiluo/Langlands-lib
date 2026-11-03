import Langlands.GroupScheme.Rational.FppfQuotientAction
import Langlands.GroupScheme.QuotientCell
import Langlands.GroupScheme.RepresentedSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smooth projection dimension from a represented fppf kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Base

variable {B : Scheme.{u}} {Z G Q : GroupScheme B} {N : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : IsFppfQuotient N q)
    {z : Z ⟶ G} (hz : N.IsRepresentedBy z)

include hq hz

/-- The specified representative of the quotient subgroup is the actual
scheme-theoretic kernel. -/
def IsFppfQuotient.kernelIso : Z ≅ kernel q :=
  hz.isoOfIsRepresentedBy ⟨inferInstance, hq.2.2.2⟩

/-- The kernel isomorphism respects the inclusions in the original group. -/
theorem IsFppfQuotient.kernelIso_hom_comp :
    (hq.kernelIso hz).hom ≫ kernelι q = z :=
  hz.isoOfIsRepresentedBy_hom_comp ⟨inferInstance, hq.2.2.2⟩

/-- Equal quotient images are exactly right differences in the represented
kernel, on every scheme test. -/
theorem IsFppfQuotient.fibers_iff (T : Over B) (g h : T ⟶ G.X) :
    g ≫ q.hom.hom = h ≫ q.hom.hom ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range z).carrier T := by
  rw [hz.2, ← hq.2.2.2, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp]
  exact inv_mul_eq_one.symm

/-- Smoothness of a represented kernel descends to the specified
quasi-compact fppf quotient projection. -/
theorem IsFppfQuotient.smooth_of_smooth_kernel [QuasiCompact q.hom.hom.left]
    (hZ : Smooth Z.X.hom) : Smooth q.hom.hom.left := by
  let : Mono z.hom.hom := hz.1
  let : Smooth Z.X.hom := hZ
  have hpb := (QuotientCell.multiplication_isPullback z (𝟙 G.X) q.hom.hom
    (hq.fibers_iff hz)).map (Over.forget B)
  change IsPullback (QuotientCell.multiplication z (𝟙 G.X)).left
    (fst G.X Z.X).left q.hom.hom.left ((𝟙 G.X) ≫ q.hom.hom).left at hpb
  simp only [Category.id_comp] at hpb
  have hsource : Smooth (fst G.X Z.X).left := by
    change Smooth (pullback.fst G.X.hom Z.X.hom)
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hpb.flip ⟨⟨hq.2.1, hq.1⟩, inferInstance⟩ hsource

end Base

section Field

variable {k : Type u} [Field k]
    {H Z G Q : GroupScheme (Spec (CommRingCat.of k))} {N : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : IsFppfQuotient N q)
    {z : Z ⟶ G} (hz : N.IsRepresentedBy z)

include hq hz in
/-- For connected source over a field, the projection has the same
smooth relative dimension as the represented kernel. -/
theorem IsFppfQuotient.smoothOfRelativeDimension_of_kernel
    [QuasiCompact q.hom.hom.left] [ConnectedSpace G.X.left]
    {n : ℕ} (hn : SmoothOfRelativeDimension n Z.X.hom) :
    SmoothOfRelativeDimension n q.hom.hom.left := by
  let : SmoothOfRelativeDimension n Z.X.hom := hn
  let : Smooth Z.X.hom := SmoothOfRelativeDimension.smooth n Z.X.hom
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hz inferInstance
  obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left Q.X.left q.hom.hom.left inferInstance inferInstance
  have hkernel : SmoothOfRelativeDimension m (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) hm
  let : SmoothOfRelativeDimension m (kernel q).X.hom := hkernel
  let e := hq.kernelIso hz
  let : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
  let : IsIso e.hom.hom.hom.left := (Over.forget _).map_isIso e.hom.hom.hom
  have hZ : SmoothOfRelativeDimension m Z.X.hom := by
    rw [← Over.w e.hom.hom.hom]
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + m)
        (e.hom.hom.hom.left ≫ (kernel q).X.hom))
  have hbase : Nonempty (Spec (CommRingCat.of k)) := by
    change Nonempty (PrimeSpectrum k)
    infer_instance
  let : Nonempty Z.X.left := ⟨η[Z.X].left (Classical.choice hbase)⟩
  have hnm : n = m := relativeDimension_eq Z.X.hom hn hZ
  exact hnm.symm ▸ hm

include hq hz in
/-- The action and strict dimension decrease on an affine fppf quotient follow
from the smooth positive dimension of its represented kernel. -/
theorem IsFppfQuotient.exists_action_relativeDimension_of_kernel
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom Q.X.hom]
    (hG : IsUnipotent G) (a : AutomorphicAction H G) (hN : a.IsStable N)
    {d n : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom)
    (hn : SmoothOfRelativeDimension n Z.X.hom) (hpos : 0 < n) :
    ∃ (b : AutomorphicAction H Q) (m : ℕ),
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ IsUnipotent Q ∧
      SmoothOfRelativeDimension n q.hom.hom.left ∧
      SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        b.act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom := by
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have hnq := hq.smoothOfRelativeDimension_of_kernel hz hn
  obtain ⟨b, m, hsm, hc, hu, hm, heq, hlt, hb⟩ :=
    hq.exists_action_relativeDimension hG a hN hd hnq hpos
  exact ⟨b, m, hsm, hc, hu, hnq, hm, heq, hlt, hb⟩

end Field

end Langlands.GroupScheme.RelativeRoot
