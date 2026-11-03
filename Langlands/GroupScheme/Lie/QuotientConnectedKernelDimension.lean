import Langlands.GroupScheme.Lie.QuotientDimension
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Dimension decrease for a nontrivial smooth connected kernel

A nontrivial smooth connected affine subgroup contributes a nonzero tangent
vector. A smooth homomorphism killing that subgroup therefore strictly lowers
Lie dimension. This applies to every supplied affine fppf quotient by a
nontrivial split ground-field unipotent radical.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace Lie

/-- A subgroup with nontrivial all-test image has a nonzero tangent vector
when its source is connected, affine and locally of finite type. -/
theorem exists_tangent_ne_zero_of_range_ne_bot
    {N G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    [ConnectedSpace N.X.left] (n : N ⟶ G)
    (hne : SubgroupFunctor.range n ≠ ⊥) :
    ∃ X : Additive (lieKernel N k), X ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ X : Additive (lieKernel N k), X = 0 := by
    simpa only [not_exists, not_not] using h
  let : Subsingleton (lieKernel N k) := ⟨fun X Y => by
    have hX := congrArg Additive.toMul (hzero (Additive.ofMul X))
    have hY := congrArg Additive.toMul (hzero (Additive.ofMul Y))
    exact hX.trans hY.symm⟩
  apply hne
  apply SubgroupFunctor.ext
  intro T
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  change y ≫ n.hom.hom = 1
  rw [points_eq_one_of_subsingleton_lieKernel N T y, MonObj.one_comp]

/-- A chosen nonzero tangent vector of a connected affine subgroup with
nontrivial all-test image. -/
def nonzeroTangentOfRangeNeBot
    {N G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    [ConnectedSpace N.X.left] (n : N ⟶ G)
    (hne : SubgroupFunctor.range n ≠ ⊥) :
    {X : Additive (lieKernel N k) // X ≠ 0} :=
  ⟨Classical.choose (exists_tangent_ne_zero_of_range_ne_bot n hne),
    Classical.choose_spec (exists_tangent_ne_zero_of_range_ne_bot n hne)⟩

/-- Killing a nontrivial connected affine subgroup strictly lowers Lie dimension
for any smooth affine group homomorphism. The subgroup source need only be
locally of finite type; monicity preserves its nonzero tangent vector. -/
theorem dimension_lt_of_smooth_kills_connected_subgroup
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    [ConnectedSpace N.X.left]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (q : G ⟶ Q) (hq : Smooth q.hom.hom.left)
    (n : N ⟶ G) [Mono n.hom.hom]
    (hkill : n.hom.hom ≫ q.hom.hom = 1)
    (hne : SubgroupFunctor.range n ≠ ⊥) :
    dimension Q < dimension G := by
  obtain ⟨X, hX⟩ := nonzeroTangentOfRangeNeBot n hne
  apply dimension_lt_of_smooth_of_kernel q hq (targetMapLinear n k X)
  · intro h
    exact hX (targetMapLinear_injective n k
      (h.trans (map_zero (targetMapLinear n k)).symm))
  · apply Additive.toMul.injective
    apply Subtype.ext
    change (X.toMul.val ≫ n.hom.hom) ≫ q.hom.hom = 1
    rw [Category.assoc, hkill, MonObj.comp_one]

end Lie

namespace RelativeRoot

/-- A nontrivial connected smooth represented kernel strictly lowers the Lie
dimension of any supplied quasi-compact affine fppf group quotient. -/
theorem IsFppfQuotient.lieDimension_lt_of_nontrivial_connected_kernel
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    [ConnectedSpace N.X.left]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    {F : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : IsFppfQuotient F q) [QuasiCompact q.hom.hom.left]
    {n : N ⟶ G} (hn : F.IsRepresentedBy n)
    (hN : Smooth N.X.hom) (hne : F ≠ ⊥) :
    Lie.dimension Q < Lie.dimension G := by
  let : Mono n.hom.hom := hn.1
  apply Lie.dimension_lt_of_smooth_kills_connected_subgroup q
    (hq.smooth_of_smooth_kernel hn hN) n
  · have hmem : n.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier N.X := by
      rw [hq.2.2.2, ← hn.2]
      change ∃ y, y ≫ n.hom.hom = n.hom.hom
      exact ⟨𝟙 N.X, Category.id_comp _⟩
    exact (mem_range_kernelι_iff q n.hom.hom).mp hmem
  · simpa only [hn.2] using hne

end RelativeRoot

/-- A supplied affine fppf quotient by a nontrivial split ground-field radical
has strictly smaller Lie dimension. Quasi-compactness of the projection follows
from affineness of its source over the field. -/
theorem IsSplitUnipotentRadical.quotient_lieDimension_lt
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    {n : N ⟶ G} (hn : IsSplitUnipotentRadical n)
    {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hne : SubgroupFunctor.range n ≠ ⊥) :
    Lie.dimension Q < Lie.dimension G := by
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : IsAffineHom N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  let : Smooth N.X.hom := hn.smooth
  let : ConnectedSpace N.X.left := hn.connectedSpace
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact hq.lieDimension_lt_of_nontrivial_connected_kernel
    ⟨Over.mono_of_mono_left _, rfl⟩ hn.smooth hne

end Langlands.GroupScheme
