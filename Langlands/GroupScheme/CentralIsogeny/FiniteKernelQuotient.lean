import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.KernelPair
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Finite central quotients from finite scheme-theoretic kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section FiniteKernel

variable {S : Scheme.{u}} {G Q N : GroupScheme S}

/-- An fpqc group homomorphism with finite actual kernel is finite. -/
theorem isFinite_of_finite_kernel (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] [IsFinite (kernel q).X.hom] :
    IsFinite q.hom.hom.left := by
  have hp : IsFinite (fst G.X (kernel q).X).left := by
    change IsFinite (pullback.fst G.X.hom (kernel q).X.hom)
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (KernelPair.isPullback_scheme q) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hp

/-- Equality of the full point functors identifies the specified finite kernel
with the actual scheme kernel, so an fpqc quotient by it is finite. -/
theorem RelativeRoot.IsFppfQuotient.isFinite_of_finite_subgroup
    {i : N ⟶ G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hi : Mono i.hom.hom) [QuasiCompact q.hom.hom.left] [IsFinite N.X.hom] :
    IsFinite q.hom.hom.left := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  have hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨hi, rfl⟩
  have hk : (SubgroupFunctor.range i).IsRepresentedBy (kernelι q) :=
    ⟨inferInstance, hq.2.2.2⟩
  let e : N ≅ kernel q := hr.isoOfIsRepresentedBy hk
  let : IsIso e.inv.hom.hom := (Grp.forget (Over S)).map_isIso e.inv
  let : IsIso e.inv.hom.hom.left := (Over.forget S).map_isIso e.inv.hom.hom
  let : IsFinite (kernel q).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  exact isFinite_of_finite_kernel q

/-- An fpqc quotient by a finite central subgroup is a central isogeny. -/
theorem RelativeRoot.IsFppfQuotient.isCentralIsogeny_of_finite_subgroup
    {i : N ⟶ G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hi : Mono i.hom.hom) (hc : IsCentral i)
    [QuasiCompact q.hom.hom.left] [IsFinite N.X.hom] :
    IsCentralIsogeny q := by
  refine ⟨⟨hq.isFinite_of_finite_subgroup hi, hq.1, hq.2.1⟩, hq.2.2.1, ?_⟩
  apply (isCentral_iff_range_le_center _).mpr
  rw [hq.2.2.2]
  exact (isCentral_iff_range_le_center _).mp hc

end FiniteKernel

/-- Every finite central closed subgroup of a smooth affine group over a field
is the exact kernel of a central isogeny onto a smooth affine group. -/
theorem exists_centralIsogeny_of_finite_central_subgroup
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G)
    (hi : IsClosedSubgroup i) (hfin : IsFinite N.X.hom) (hc : IsCentral i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ IsCentralIsogeny q ∧
        SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i := by
  obtain ⟨Q, q, hs, ha, hq⟩ := normalSubgroupQuotient k G N i hi hn
  let : IsAffineHom Q.X.hom := ha
  let : IsFinite N.X.hom := hfin
  let : IsClosedImmersion i.hom.hom.left := hi
  let : QuasiCompact q.hom.hom.left := by
    have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ Q.X.hom
  exact ⟨Q, q, hs, ha,
    hq.isCentralIsogeny_of_finite_subgroup (Over.mono_of_mono_left _) hc, hq.2.2.2⟩


/-- Finite central normal closed subgroups have actual central-isogeny quotients
onto smooth affine groups over arbitrary fields. -/
def FiniteCentralSubgroupQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsClosedSubgroup i → IsFinite N.X.hom → IsCentral i →
      (SubgroupFunctor.range i).IsNormal →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ IsCentralIsogeny q ∧
          SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i

/-- The universal finite central subgroup quotient proposition. -/
theorem finiteCentralSubgroupQuotient : FiniteCentralSubgroupQuotientStatement.{u} := by
  intro k _ G _ _ N i hi hfin hc hn
  exact exists_centralIsogeny_of_finite_central_subgroup k G N i hi hfin hc hn

end Langlands.GroupScheme
