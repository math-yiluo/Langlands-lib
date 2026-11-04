import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Tori in quotients with unipotent kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {H G Q : GroupScheme S}

/-- A monic subgroup stays monic after a homomorphism whose kernel is contained
in a subgroup functor meeting it trivially on every scheme test. -/
theorem mono_comp_of_kernel_range_le_of_inf_eq_bot
    (i : H ⟶ G) (q : G ⟶ Q) [Mono i.hom.hom]
    (N : SubgroupFunctor G)
    (hker : SubgroupFunctor.range (kernelι q) ≤ N)
    (hinter : N ⊓ SubgroupFunctor.range i = ⊥) :
    Mono (i ≫ q).hom.hom := by
  constructor
  intro A x y hxy
  have hq : ((x⁻¹ * y) ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
    change (x⁻¹ * y) ≫ (i ≫ q).hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
  have hmem : (x⁻¹ * y) ≫ i.hom.hom ∈
      (N ⊓ SubgroupFunctor.range i).carrier A :=
    ⟨hker A ((mem_range_kernelι_iff q _).mpr hq), ⟨x⁻¹ * y, rfl⟩⟩
  rw [hinter] at hmem
  have hone : x⁻¹ * y = 1 := by
    apply (cancel_mono i.hom.hom).mp
    exact (Subgroup.mem_bot.mp hmem).trans (MonObj.one_comp _).symm
  exact inv_mul_eq_one.mp hone

end ArbitraryBase

section Field

variable {k : Type u} [Field k]
  {N T G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Conditional on closed-subgroup unipotence, the actual intersection of the
range of an affine finite-type unipotent group with a closed torus is trivial.
The homomorphism from the unipotent group need not be monic. -/
theorem IsUnipotent.range_inf_torus_eq_bot
    (hsub : UnipotentClosedSubgroupStatement.{u})
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i) :
    SubgroupFunctor.range n ⊓ SubgroupFunctor.range i = ⊥ := by
  have hii : IsClosedImmersion i.hom.hom.left := hi
  have hfst : IsClosedImmersion (subgroupIntersectionFst n i).hom.hom.left :=
    MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme n i).flip hii
  let : IsClosedImmersion (subgroupIntersectionFst n i).hom.hom.left := hfst
  let : IsAffineHom (subgroupIntersection n i).X.hom := by
    rw [← Over.w (subgroupIntersectionFst n i).hom.hom]
    infer_instance
  have hW : IsUnipotent (subgroupIntersection n i) :=
    hsub k N (subgroupIntersection n i) (subgroupIntersectionFst n i) hfst hN
  have hzero : subgroupIntersectionHom n i = 0 := by
    change subgroupIntersectionFst n i ≫ n = 0
    rw [subgroupIntersection_condition,
      hW.hom_eq_zero_of_isTorus hT (subgroupIntersectionSnd n i), zero_comp]
  rw [← range_subgroupIntersectionHom n i, hzero, SubgroupFunctor.range_zero]

/-- A closed torus maps monomorphically through any homomorphism whose full
scheme-theoretic kernel is contained in an affine finite-type unipotent range.
Closed-subgroup unipotence remains an explicit premise. -/
theorem IsUnipotent.mono_torus_quotient
    (hsub : UnipotentClosedSubgroupStatement.{u})
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n) :
    Mono (i ≫ q).hom.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact mono_comp_of_kernel_range_le_of_inf_eq_bot i q (SubgroupFunctor.range n)
    hker (hN.range_inf_torus_eq_bot hsub hT n i hi)

/-- The induced embedding of torus points into the quotient on each scheme test,
conditional on closed-subgroup unipotence. -/
def IsUnipotent.torusQuotientPointEmbedding
    (hsub : UnipotentClosedSubgroupStatement.{u})
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n)
    (A : Over (Spec (CommRingCat.of k))) : (A ⟶ T.X) ↪ (A ⟶ Q.X) :=
  letI := hN.mono_torus_quotient hsub hT n i hi q hker
  { toFun := fun x => x ≫ (i ≫ q).hom.hom
    inj' := fun _ _ h => (cancel_mono (i ≫ q).hom.hom).mp h }

@[simp]
theorem IsUnipotent.torusQuotientPointEmbedding_apply
    (hsub : UnipotentClosedSubgroupStatement.{u})
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n)
    (A : Over (Spec (CommRingCat.of k))) (x : A ⟶ T.X) :
    hN.torusQuotientPointEmbedding hsub hT n i hi q hker A x =
      x ≫ i.hom.hom ≫ q.hom.hom :=
  rfl

/-- The constructed point embeddings commute with every restriction of tests. -/
theorem IsUnipotent.torusQuotientPointEmbedding_naturality
    (hsub : UnipotentClosedSubgroupStatement.{u})
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n)
    {A B : Over (Spec (CommRingCat.of k))} (a : B ⟶ A) (x : A ⟶ T.X) :
    hN.torusQuotientPointEmbedding hsub hT n i hi q hker B (a ≫ x) =
      a ≫ hN.torusQuotientPointEmbedding hsub hT n i hi q hker A x := by
  simp only [IsUnipotent.torusQuotientPointEmbedding_apply, Category.assoc]

end Field

end Langlands.GroupScheme
