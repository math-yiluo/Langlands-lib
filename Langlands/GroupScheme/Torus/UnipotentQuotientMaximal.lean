import Langlands.GroupScheme.Torus.QuotientMaximal
import Langlands.GroupScheme.Rational.SplitUnipotentQuotientTorusLift
import Langlands.GroupScheme.Rational.TorusUnipotentQuotientConjugacy
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Maximal tori through smooth connected unipotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Quotient

variable {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : IsUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)

include hi hn hN hq

/-- Full maximality is preserved by a quotient with smooth connected closed
split-unipotent kernel. All structural inputs are supplied by published proofs. -/
theorem IsMaximalTorus.comp_of_split_unipotent_kernel
    (hNsplit : RelativeRoot.IsSplitUnipotent N) : IsMaximalTorus (i ≫ q) := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  have hc : IsClosedSubgroup (i ≫ q) :=
    hN.closed_torus_quotient unipotentClosedSubgroup hi.1 n i hi.2.1 q hq.2.2.2.le
  apply hi.comp_of_torus_lifts q hc
  · intro T' i' hT' hi'
    exact hT'.exists_splitUnipotentQuotientLift n q hq hN hNsplit
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization i' hi'
  · intro j hj
    exact subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
      n hn inferInstance inferInstance hN hNsplit q hq i j hj hi.1

/-- Over a perfect field, smooth connected unipotence of the represented
full kernel suffices for preservation of full maximality. -/
theorem IsMaximalTorus.comp_of_perfect_field_unipotent_kernel [PerfectField k] :
    IsMaximalTorus (i ≫ q) := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : IsAffineHom N.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact hi.comp_of_split_unipotent_kernel n hn hN q hq
    (perfectFieldUnipotentSplit k N inferInstance hN)

end Quotient

/-- The original source of every maximal torus remains a maximal torus after
an fppf quotient with smooth connected unipotent kernel over a perfect field. -/
def PerfectFieldUnipotentQuotientMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k]
    (N G Q : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (n : N ⟶ G) (q : G ⟶ Q),
    IsClosedSubgroup n → IsUnipotent N →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q)

theorem perfectFieldUnipotentQuotientMaximalTorus :
    PerfectFieldUnipotentQuotientMaximalTorusStatement.{u} := by
  intro k _ _ N G Q _ _ _ _ _ _ n q hn hN hq T i hi
  exact hi.comp_of_perfect_field_unipotent_kernel n hn hN q hq

end Langlands.GroupScheme
