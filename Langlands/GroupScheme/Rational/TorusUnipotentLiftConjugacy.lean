import Langlands.GroupScheme.Rational.TorusUnipotentCocycle
import Langlands.GroupScheme.Rational.QuotientHomCocycle

/-! # Same-source torus lifts through split unipotent kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace QuotientHomCocycle

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (htorsor : SplitUnipotentAffineTorsorStatement.{u})
    {k : Type u} [Field k]
    {H N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [Smooth N.X.hom] [IsAffineHom N.X.hom]
    [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (i₀ i₁ : H ⟶ G) (hi : i₀ ≫ q = i₁ ≫ q) (hH : IsTorus H)

/-- A rational kernel point conjugating any two same-source torus maps with
equal quotient maps, conditional on the three named structural inputs. -/
def splitUnipotentTorusConjugator :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X :=
  RelativeRoot.torusUnipotentCocycleConjugator hstable hlinear htorsor H hH N
    hN hNsplit (action n q hn i₀) (cocycle n q hn i₀ i₁ hi)

/-- The constructed point conjugates the actual homomorphisms with the
identity source isomorphism; neither source map need be monic. -/
theorem splitUnipotentTorusConjugator_conjugates :
    i₀ ≫ (G.innerIso
      (splitUnipotentTorusConjugator hstable hlinear htorsor
        n q hn hN hNsplit i₀ i₁ hi hH ≫ n.hom.hom)).hom = i₁ := by
  apply (cocycle_eq_coboundary_iff n q hn i₀ i₁ hi _).1
  exact RelativeRoot.cocycle_eq_coboundary_of_split_unipotent_of_structuralStatements
    hstable hlinear htorsor H hH N hN hNsplit
      (action n q hn i₀) (cocycle n q hn i₀ i₁ hi)

/-- The actual conjugating point lies in the original represented kernel. -/
theorem splitUnipotentTorusConjugator_mem_kernel :
    splitUnipotentTorusConjugator hstable hlinear htorsor
      n q hn hN hNsplit i₀ i₁ hi hH ≫ n.hom.hom ∈
        (SubgroupFunctor.range (kernelι q)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← hn]
  exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

include hn hi hN hNsplit hH hstable hlinear htorsor

/-- Equality after the quotient implies conjugacy of the homomorphisms
themselves, preserving every source point. -/
theorem homConjugate_of_isTorus_split_unipotent_kernel : HomConjugate i₀ i₁ :=
  ⟨_, splitUnipotentTorusConjugator_conjugates
    hstable hlinear htorsor n q hn hN hNsplit i₀ i₁ hi hH⟩

/-- The same kernel point supplies subgroup conjugacy with the identity
source isomorphism. -/
theorem subgroupConjugate_of_isTorus_split_unipotent_kernel :
    SubgroupConjugate i₀ i₁ := by
  refine ⟨splitUnipotentTorusConjugator hstable hlinear htorsor
    n q hn hN hNsplit i₀ i₁ hi hH ≫ n.hom.hom, Iso.refl H, ?_⟩
  simpa only [Iso.refl_hom, Category.id_comp] using
    splitUnipotentTorusConjugator_conjugates
      hstable hlinear htorsor n q hn hN hNsplit i₀ i₁ hi hH

end QuotientHomCocycle

section Fppf

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (htorsor : SplitUnipotentAffineTorsorStatement.{u})
    {k : Type u} [Field k]
    {H N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hNsm : Smooth N.X.hom) (hNconn : ConnectedSpace N.X.left)
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (i₀ i₁ : H ⟶ G) (hi : i₀ ≫ q = i₁ ≫ q) (hH : IsTorus H)

include hstable hlinear htorsor hn hNsm hNconn hN hNsplit hq hi hH

/-- The same-source equality interface for a represented fppf quotient with
smooth connected closed split unipotent kernel in an affine ambient group.
The torus maps may be trivial or noninjective. -/
theorem homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements :
    HomConjugate i₀ i₁ := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : Smooth N.X.hom := hNsm
  let : ConnectedSpace N.X.left := hNconn
  let : IsAffineHom N.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact QuotientHomCocycle.homConjugate_of_isTorus_split_unipotent_kernel
    hstable hlinear htorsor n q hq.2.2.2.symm hN hNsplit i₀ i₁ hi hH

/-- Subgroup conjugacy for the same fppf quotient, with no maximality
assumption on either torus map. -/
theorem subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements :
    SubgroupConjugate i₀ i₁ := by
  obtain ⟨g, hg⟩ :=
    homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
      hstable hlinear htorsor n hn hNsm hNconn hN hNsplit q hq i₀ i₁ hi hH
  exact ⟨g, Iso.refl H, by simpa only [Iso.refl_hom, Category.id_comp] using hg⟩

end Fppf

end Langlands.GroupScheme
