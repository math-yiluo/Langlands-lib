import Langlands.GroupScheme.Rational.QuotientHomCocycle
import Langlands.GroupScheme.Rational.TorusVectorCocycle

/-! # Rational conjugacy of torus lifts across a linear vector kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientHomCocycle

variable {k : Type u} [Field k]
    {H N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [IsAffineHom N.X.hom]
    (i₀ i₁ : H ⟶ G) (hi : i₀ ≫ q = i₁ ≫ q)
    (hH : IsTorus H) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates (action n q hn i₀) e)

/-- An actual rational kernel point conjugating the two torus lifts. -/
def torusConjugator : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X :=
  RelativeRoot.torusCocycleConjugator (action n q hn i₀) e he hH
    (cocycle n q hn i₀ i₁ hi)

/-- The constructed point conjugates the actual homomorphisms. -/
theorem torusConjugator_conjugates :
    i₀ ≫ (G.innerIso (torusConjugator n q hn i₀ i₁ hi hH e he ≫ n.hom.hom)).hom =
      i₁ := by
  apply (cocycle_eq_coboundary_iff n q hn i₀ i₁ hi _).1
  exact RelativeRoot.cocycle_eq_coboundary_of_isTorus (action n q hn i₀) e he hH
    (cocycle n q hn i₀ i₁ hi)

/-- The conjugating point belongs to the actual kernel range on the base test. -/
theorem torusConjugator_mem_kernel :
    torusConjugator n q hn i₀ i₁ hi hH e he ≫ n.hom.hom ∈
      (SubgroupFunctor.range (kernelι q)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← hn]
  exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩

include hn hi hH he in
/-- Equal quotient maps from a torus are rationally conjugate through a kernel point
when the kernel conjugation action has supplied scalar-linear vector coordinates. -/
theorem subgroupConjugate_of_isTorus : SubgroupConjugate i₀ i₁ := by
  refine ⟨torusConjugator n q hn i₀ i₁ hi hH e he ≫ n.hom.hom, Iso.refl H, ?_⟩
  simpa only [Iso.refl_hom, Category.id_comp] using
    torusConjugator_conjugates n q hn i₀ i₁ hi hH e he

end Langlands.GroupScheme.QuotientHomCocycle

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [IsAffineHom N.X.hom]
    (i : H ⟶ G) (i' : H' ⟶ G) (f : H ≅ H')
    (hi : i ≫ q = (f.hom ≫ i') ≫ q)
    (hH : IsTorus H) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates
      (QuotientHomCocycle.action n q hn i) e)

include hn hi hH he

/-- A supplied quotient-compatible source isomorphism is realized by an actual
rational conjugator in the vector kernel. -/
theorem exists_kernel_conjugator_of_isTorus_iso :
    ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X,
      i ≫ (G.innerIso (v ≫ n.hom.hom)).hom = f.hom ≫ i' :=
  ⟨QuotientHomCocycle.torusConjugator n q hn i (f.hom ≫ i') hi hH e he,
    QuotientHomCocycle.torusConjugator_conjugates n q hn i (f.hom ≫ i') hi hH e he⟩

/-- Rational conjugacy of torus lifts permits the supplied distinct source groups. -/
theorem subgroupConjugate_of_isTorus_vector_kernel :
    SubgroupConjugate i i' := by
  obtain ⟨v, hv⟩ := exists_kernel_conjugator_of_isTorus_iso n q hn i i' f hi hH e he
  exact ⟨v ≫ n.hom.hom, f, hv⟩

end Langlands.GroupScheme
