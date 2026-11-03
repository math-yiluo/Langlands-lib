import Langlands.GroupScheme.Rational.TorusVectorLiftConjugacy

/-! # Lifting rational torus conjugacy through a scalar-linear vector kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientConjugacyLift

variable {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [IsAffineHom N.X.hom]
    (i : H ⟶ G) (i' : H' ⟶ G) (f : H ≅ H')
    (hH : IsTorus H) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates
      (QuotientHomCocycle.action n q hn i) e)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X)
    (hx : (i ≫ q) ≫ (Q.innerIso x).hom = f.hom ≫ (i' ≫ q))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ≫ q.hom.hom = x)

include hx hg in
/-- Conjugating the second lift backwards by the supplied lift of the quotient
conjugator makes its quotient map equal to the original first map. -/
theorem quotient_eq :
    i ≫ q = ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom) ≫ q := by
  calc
    i ≫ q = ((i ≫ q) ≫ (Q.innerIso x).hom) ≫ (Q.innerIso x).inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (f.hom ≫ (i' ≫ q)) ≫ (Q.innerIso x).inv := by rw [hx]
    _ = ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom) ≫ q := by
      simp only [Category.assoc]
      rw [innerIso_hom_comp, GrpObj.inv_comp, hg, innerIso_inv_hom]

/-- The rational kernel correction for the chosen lift of a quotient conjugator. -/
def kernelCorrection : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X :=
  QuotientHomCocycle.torusConjugator n q hn i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH e he

/-- The actual rational conjugator obtained by correcting the supplied lift. -/
def conjugator : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  g * (kernelCorrection n q hn i i' f hH e he x hx g hg ≫ n.hom.hom)

/-- The correction lies in the kernel, so the constructed conjugator lifts the
original specified quotient point. -/
theorem conjugator_comp :
    conjugator n q hn i i' f hH e he x hx g hg ≫ q.hom.hom = x := by
  have hv := QuotientHomCocycle.torusConjugator_mem_kernel n q hn i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH e he
  rw [mem_range_kernelι_iff] at hv
  rw [conjugator, MonObj.mul_comp, kernelCorrection, hv, mul_one, hg]

/-- The constructed point conjugates the original maps with precisely the
source isomorphism supplied by the quotient conjugacy. -/
theorem conjugator_conjugates :
    i ≫ (G.innerIso (conjugator n q hn i i' f hH e he x hx g hg)).hom =
      f.hom ≫ i' := by
  rw [conjugator, innerIso_mul_hom, ← Category.assoc]
  have hv := QuotientHomCocycle.torusConjugator_conjugates n q hn i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH e he
  change (i ≫ (G.innerIso
    (QuotientHomCocycle.torusConjugator n q hn i
      ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
      (quotient_eq q i i' f x hx g hg) hH e he ≫ n.hom.hom)).hom) ≫
        (G.innerIso g).hom = f.hom ≫ i'
  rw [hv, innerIso_inv_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

include hn hH he hx hg in
/-- A specified liftable quotient conjugacy yields rational subgroup conjugacy. -/
theorem subgroupConjugate : SubgroupConjugate i i' :=
  ⟨conjugator n q hn i i' f hH e he x hx g hg, f,
    conjugator_conjugates n q hn i i' f hH e he x hx g hg⟩

end Langlands.GroupScheme.QuotientConjugacyLift

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [IsAffineHom N.X.hom]
    (i : H ⟶ G) (i' : H' ⟶ G) (hH : IsTorus H) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates
      (QuotientHomCocycle.action n q hn i) e)

include hn hH he in
/-- For a quotient map surjective on rational points, conjugacy of maps from a
torus is equivalent to conjugacy after the quotient, under the supplied
scalar-linear vector-kernel coordinates. -/
theorem subgroupConjugate_iff_quotient_of_isTorus_vector_kernel
    (hq : Function.Surjective
      (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => g ≫ q.hom.hom)) :
    SubgroupConjugate i i' ↔ SubgroupConjugate (i ≫ q) (i' ≫ q) := by
  constructor
  · exact fun h => h.postcomp q
  · rintro ⟨x, f, hx⟩
    obtain ⟨g, hg⟩ := hq x
    exact QuotientConjugacyLift.subgroupConjugate
      n q hn i i' f hH e he x hx g hg

end Langlands.GroupScheme
