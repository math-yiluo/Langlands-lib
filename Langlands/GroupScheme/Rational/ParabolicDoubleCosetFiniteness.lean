import Langlands.GroupScheme.Rational.ParabolicDoubleCosetStatement
import Langlands.GroupScheme.Rational.ParabolicContainsMinimalProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.BruhatPointReduction
import Langlands.GroupScheme.HomConjugacy

/-! # Finite parabolic double cosets from rational Bruhat covering -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Groups

variable {Γ : Type v} [Group Γ] (A H K : Subgroup Γ) (x y : Γ)
    (hH : ∀ a ∈ A, x⁻¹ * a * x ∈ H)
    (hK : ∀ a ∈ A, y⁻¹ * a * y ∈ K)

/-- Translate a double coset for a subgroup into a double coset for two
subgroups containing specified conjugates of it. -/
def conjugateContainingDoubleCosetMap :
    DoubleCoset.Quotient (A : Set Γ) A → DoubleCoset.Quotient (H : Set Γ) K :=
  Quotient.lift (fun g : Γ => DoubleCoset.mk H K (x⁻¹ * g * y)) (by
    intro a b hab
    obtain ⟨p, hp, q, hq, rfl⟩ := DoubleCoset.rel_iff.mp hab
    apply DoubleCoset.eq.mpr
    exact ⟨x⁻¹ * p * x, hH p hp, y⁻¹ * q * y, hK q hq, by group⟩)

/-- The translation map onto the larger double-coset quotient is surjective. -/
theorem conjugateContainingDoubleCosetMap_surjective :
    Function.Surjective (conjugateContainingDoubleCosetMap A H K x y hH hK) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro g
  refine ⟨DoubleCoset.mk A A (x * g * y⁻¹), ?_⟩
  change DoubleCoset.mk H K (x⁻¹ * (x * g * y⁻¹) * y) = DoubleCoset.mk H K g
  congr 1
  group

include x y hH hK in
/-- Finiteness descends when the two subgroups contain rational conjugates of
a subgroup with finite double-coset quotient. -/
theorem finite_doubleCosets_of_conjugate_containment
    [Finite (DoubleCoset.Quotient (A : Set Γ) A)] :
    Finite (DoubleCoset.Quotient (H : Set Γ) K) :=
  Finite.of_surjective _ (conjugateContainingDoubleCosetMap_surjective A H K x y hH hK)

end Groups

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational Bruhat covering gives finiteness of the dynamic minimal-parabolic
double-coset quotient, using the proved finiteness of the actual relative Weyl group. -/
theorem finite_rationalBruhatDoubleCosets
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hBruhat : HasRationalBruhatDecomposition i ν) :
    Finite (rationalBruhatDoubleCosets i ν) := by
  let := hG.finite_relativeWeylGroup i hi
  exact Finite.of_surjective _ ((hasRationalBruhatDecomposition_iff_bijective i ν).mp
    hBruhat).2

set_option maxHeartbeats 800000 in
/-- The finiteness clause for arbitrary actual rational parabolics follows from
the three stated structural propositions. Minimal containment and Weyl finiteness
are discharged by their published proofs. -/
theorem finite_parabolicDoubleCosets_of_bruhat_minimal_conjugacy
    (hBruhat : RationalBruhatStatement.{u})
    (hGeneric : GenericMinimalParabolicStatement.{u})
    (hConjugacy : MinimalParabolicConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    {P Q : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G) (q : Q ⟶ G)
    (hp : IsParabolicSubgroup p) (hq : IsParabolicSubgroup q) :
    Finite (DoubleCoset.Quotient
      ((rationalPoints.map p).range : Set (rationalPoints G))
      ((rationalPoints.map q).range : Set (rationalPoints G))) := by
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨T, i, hi⟩ := exists_maximalSplitTorus G
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  let F := Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)
  have hF : IsMinimalParabolicFunctor F := hGeneric k G hG T i hi ν hν
  obtain ⟨x, hx⟩ := exists_conjugate_containing_minimal_of_statements
    hConjugacy parabolicContainsMinimalStatement hG hF
      (show IsParabolicFunctor (SubgroupFunctor.range p) from ⟨P, p, hp, rfl⟩)
  obtain ⟨y, hy⟩ := exists_conjugate_containing_minimal_of_statements
    hConjugacy parabolicContainsMinimalStatement hG hF
      (show IsParabolicFunctor (SubgroupFunctor.range q) from ⟨Q, q, hq, rfl⟩)
  let A := F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let : Finite (DoubleCoset.Quotient (A : Set (rationalPoints G)) A) :=
    finite_rationalBruhatDoubleCosets hG i hi ν (hBruhat k G hG T i hi ν hν)
  apply finite_doubleCosets_of_conjugate_containment A
    (rationalPoints.map p).range (rationalPoints.map q).range x y
  · intro a ha
    have h := hx (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ha
    change a ≫ (G.innerIso x).inv.hom.hom ∈
      (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) at h
    rw [← innerIso_inv_hom, comp_innerIso_hom] at h
    simp only [constantPoint_self, inv_inv] at h
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp h
    exact ⟨b, hb⟩
  · intro a ha
    have h := hy (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ha
    change a ≫ (G.innerIso y).inv.hom.hom ∈
      (SubgroupFunctor.range q).carrier (Over.mk (𝟙 _)) at h
    rw [← innerIso_inv_hom, comp_innerIso_hom] at h
    simp only [constantPoint_self, inv_inv] at h
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp h
    exact ⟨b, hb⟩

end Langlands.GroupScheme
