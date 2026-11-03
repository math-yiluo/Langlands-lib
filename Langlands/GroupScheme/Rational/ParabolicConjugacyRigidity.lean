import Langlands.Group.TitsParabolicRigidity
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence
import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.HomConjugacy

/-! # From rational-point Tits transporters to all-test conjugacy rigidity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}
  {W : Type v} [Group W]
  {B N : Subgroup (Over.mk (𝟙 S) ⟶ G.X)} {π : N →* W} {Delta : Set W}

/-- A rational point conjugating one overgroup of `B` to another belongs to the
target subgroup functor at the base test scheme. -/
theorem mem_of_eq_comap_innerIso_of_tits
    (h : Langlands.Group.IsTitsSystem B N π Delta)
    {P Q : SubgroupFunctor G}
    (hBP : B ≤ P.carrier (Over.mk (𝟙 S)))
    (hBQ : B ≤ Q.carrier (Over.mk (𝟙 S)))
    (g : Over.mk (𝟙 S) ⟶ G.X) (heq : P = Q.comap (G.innerIso g).hom) :
    g ∈ Q.carrier (Over.mk (𝟙 S)) := by
  have hg : g⁻¹ ∈ Q.carrier (Over.mk (𝟙 S)) :=
    h.mem_of_conjugate_le hBQ g⁻¹ (by
      intro b hb
      have hbP := hBP hb
      rw [heq, mem_comap, comp_innerIso_hom, constantPoint_self] at hbP
      simpa only [inv_inv] using hbP)
  simpa only [inv_inv] using (Q.carrier _).inv_mem hg

/-- The actual conjugating rational point, now viewed as a point of the target
subgroup. Its underlying ambient rational point remains `g`. -/
def rationalConjugatingPointInSubgroup_of_tits
    (h : Langlands.Group.IsTitsSystem B N π Delta)
    {P Q : SubgroupFunctor G}
    (hBP : B ≤ P.carrier (Over.mk (𝟙 S)))
    (hBQ : B ≤ Q.carrier (Over.mk (𝟙 S)))
    (g : Over.mk (𝟙 S) ⟶ G.X) (heq : P = Q.comap (G.innerIso g).hom) :
    Q.carrier (Over.mk (𝟙 S)) :=
  ⟨g, mem_of_eq_comap_innerIso_of_tits h hBP hBQ g heq⟩

/-- Tits rigidity at base points yields equality of the full subgroup functors:
the rational conjugating point belongs to the target, so its restriction to
every test scheme normalizes that subgroup. -/
theorem eq_of_isRationallyConjugate_of_tits
    (h : Langlands.Group.IsTitsSystem B N π Delta)
    {P Q : SubgroupFunctor G}
    (hBP : B ≤ P.carrier (Over.mk (𝟙 S)))
    (hBQ : B ≤ Q.carrier (Over.mk (𝟙 S)))
    (hconj : P.IsRationallyConjugate Q) : P = Q := by
  obtain ⟨g, hg⟩ := hconj
  exact hg.trans
    (Q.comap_innerIso_hom_eq_of_mem (mem_of_eq_comap_innerIso_of_tits h hBP hBQ g hg))

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The two published structural statements imply all-test conjugacy rigidity
of standard parabolics, at their full field and universe scope. -/
theorem standardParabolic_eq_of_isRationallyConjugate_of_statements
    (hTS : RelativeTitsSystemStatement.{u}) (horder : StandardParabolicOrderStatement.{u})
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    letI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ J K : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
        (standardParabolic i ν J).IsRationallyConjugate (standardParabolic i ν K) →
          standardParabolic i ν J = standardParabolic i ν K := by
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  intro hν J K hJ hK hconj
  have hO := (horder k G hG T i hi ν hν).1
  have hminJ : standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
    ((hO ∅ J (Set.empty_subset _) hJ).1).mp (Set.empty_subset _)
  have hminK : standardParabolic i ν ∅ ≤ standardParabolic i ν K :=
    ((hO ∅ K (Set.empty_subset _) hK).1).mp (Set.empty_subset _)
  exact SubgroupFunctor.eq_of_isRationallyConjugate_of_tits
    (hTS k G hG T i hi ν hν).isTitsSystem
    (hminJ (Over.mk (𝟙 _))) (hminK (Over.mk (𝟙 _))) hconj

end Langlands.GroupScheme
