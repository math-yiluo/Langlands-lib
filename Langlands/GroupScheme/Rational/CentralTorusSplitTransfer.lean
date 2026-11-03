import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.Lattice

/-! # Split-part transfer through the central torus of a represented centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  {T Z B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A closed torus whose centralizer is represented by `M` factors through any
closed commutative subgroup of `M` containing all its closed central tori. If that
subgroup also factors through `T`, the original torus factors through `T`. -/
theorem exists_factor_through_torus_of_centralizer_center
    (t : T.toGrp ⟶ G) (i : Z.toGrp ⟶ T.toGrp)
    (z : Z.toGrp ⟶ M) (hz : IsClosedSubgroup z)
    (hzgreatest : ∀ (C : CommGroupScheme (Spec (CommRingCat.of k)))
      (c : C.toGrp ⟶ M), IsTorus C.toGrp → IsClosedSubgroup c → IsCentral c →
        SubgroupFunctor.range c ≤ SubgroupFunctor.range z)
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (hcomm : i ≫ t = z ≫ j)
    (b : B.toGrp ⟶ G) (hb : IsTorus B.toGrp) (hbc : IsClosedSubgroup b)
    (hrep : (torusCentralizer b).IsRepresentedBy j) :
    ∃ bT : B.toGrp ⟶ T.toGrp, bT ≫ t = b := by
  have : IsClosedImmersion z.hom.hom.left := hz
  have hzrep : (SubgroupFunctor.range z).IsRepresentedBy z :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let c := torusCentralizerFactor b hrep
  have hc : IsClosedSubgroup c :=
    isClosedSubgroup_torusCentralizerFactor b hrep hj hbc
  have hcentral : IsCentral c := isCentral_torusCentralizerFactor b hrep
  let d := hzrep.factorHom c (hzgreatest B c hb hc hcentral)
  have hd : d ≫ z = c := hzrep.factorHom_comp c _
  refine ⟨d ≫ i, ?_⟩
  calc
    (d ≫ i) ≫ t = d ≫ (z ≫ j) := by rw [Category.assoc, hcomm]
    _ = c ≫ j := by rw [← Category.assoc, hd]
    _ = b := torusCentralizerFactor_comp b hrep

/-- The central-torus factor supplies the geometric map required by the ambient
split-part transfer. All existence and centralizer-representation data remain
explicit hypotheses. -/
theorem IsMaximalSplitTorus.ambient_transfer_of_centralizer_center
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ T.toGrp} (ha : IsMaximalSplitTorus a)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (i : Z.toGrp ⟶ T.toGrp) (z : Z.toGrp ⟶ M) (hz : IsClosedSubgroup z)
    (hzgreatest : ∀ (C : CommGroupScheme (Spec (CommRingCat.of k)))
      (c : C.toGrp ⟶ M), IsTorus C.toGrp → IsClosedSubgroup c → IsCentral c →
        SubgroupFunctor.range c ≤ SubgroupFunctor.range z)
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (hcomm : i ≫ t = z ≫ j)
    (b : B.toGrp ⟶ G) (hb : IsMaximalSplitTorus b)
    (hrep : (torusCentralizer b).IsRepresentedBy j)
    {F : SubgroupFunctor G} (hF : SubgroupFunctor.range j ≤ F) :
    IsMaximalSplitTorus (a ≫ t) ∧ torusCentralizer (a ≫ t) ≤ F := by
  obtain ⟨bT, hbT⟩ := exists_factor_through_torus_of_centralizer_center
    t i z hz hzgreatest j hj hcomm b hb.1.1.isTorus hb.1.2 hrep
  apply ha.ambient_transfer_of_isClosedSubgroup t ht bT
  · rwa [hbT]
  · rw [hbT, ← hrep.2]
    exact hF

/-- Conditional transfer through a closed commutative subgroup of a represented
centralizer containing all its closed central tori, uniformly over all fields. -/
def CentralTorusSplitTransferStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (M : GroupScheme (Spec (CommRingCat.of k)))
    (T Z A B : CommGroupScheme (Spec (CommRingCat.of k)))
    (a : A.toGrp ⟶ T.toGrp), IsMaximalSplitTorus a →
    ∀ (t : T.toGrp ⟶ G), IsClosedSubgroup t →
    ∀ (i : Z.toGrp ⟶ T.toGrp) (z : Z.toGrp ⟶ M), IsClosedSubgroup z →
      (∀ (C : CommGroupScheme (Spec (CommRingCat.of k)))
        (c : C.toGrp ⟶ M), IsTorus C.toGrp → IsClosedSubgroup c → IsCentral c →
          SubgroupFunctor.range c ≤ SubgroupFunctor.range z) →
      ∀ (j : M ⟶ G), IsClosedSubgroup j → i ≫ t = z ≫ j →
      ∀ (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        (torusCentralizer b).IsRepresentedBy j →
        ∀ F : SubgroupFunctor G, SubgroupFunctor.range j ≤ F →
          IsMaximalSplitTorus (a ≫ t) ∧ torusCentralizer (a ≫ t) ≤ F

/-- The uniform conditional central-torus transfer. -/
theorem centralTorusSplitTransfer : CentralTorusSplitTransferStatement.{u} := by
  intro k _ G _ _ M T Z A B a ha t ht i z hz hzgreatest j hj hcomm b hb hrep F hF
  exact ha.ambient_transfer_of_centralizer_center
    t ht i z hz hzgreatest j hj hcomm b hb hrep hF

end Langlands.GroupScheme
