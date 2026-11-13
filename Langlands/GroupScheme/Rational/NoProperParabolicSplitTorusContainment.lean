import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.PseudoReductiveCentralCocharacterProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-! # Split tori without proper rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- In a connected reductive group without proper rational parabolics,
every homomorphism from a split torus is central on all test schemes. -/
theorem IsSplitTorus.isCentral_of_noProperParabolic
    (hS : IsSplitTorus S.toGrp) (hG : IsConnectedReductive G)
    (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      IsParabolicSubgroup p → IsIso p)
    (s : S.toGrp ⟶ G) : IsCentral s := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ν, hν⟩ := hS.exists_cocharacter_centralizer s
  let χ := CommGroupScheme.groupHom ν ≫ s
  let p := Dynamic.Affine.parabolicHom χ
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hpc : IsParabolicSubgroup p :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG p
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ) χ hp.2
  have : IsIso p := hpar _ p hpc
  have hfull : Dynamic.parabolic χ = ⊤ := by
    rw [← hp.2]
    calc
      SubgroupFunctor.range p =
          SubgroupFunctor.range ((asIso p).hom ≫ 𝟙 G) := by simp
      _ = SubgroupFunctor.range (𝟙 G) :=
        SubgroupFunctor.range_iso_comp (asIso p) (𝟙 G)
      _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id G).2
  apply (isCentral_iff_torusCentralizer_eq_top s).mpr
  rw [← hν]
  exact (pseudoReductiveCentralCocharacter k G hG.isPseudoReductive χ).mp hfull

/-- The central split-torus image factors through every maximal torus.
Closedness and maximal splitness of the original map pass to this factor. -/
theorem IsSplitTorus.exists_commFactor_of_noProperParabolic
    (hS : IsSplitTorus S.toGrp) (hG : IsConnectedReductive G)
    (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      IsParabolicSubgroup p → IsIso p)
    (s : S.toGrp ⟶ G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G}
    (ht : IsMaximalTorus t) :
    ∃ f : S ⟶ T,
      CommGroupScheme.groupHom f ≫ t = s ∧
      (IsClosedSubgroup s → IsClosedSubgroup (CommGroupScheme.groupHom f)) ∧
      (IsMaximalSplitTorus s → IsMaximalSplitTorus (CommGroupScheme.groupHom f)) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨g, hg⟩ :=
    (hS.isCentral_of_noProperParabolic hG hpar s).exists_factor_of_isMaximalTorus
      hS.isTorus ht
  let f : S ⟶ T := Additive.ofMul g
  have hf : CommGroupScheme.groupHom f ≫ t = s := hg
  refine ⟨f, hf, ?_, ?_⟩
  · intro hs
    exact IsClosedSubgroup.of_comp ht.2.1 (by rwa [hf])
  · intro hs
    exact IsMaximalSplitTorus.of_comp ht.2.1 (by rwa [hf])

/-- Every maximal torus contains the prescribed ambient maximal split torus,
and the factor is still maximal split in that maximal torus. -/
theorem IsMaximalSplitTorus.exists_commFactor_of_noProperParabolic
    {s : S.toGrp ⟶ G} (hs : IsMaximalSplitTorus s)
    (hG : IsConnectedReductive G)
    (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      IsParabolicSubgroup p → IsIso p)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G}
    (ht : IsMaximalTorus t) :
    IsCentral s ∧ ∃ f : S ⟶ T,
      CommGroupScheme.groupHom f ≫ t = s ∧
      IsMaximalSplitTorus (CommGroupScheme.groupHom f) := by
  obtain ⟨f, hf, -, hmax⟩ :=
    hs.1.1.exists_commFactor_of_noProperParabolic hG hpar s ht
  exact ⟨hs.1.1.isCentral_of_noProperParabolic hG hpar s, f, hf, hmax hs⟩

/-- The algebraic residue-torus step used after a Gamma-chamber reductive
quotient and its lack of proper rational parabolics have been supplied. -/
def NoProperParabolicSplitTorusContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      IsParabolicSubgroup p → IsIso p) →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
      IsSplitTorus S.toGrp →
      IsCentral s ∧
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsMaximalTorus t →
        ∃ f : S ⟶ T,
          CommGroupScheme.groupHom f ≫ t = s ∧
          (IsClosedSubgroup s → IsClosedSubgroup (CommGroupScheme.groupHom f)) ∧
          (IsMaximalSplitTorus s → IsMaximalSplitTorus (CommGroupScheme.groupHom f))

/-- Proof of the algebraic residue-torus containment statement. -/
theorem noProperParabolicSplitTorusContainment :
    NoProperParabolicSplitTorusContainmentStatement.{u} := by
  intro k _ G hG hpar S s hS
  exact ⟨hS.isCentral_of_noProperParabolic hG hpar s,
    fun _ _ ht => hS.exists_commFactor_of_noProperParabolic hG hpar s ht⟩

end Langlands.GroupScheme
