import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization

/-! # Actual standard-Levi split components contain root annihilators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- Actual split components of a standard Levi contain the real selected-root
annihilator, provided the simple roots are finite and a standard cocharacter
exists. These structural premises are retained explicitly. -/
def StandardLeviSplitContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    ∀ (ν : cocharacterLattice T) (J : Set (characterLattice T)),
      (simpleRelativeRoots i ν).Finite →
      (∃ zeta, IsStandardCocharacter i ν J zeta) →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j → (standardLevi i ν J).IsRepresentedBy j →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
      IsSplitComponent a →
      Module.Finite ℝ (V A) ∧
      ∃ f : A ⟶ T,
        CommGroupScheme.groupHom f ≫ i = a ≫ j ∧
        IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
        Function.Injective (cocharacterMapReal f) ∧
        rootAnnihilator T J ≤ (cocharacterMapReal f).range

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice T) (J : Set (characterLattice T))
  {j : L ⟶ G} (hjc : IsClosedSubgroup j)
  (hj : (standardLevi i ν J).IsRepresentedBy j)
  {a : A.toGrp ⟶ L} (ha : IsSplitComponent a)

include hi hjc hj ha

/-- Every supplied split component of a closed standard Levi has an actual
closed factor through the ambient maximal split torus, injective on real
cocharacters. No root-system premise or Levi reductivity is required. -/
theorem IsSplitComponent.exists_commFactor_standardLevi :
    ∃ f : A ⟶ T,
      CommGroupScheme.groupHom f ≫ i = a ≫ j ∧
      IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
      Function.Injective (cocharacterMapReal f) := by
  have : IsAffineHom L.X.hom := hjc.isAffineHom_source
  let t := standardLeviTorusFactor i ν J hj
  have ht : t ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have htmax : IsMaximalSplitTorus t :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  obtain ⟨f, hf, hfc, hfinj⟩ := ha.exists_commFactor_of_isMaximalSplitTorus htmax
  refine ⟨f, ?_, hfc, hfinj⟩
  rw [← ht, ← Category.assoc, hf]

/-- A compatible actual split-component map contains the real annihilator of
selected roots, under the finite-root and standard-cocharacter premises. -/
theorem IsSplitComponent.rootAnnihilator_le_range_standardLevi
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = a ≫ j) :
    rootAnnihilator T J ≤ (cocharacterMapReal f).range := by
  have : IsAffineHom L.X.hom := hjc.isAffineHom_source
  let t := standardLeviTorusFactor i ν J hj
  have ht : t ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have htmax : IsMaximalSplitTorus t :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  have : Mono t.hom.hom.left := htmax.1.2.mono
  have : Mono j.hom.hom := hj.1
  have hft : CommGroupScheme.groupHom f ≫ t = a := by
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    exact congrArg (fun q => q.hom.hom)
      (show (CommGroupScheme.groupHom f ≫ t) ≫ j = a ≫ j by
        rw [Category.assoc, ht, hf])
  have hJ : J ⊆ simpleRelativeRoots i ν := hexists.choose_spec.1
  have : Finite J := (hfinite.subset hJ).to_subtype
  apply ha.rootAnnihilator_le_range_cocharacterMapReal f hft J
  intro zeta hzeta
  exact isCentral_standardLeviTorusFactor_of_annihilates i ν J hj
    hfinite hexists zeta hzeta

/-- The actual closed component embedding and reverse annihilator containment,
under exactly the finite-root and standard-cocharacter premises. -/
theorem IsSplitComponent.exists_commFactor_standardLevi_containing_annihilator
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    Module.Finite ℝ (V A) ∧
    ∃ f : A ⟶ T,
      CommGroupScheme.groupHom f ≫ i = a ≫ j ∧
      IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
      Function.Injective (cocharacterMapReal f) ∧
      rootAnnihilator T J ≤ (cocharacterMapReal f).range := by
  obtain ⟨f, hf, hfc, hfinj⟩ := ha.exists_commFactor_standardLevi hi ν J hjc hj
  exact ⟨ha.1.1.1.finite_realCocharacterSpace, f, hf, hfc, hfinj,
    ha.rootAnnihilator_le_range_standardLevi hi ν J hjc hj hfinite hexists f hf⟩

variable [Mono i.hom.hom.left]

/-- A relative-root-system realization supplies exactly the finite-root and
standard-cocharacter premises needed for actual reverse real containment. -/
theorem IsSplitComponent.rootAnnihilator_le_range_standardLevi_of_rootSystem
    (hR : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = a ≫ j) :
    rootAnnihilator T J ≤ (cocharacterMapReal f).range := by
  exact ha.rootAnnihilator_le_range_standardLevi hi ν J hjc hj
    (hR.finite_simpleRelativeRoots i hi.1.1 ν)
    (hR.exists_standardCocharacter i ν hi.1.1 hν J hJ) f hf

omit hi hjc hj ha in
/-- The packaged supporting statement, with every displayed premise retained. -/
theorem standardLeviSplitContainment : StandardLeviSplitContainmentStatement.{u} := by
  intro k _ G _ T i hi ν J hfinite hexists L j hjc hj A a ha
  exact ha.exists_commFactor_standardLevi_containing_annihilator hi ν J hjc hj
    hfinite hexists

end Langlands.GroupScheme
