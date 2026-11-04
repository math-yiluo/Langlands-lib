import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Derived.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.ConjugacyStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly

/-! # Derived maximal split tori inside an ambient maximal split torus, from conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]

/-- Every maximal split torus of `G` contains, through a closed homomorphism of commutative
group schemes, a maximal split torus of the source of `d`, compatibly with `d`. -/
def MaximalSplitToriContainSubgroupTori {G D : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ G) : Prop :=
  ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    ∃ (S_D : CommGroupScheme (Spec (CommRingCat.of k))) (j : S_D.toGrp ⟶ D)
      (e : S_D ⟶ S),
      IsMaximalSplitTorus j ∧
      IsClosedSubgroup (CommGroupScheme.groupHom e) ∧
      j ≫ d = CommGroupScheme.groupHom e ≫ i

/-- Let `d : D ⟶ G` be a closed subgroup of an affine locally finite type group over a field,
representing a normal subgroup functor. If the maximal split tori of `G` are conjugate by
rational points, then every maximal split torus `i : S ⟶ G` contains, through a closed
homomorphism `e`, a maximal split torus `j` of `D` with `j ≫ d = e ≫ i`. -/
theorem SubgroupFunctor.IsRepresentedBy.maximalSplitToriContainSubgroupTori_of_conjugate
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {F : SubgroupFunctor G} {d : D ⟶ G} (hr : F.IsRepresentedBy d) (hdc : IsClosedSubgroup d)
    (hn : F.IsNormal) (hconj : MaximalSplitToriAreConjugate G) :
    MaximalSplitToriContainSubgroupTori d := by
  intro S i hi
  have hdci : IsClosedImmersion d.hom.hom.left := hdc
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  have : LocallyOfFiniteType D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  obtain ⟨T, j₀, hj₀⟩ := exists_maximalSplitTorus D
  obtain ⟨M, m, hm, f, hf⟩ := exists_maximalSplitTorus_extension G (j₀ ≫ d) (hj₀.1.comp hdc)
  obtain ⟨g, c, hc⟩ := hconj M S m i hm hi
  let φ := hr.conjugateIso hn g
  have hcomm : (j₀ ≫ φ.hom) ≫ d = CommGroupScheme.groupHom
      (Additive.ofMul (f ≫ c.hom) : T ⟶ S) ≫ i := by
    change (j₀ ≫ φ.hom) ≫ d = (f ≫ c.hom) ≫ i
    rw [Category.assoc, hr.conjugateIso_hom_comp, ← Category.assoc, ← hf, Category.assoc,
      hc, Category.assoc]
  refine ⟨T, j₀ ≫ φ.hom, Additive.ofMul (f ≫ c.hom), hj₀.comp_iso φ, ?_, hcomm⟩
  apply IsClosedSubgroup.of_comp hi.1.2
  rw [← hcomm]
  exact (hj₀.comp_iso φ).1.2.comp hdc

/-- The same conclusion for an actual inclusion exhibiting the scheme-theoretic derived
subgroup, whose range is normal. -/
theorem IsDerivedSubgroup.maximalSplitToriContainSubgroupTori_of_conjugate
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (hconj : MaximalSplitToriAreConjugate G) :
    MaximalSplitToriContainSubgroupTori d :=
  hd.isRepresentedBy.maximalSplitToriContainSubgroupTori_of_conjugate hd.1
    (derivedSubgroup_isNormal G) hconj

end Field

/-- The published derived statement is the fixed-group property for every exhibited derived
subgroup of every connected reductive field group. -/
theorem derivedMaximalSplitTorusStatement_iff :
    DerivedMaximalSplitTorusStatement.{u} ↔
      ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
        IsConnectedReductive G → IsDerivedSubgroup d →
        MaximalSplitToriContainSubgroupTori d :=
  Iff.rfl

/-- Conjugacy of maximal split tori in every connected reductive field group implies the
derived maximal split torus statement. -/
theorem derivedMaximalSplitTorus_of_conjugate
    (hconj : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → MaximalSplitToriAreConjugate G) :
    DerivedMaximalSplitTorusStatement.{u} := by
  rw [derivedMaximalSplitTorusStatement_iff]
  intro k _ G D d hG hd
  have := hG.smooth
  have := hG.isAffineHom
  exact hd.maximalSplitToriContainSubgroupTori_of_conjugate (hconj k G hG)

/-- Rational conjugacy of maximal split tori in smooth connected affine field groups
(Borel–Tits) implies the derived maximal split torus statement. -/
theorem derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    DerivedMaximalSplitTorusStatement.{u} :=
  derivedMaximalSplitTorus_of_conjugate fun k _ G hG => by
    have := hG.smooth
    have := hG.isAffineHom
    have := hG.connectedSpace
    exact hconj k G

/-- The reductive conjugacy statement, through its conjugacy conjunct, implies the derived
maximal split torus statement. -/
theorem derivedMaximalSplitTorus_of_maximalSplitTorusConjugacy
    (hconj : MaximalSplitTorusConjugacyStatement.{u}) :
    DerivedMaximalSplitTorusStatement.{u} :=
  derivedMaximalSplitTorus_of_conjugate fun k _ G hG => (hconj k G hG).1

end Langlands.GroupScheme
