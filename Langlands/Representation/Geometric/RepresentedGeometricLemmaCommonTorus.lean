import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # The original common split torus of a represented geometric-lemma datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- A cocharacter centralized by the image of a maximal split torus factors
through that same torus. -/
theorem IsMaximalSplitTorus.exists_cocharacter_factor_of_centralizing
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range i ≤ Dynamic.centralizer χ) :
    ∃ ξ : cocharacterLattice T, CommGroupScheme.groupHom ξ ≫ i = χ := by
  obtain ⟨f, hf⟩ := hi.exists_factor_of_commute isSplitTorus_gm χ (by
    intro W x y
    have hy := hχ W (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hy
    exact (hy W (𝟙 W) x).symm)
  exact ⟨Additive.ofMul f, hf⟩

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

/-- The supplied source common torus, transported by the original algebraic
conjugation isomorphism to the actual target common Levi. -/
abbrev targetCommonTorusHom : D.torus.toGrp ⟶ D.L' := D.leviTorus

/-- The ambient target torus is the original source torus conjugated by z⁻¹. -/
theorem targetCommonTorusHom_comp :
    D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q =
      (D.t ≫ D.l' ≫ D.p' ≫ l ≫ p) ≫ (G.innerIso z).inv :=
  D.leviTorus_comp

/-- The target common torus remains a maximal split torus in the ambient G. -/
theorem targetCommonTorus_isMaximalSplitTorus_ambient :
    IsMaximalSplitTorus (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q) :=
  D.isMaximalSplitTorus_leviTorus_comp

/-- The original source common torus is maximal split in the original source
common Levi as well as in G. -/
theorem sourceCommonTorus_isMaximalSplitTorus : IsMaximalSplitTorus D.t := by
  have hc : IsClosedSubgroup (D.l' ≫ D.p' ≫ l ≫ p) :=
    D.hl'.isClosedSubgroup.comp (D.hp'.isClosedSubgroup.comp
      (hl.isClosedSubgroup.comp hp.isClosedSubgroup))
  apply IsMaximalSplitTorus.of_comp hc
  simpa only [Category.assoc] using D.isMaximalSplitTorus

/-- The transported common torus is maximal split in the actual target
common Levi, with no choice of a new torus or conjugation map. -/
theorem targetCommonTorus_isMaximalSplitTorus :
    IsMaximalSplitTorus D.targetCommonTorusHom := by
  exact D.sourceCommonTorus_isMaximalSplitTorus.comp_iso D.φ.symm

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
