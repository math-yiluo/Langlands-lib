import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessStatement
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # Comparing opposite cocharacters with the same centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section CommonTorus

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Two commuting cocharacters factor through a common actual maximal split torus. -/
theorem exists_common_maximalSplitTorus_of_range_le_centralizer
    (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hpsi : SubgroupFunctor.range psi ≤ Dynamic.centralizer chi) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (zeta eta : cocharacterLattice T),
      IsMaximalSplitTorus i ∧
        CommGroupScheme.groupHom zeta ≫ i = chi ∧
        CommGroupScheme.groupHom eta ≫ i = psi := by
  let hab := fun (U : Over (Spec (CommRingCat.of k)))
    (x y : U ⟶ (Gm (Spec (CommRingCat.of k))).X) =>
      (Dynamic.commute_cocharacter_of_mem_centralizer chi
        (hpsi U (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)) x).symm
  obtain ⟨D, pi, j, hj, hpi, _⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus'
      (isSplitTorus_gm.tensor isSplitTorus_gm) (prodHom chi psi hab)
  obtain ⟨T, i, hi, f, hf⟩ := exists_maximalSplitTorus_extension G j hj
  refine ⟨T, i, Additive.ofMul (prodInl _ _ ≫ pi ≫ f),
    Additive.ofMul (prodInr _ _ ≫ pi ≫ f), hi, ?_, ?_⟩
  · change (prodInl _ _ ≫ pi ≫ f) ≫ i = chi
    rw [Category.assoc, Category.assoc, hf, hpi, prodInl_prodHom]
  · change (prodInr _ _ ≫ pi ≫ f) ≫ i = psi
    rw [Category.assoc, Category.assoc, hf, hpi, prodInr_prodHom]

/-- The actual simultaneous factorization of two commuting cocharacters through
a maximal split torus, including their two lattice cocharacters. -/
structure CommonMaximalSplitTorusFactorization
    (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  first : cocharacterLattice torus
  second : cocharacterLattice torus
  isMaximal : IsMaximalSplitTorus inclusion
  first_comp : CommGroupScheme.groupHom first ≫ inclusion = chi
  second_comp : CommGroupScheme.groupHom second ≫ inclusion = psi

/-- Choose a common maximal split-torus factorization from centralizing ranges. -/
def commonMaximalSplitTorusFactorization
    (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hpsi : SubgroupFunctor.range psi ≤ Dynamic.centralizer chi) :
    CommonMaximalSplitTorusFactorization chi psi :=
  Classical.choice (by
    obtain ⟨T, i, zeta, eta, hi, hzeta, heta⟩ :=
      exists_common_maximalSplitTorus_of_range_le_centralizer chi psi hpsi
    exact ⟨⟨T, i, zeta, eta, hi, hzeta, heta⟩⟩)

end CommonTorus

section RootSigns

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)

include hT

/-- A rational parabolic intersection equal to the first centralizer excludes
an actual root positive on both cocharacters. -/
theorem not_both_positive_of_rational_parabolic_inf_eq_centralizer
    (hpoints :
      (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) ⊓
          (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).carrier (Over.mk (𝟙 _)) =
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)))
    {alpha : characterLattice T} (halpha : alpha ∈ relativeRoots i)
    (hzeta : 0 < latticePairing T alpha zeta) :
    ¬ 0 < latticePairing T alpha eta := by
  intro heta
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i halpha
  have hxz := RelativeRoot.subgroup_le_dynamicUnipotent i zeta hzeta _ hx
  have hxe := RelativeRoot.subgroup_le_dynamicUnipotent i eta heta _ hx
  have hxc : x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    rw [← hpoints]
    exact ⟨Dynamic.unipotent_le_parabolic _ _ hxz,
      Dynamic.unipotent_le_parabolic _ _ hxe⟩
  exact hx1 (Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent
    (CommGroupScheme.groupHom zeta ≫ i)
    (fun _ _ _ _ h h' => h.unique _ h') hxc hxz)

/-- Equal centralizers and the rational intersection condition force opposite
root signs when the actual root support is stable under negation. -/
theorem opposite_root_signs_of_rational_parabolic_inf_eq_centralizer
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hpoints :
      (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) ⊓
          (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).carrier (Over.mk (𝟙 _)) =
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∀ alpha ∈ relativeRoots i,
      (0 ≤ latticePairing T alpha eta ↔ latticePairing T alpha zeta ≤ 0) ∧
        (0 < latticePairing T alpha eta ↔ latticePairing T alpha zeta < 0) := by
  intro alpha halpha
  have hzero : latticePairing T alpha eta = 0 ↔ latticePairing T alpha zeta = 0 := by
    constructor
    · exact root_zero_imp_of_dynamicCentralizer_rationalPoints_le hT i eta zeta
        (by rw [hZ]) halpha
    · exact root_zero_imp_of_dynamicCentralizer_rationalPoints_le hT i zeta eta
        (by rw [hZ]) halpha
  have hpos := not_both_positive_of_rational_parabolic_inf_eq_centralizer
    hT i zeta eta hpoints halpha
  have hminus := not_both_positive_of_rational_parabolic_inf_eq_centralizer
    hT i zeta eta hpoints (hneg alpha halpha)
  simp only [map_neg, LinearMap.neg_apply, neg_pos] at hminus
  omega

end RootSigns

/-- The exact opposite-parabolic uniqueness statement follows from unconditional
negation stability of the actual relative roots. -/
theorem oppositeDynamicParabolicUniqueness_of_relativeRootNegation
    (hneg : RelativeRootNegationStatement.{u}) :
    OppositeDynamicParabolicUniquenessStatement.{u} := by
  intro k _ G hG chi psi hZ hpoints
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have hcomm : SubgroupFunctor.range psi ≤ Dynamic.centralizer chi := by
    rw [← hZ]
    exact Dynamic.range_le_centralizer psi
  obtain ⟨T, i, zeta, eta, hi, hzeta, heta⟩ :=
    commonMaximalSplitTorusFactorization chi psi hcomm
  rw [← hzeta, ← heta] at hZ hpoints ⊢
  rw [← groupHom_neg_comp_eq_oppositeCocharacter i zeta]
  have hsign := opposite_root_signs_of_rational_parabolic_inf_eq_centralizer
    hi.1.1 i zeta eta (hneg k G hG T i hi) hZ hpoints
  constructor
  · apply le_antisymm
    · apply (relativeRootSignInclusions k G hG T i hi eta (-zeta)).1.mpr
      intro alpha halpha h
      simpa only [map_neg, neg_nonneg] using (hsign alpha halpha).1.mp h
    · apply (relativeRootSignInclusions k G hG T i hi (-zeta) eta).1.mpr
      intro alpha halpha h
      exact (hsign alpha halpha).1.mpr (by simpa only [map_neg, neg_nonneg] using h)
  · apply le_antisymm
    · apply (relativeRootSignInclusions k G hG T i hi eta (-zeta)).2
      intro alpha halpha h
      simpa only [map_neg, neg_pos] using (hsign alpha halpha).2.mp h
    · apply (relativeRootSignInclusions k G hG T i hi (-zeta) eta).2
      intro alpha halpha h
      exact (hsign alpha halpha).2.mpr (by simpa only [map_neg, neg_pos] using h)

end Langlands.GroupScheme
