import Langlands.GroupScheme.Rational.HighestWeightRootFixed
import Langlands.GroupScheme.Rational.GenericTorusCocharacter

/-! # Rank-one nonvanishing from actual highest-weight data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial Classical

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus)

/-- The original character-space equation gives the actual natural-power
cocharacter action whenever its lattice pairing is the supplied natural number. -/
theorem affineAction_cocharacter_of_mem_weightSpace
    (nu : cocharacterLattice p.torus) (m : ℕ)
    (hm : latticePairing p.torus lam nu = (m : ℤ))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (u : kˣ) :
    ρ.affineAction (CommAlgCat.of k k)
      ((Gm.affinePointsEquiv (R := CommRingCat.of k)
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom).symm u ≫
        (CommGroupScheme.groupHom nu).hom.hom ≫ p.inclusion.hom.hom) v =
      (u : k) ^ m • v := by
  let := p.isSplitTorus.isAffineHom
  let t := (Gm.affinePointsEquiv (R := CommRingCat.of k)
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom).symm u
  have h := characterSpace_affine hv (CommAlgCat.of k k)
    (t ≫ (CommGroupScheme.groupHom nu).hom.hom)
  change (ρ.restrict p.inclusion).affineAction (CommAlgCat.of k k)
      (t ≫ (CommGroupScheme.groupHom nu).hom.hom) v =
    (Lie.characterValue lam (t ≫ (CommGroupScheme.groupHom nu).hom.hom) : k) • v at h
  rw [affineAction_restrict, CoordinateWeights.characterValue_cocharacter, hm,
    zpow_natCast] at h
  let e := Gm.affinePointsEquiv (R := CommRingCat.of k)
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom
  change ρ.affineAction (CommAlgCat.of k k)
      ((t ≫ (CommGroupScheme.groupHom nu).hom.hom) ≫ p.inclusion.hom.hom) v =
    (e t).val ^ m • v at h
  simpa only [e, t, MulEquiv.apply_symm_apply, Category.assoc] using h

variable [Fintype p.rootIndex] (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hρ : p.IsHighestWeight ρ lam)

/-- The normalized binomial pairings on every nonzero vector of the original
highest-character space, for the two supplied actual additive root maps. -/
def HasHighestWeightRankOnePairing
    (xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) (m : ℕ) : Prop :=
  ∀ (v : n → k), v ∈ p.representationWeightSpace ρ lam → v ≠ 0 →
    ∃ ell : Module.Dual k (n → k), ell v = 1 ∧
      ∀ a b : ℕ,
        ell (dividedPower (ρ.restrict xp) a (dividedPower (ρ.restrict xm) b v)) =
          if b = a then (m.choose a : k) else 0

include hρ

/-- Every supplied nonzero highest vector has a normalized functional that
kills all positive lowering coefficients and is fixed at every lowering point. -/
theorem exists_normalized_lowering_functional
    {xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    {α : characterLattice p.torus}
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-α))
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    ∃ ell : Module.Dual k (n → k), ell v = 1 ∧
      (∀ m : ℕ, 0 < m → ell.comp (dividedPower (ρ.restrict xm) m) = 0) ∧
      ∀ (t : k) (w : n → k),
        ell ((ρ.restrict xm).affineAction (CommAlgCat.of k k)
          (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
            (CommAlgCat.of k k) (fun _ => t)) w) = ell w := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv0
  let ell := f.comp (p.highestWeightProjector ρ lam)
  have hell : ∀ m : ℕ, 0 < m →
      ell.comp (dividedPower (ρ.restrict xm) m) = 0 := by
    intro m hm
    rw [show ell = f.comp (p.highestWeightProjector ρ lam) from rfl,
      LinearMap.comp_assoc,
      p.highestWeightProjector_comp_dividedPower_eq_zero ρ lam hspan hρ hxm hα hm,
      LinearMap.comp_zero]
  refine ⟨ell, ?_, hell, FunctionalRecovery.functional_affineAction_eq _ ell hell⟩
  change f (p.highestWeightProjector ρ lam v) = 1
  rw [p.highestWeightProjector_of_mem ρ lam hv, ite_eq_left rfl, hf]

variable {xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    {α : characterLattice p.torus}
    (hxp : VectorGroup.IsTorusEquivariant p.inclusion xp α)
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-α))
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    (nu : cocharacterLattice p.torus) (m : ℕ)
    (hm : latticePairing p.torus lam nu = (m : ℤ))
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)),
      RootCell.RelationOver p.inclusion nu xp xm Z)

include hxp hxm hα hm hcell

/-- For every original nonzero highest vector, the actual root-cell relation
has all diagonal and off-diagonal binomial coefficient pairings. -/
theorem exists_highestWeight_rankOne_pairing [Infinite k]
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    ∃ ell : Module.Dual k (n → k), ell v = 1 ∧
      ∀ a b : ℕ,
        ell (dividedPower (ρ.restrict xp) a (dividedPower (ρ.restrict xm) b v)) =
          if b = a then (m.choose a : k) else 0 := by
  obtain ⟨ell, hnorm, _, hell⟩ :=
    p.exists_normalized_lowering_functional ρ lam hspan hρ hxm hα hv hv0
  have hfixed := p.isFixedVector_of_mem_highestWeight ρ lam hspan hρ hxp hα hv
  have hfixed' (s : k) : (ρ.restrict xp).affineAction (CommAlgCat.of k k)
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k) (fun _ => s)) v = v := by
    exact hfixed.affine (CommAlgCat.of k k) _
  refine ⟨ell, hnorm, ?_⟩
  exact RankOneRootCoefficient.dividedPower_pairing ell v m ρ p.inclusion nu xp xm
    hcell hfixed' hell (p.affineAction_cocharacter_of_mem_weightSpace ρ lam nu m hm hv)
    hnorm

/-- The supplied actual highest-weight and root-cell data satisfy the normalized
binomial pairing condition. -/
theorem hasHighestWeightRankOnePairing [Infinite k] :
    p.HasHighestWeightRankOnePairing ρ lam xp xm m := by
  intro v hv hv0
  exact p.exists_highestWeight_rankOne_pairing ρ lam hspan hρ
    hxp hxm hα nu m hm hcell hv hv0

/-- A nonzero binomial coefficient forces nonzero lowering on every original
nonzero highest vector; all fixed-data premises are derived from highest weight. -/
theorem highestWeight_dividedPower_ne_zero [Infinite k]
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0)
    (a : ℕ) (ha : (m.choose a : k) ≠ 0) :
    dividedPower (ρ.restrict xm) a v ≠ 0 := by
  obtain ⟨ell, _, hpair⟩ :=
    p.exists_highestWeight_rankOne_pairing ρ lam hspan hρ hxp hxm hα nu m hm hcell hv hv0
  intro hz
  have he := hpair a a
  rw [hz, map_zero, map_zero, ite_eq_left rfl] at he
  exact ha he.symm

omit hm in
/-- At a Steinberg coroot weight every retained actual lowering coefficient
acts nontrivially on any original nonzero highest vector. -/
theorem highestWeight_steinberg_dividedPower_ne_zero [Infinite k]
    (q : ℕ) [Fact q.Prime] [CharP k q] (r : ℕ)
    (hweight : latticePairing p.torus lam nu = (q ^ r - 1 : ℕ))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0)
    (a : ℕ) (ha : a ≤ q ^ r - 1) :
    dividedPower (ρ.restrict xm) a v ≠ 0 :=
  p.highestWeight_dividedPower_ne_zero ρ lam hspan hρ hxp hxm hα nu
    (q ^ r - 1) hweight hcell hv hv0 a
    (RankOneSteinberg.choose_steinberg_cast_ne_zero q r a ha)

end Langlands.GroupScheme.SplitPinning
