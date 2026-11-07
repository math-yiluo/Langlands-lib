import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.MatrixRepresentation.AdditiveInvariantSubspaces
import Langlands.GroupScheme.MatrixRepresentation.RankOneRootCoefficient
import Langlands.GroupScheme.Reductive.HighestWeightExtremal

/-! # Fixed highest vectors and highest-coordinate functionals -/

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

/-- The existing actual torus-character projector onto the supplied weight. -/
def highestWeightProjector : Module.End k (n → k) :=
  letI := p.isSplitTorus.isAffineHom
  (ρ.restrict p.inclusion).characterProjector
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)

theorem highestWeightProjector_of_mem {mu : characterLattice p.torus}
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ mu) :
    p.highestWeightProjector ρ lam v = if mu = lam then v else 0 := by
  classical
  let := p.isSplitTorus.isAffineHom
  simpa only [highestWeightProjector, EmbeddingLike.apply_eq_iff_eq] using
    (ρ.restrict p.inclusion).characterProjector_of_mem
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam)
      ((rationalCharacters.equivCharacterLattice p.torus).symm mu) hv

variable [Fintype p.rootIndex] (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hρ : p.IsHighestWeight ρ lam)

include hρ

/-- All occurring weights are at most the highest weight on polarized rho. -/
theorem pairing_le_highestWeight {mu : characterLattice p.torus}
    (hmu : p.representationWeightSpace ρ mu ≠ ⊥) :
    p.rootDatum.toLinearMap mu
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≤
      p.rootDatum.toLinearMap lam
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) := by
  by_cases he : lam = mu
  · rw [he]
  · have hp := p.pairing_polarization_rho_pos_of_mem_positiveRootMonoid hspan
      (hρ.2.2.2 mu hmu) (sub_ne_zero.mpr he)
    simpa only [map_sub, LinearMap.sub_apply, sub_nonneg] using le_of_lt hp

/-- A weight strictly above the highest weight on polarized rho cannot occur. -/
theorem weightSpace_eq_bot_of_pairing_gt {mu : characterLattice p.torus}
    (hgt : p.rootDatum.toLinearMap lam
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) <
      p.rootDatum.toLinearMap mu
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan))) :
    p.representationWeightSpace ρ mu = ⊥ := by
  by_contra hn
  exact (not_lt_of_ge (p.pairing_le_highestWeight ρ lam hspan hρ hn)) hgt

variable {x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    {α : characterLattice p.torus}

/-- A positive-weight additive coefficient of positive degree kills every
vector of the highest weight. -/
theorem dividedPower_eq_zero_on_highestWeight
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x α)
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam)
    {m : ℕ} (hm : 0 < m) :
    dividedPower (ρ.restrict x) m v = 0 := by
  let f := p.rootDatum.toLinearMap.flip
    (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan))
  have hpos : 0 < (m : ℤ) * f α := mul_pos (Int.natCast_pos.mpr hm) hα
  have hgt : f lam < f (lam + m • α) := by
    rw [map_add, map_nsmul, nsmul_eq_mul]
    omega
  have hbot := p.weightSpace_eq_bot_of_pairing_gt ρ lam hspan hρ hgt
  have hw := p.dividedPower_mem_representationWeightSpace_of_equivariant hx ρ m hv
  rwa [hbot, Submodule.mem_bot] at hw

/-- The highest vector is fixed by the entire supplied positive-weight
additive action on every relative scheme test. -/
theorem isFixedVector_of_mem_highestWeight
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x α)
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) :
    (ρ.restrict x).IsFixedVector v := by
  apply (AdditiveInvariantSubspaces.mem_fixedSubmodule_iff_isFixedVector _ v).mp
  apply (AdditiveFixedVectors.mem_fixedSubmodule _ v).mpr
  exact fun m hm => p.dividedPower_eq_zero_on_highestWeight ρ lam hspan hρ hx hα hv hm

/-- Every positive-degree lowering coefficient has zero highest-weight
projection on the entire original representation space. -/
theorem highestWeightProjector_comp_dividedPower_eq_zero
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x (-α))
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    {m : ℕ} (hm : 0 < m) :
    (p.highestWeightProjector ρ lam).comp (dividedPower (ρ.restrict x) m) = 0 := by
  let f := p.rootDatum.toLinearMap.flip
    (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan))
  have hpos : 0 < (m : ℤ) * f α := mul_pos (Int.natCast_pos.mpr hm) hα
  have hker : (⨆ mu, p.representationWeightSpace ρ mu) ≤
      LinearMap.ker ((p.highestWeightProjector ρ lam).comp
        (dividedPower (ρ.restrict x) m)) := by
    refine iSup_le fun mu => ?_
    intro v hv
    by_cases hbot : p.representationWeightSpace ρ mu = ⊥
    · have hz : v = 0 := by simpa only [hbot, Submodule.mem_bot] using hv
      simp [hz]
    have hle : f mu ≤ f lam := p.pairing_le_highestWeight ρ lam hspan hρ hbot
    have hlt : f (mu + m • (-α)) < f lam := by
      rw [map_add, map_nsmul, map_neg, nsmul_eq_mul]
      nlinarith
    have hne : mu + m • (-α) ≠ lam := by
      intro he
      rw [he] at hlt
      exact lt_irrefl _ hlt
    change p.highestWeightProjector ρ lam (dividedPower (ρ.restrict x) m v) = 0
    rw [p.highestWeightProjector_of_mem ρ lam
      (p.dividedPower_mem_representationWeightSpace_of_equivariant hx ρ m hv),
      ite_eq_right hne]
  rw [hρ.2.1] at hker
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)

omit hρ

namespace FunctionalRecovery

open MatrixRepresentation.RankOneRootCoefficient

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (E : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
    (ell : Module.Dual k (n → k))

/-- A functional killing every positive original coefficient is constant on
the polynomial orbit, over finite as well as infinite fields. -/
theorem coefficientPolynomial_eq_C
    (hell : ∀ m : ℕ, 0 < m → ell.comp (dividedPower E m) = 0) (w : n → k) :
    coefficientPolynomial (univariateMatrix E) ell w = Polynomial.C (ell w) := by
  apply Polynomial.ext
  intro m
  rw [coefficientPolynomial_univariate_coeff]
  by_cases hm : m = 0
  · subst m
    simp
  · have h := congrArg (fun L : Module.Dual k (n → k) => L w)
      (hell m (Nat.pos_of_ne_zero hm))
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Polynomial.coeff_C, hm,
      ite_false] using h

/-- The same coefficient criterion implies actual base-field functional
invariance for every scalar parameter. -/
theorem functional_affineAction_eq
    (hell : ∀ m : ℕ, 0 < m → ell.comp (dividedPower E m) = 0)
    (t : k) (w : n → k) :
    ell (E.affineAction (CommAlgCat.of k k)
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k) (fun _ => t)) w) = ell w := by
  have he := univariateMatrix_aeval E (CommAlgCat.of k k) t
  change (univariateMatrix E).map
    (Polynomial.aeval (R := k) (A := k) t : k[X] → k) = _ at he
  rw [Polynomial.coe_aeval_eq_eval] at he
  rw [affineAction_apply, ← he, ← coefficientPolynomial_eval,
    coefficientPolynomial_eq_C E ell hell, Polynomial.eval_C]

end FunctionalRecovery

include hρ

/-- A normalized highest vector and a highest-coordinate functional can be
chosen so that the vector is raising-fixed on all relative tests and the
functional is lowering-fixed at every base-field point. -/
theorem exists_highestWeight_fixed_pair
    {xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (hxp : VectorGroup.IsTorusEquivariant p.inclusion xp α)
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-α))
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan))) :
    ∃ (v : n → k) (ell : Module.Dual k (n → k)),
      v ∈ p.representationWeightSpace ρ lam ∧ ell v = 1 ∧
      (ρ.restrict xp).IsFixedVector v ∧
      ∀ (t : k) (w : n → k),
        ell ((ρ.restrict xm).affineAction (CommAlgCat.of k k)
          (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
            (CommAlgCat.of k k) (fun _ => t)) w) = ell w := by
  classical
  obtain ⟨b, mu, a, hb, ha, _⟩ := p.exists_highestWeight_characterBasis hspan ρ hρ
  let P := p.highestWeightProjector ρ lam
  let ell := (b.coord a).comp P
  have hv : b a ∈ p.representationWeightSpace ρ lam := ha ▸ hb a
  refine ⟨b a, ell, hv, ?_,
    p.isFixedVector_of_mem_highestWeight ρ lam hspan hρ hxp hα hv, ?_⟩
  · change b.coord a (p.highestWeightProjector ρ lam (b a)) = 1
    rw [p.highestWeightProjector_of_mem ρ lam hv, ite_eq_left rfl]
    simp
  · apply FunctionalRecovery.functional_affineAction_eq
    intro m hm
    change ((b.coord a).comp P).comp (dividedPower (ρ.restrict xm) m) = 0
    rw [LinearMap.comp_assoc,
      p.highestWeightProjector_comp_dividedPower_eq_zero ρ lam hspan hρ hxm hα hm,
      LinearMap.comp_zero]

end Langlands.GroupScheme.SplitPinning
