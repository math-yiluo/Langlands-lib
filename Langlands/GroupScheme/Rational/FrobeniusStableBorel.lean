import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.FrobeniusConjugate

/-! # Frobenius-stable Borels from explicit Borel conjugacy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable (k Ω : Type u) [Field k] [Fintype k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

local instance : Smooth ((baseChange (algebraBaseMap k Ω)).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom (algebraBaseMap k Ω))
  infer_instance

local instance : IsAffineHom ((baseChange (algebraBaseMap k Ω)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k Ω))
  infer_instance

local instance : ConnectedSpace ((baseChange (algebraBaseMap k Ω)).obj G).X.left :=
  G.connectedSpace_baseChange_of_smooth_affine (algebraBaseMap k Ω)

variable {B : GroupScheme (Spec (CommRingCat.of Ω))}
  {i : B ⟶ (baseChange (algebraBaseMap k Ω)).obj G}

/-- The Lang-chosen conjugate of a Borel remains Borel. -/
theorem IsBorelSubgroup.frobeniusStableConjugate (hi : IsBorelSubgroup i)
    (hc : SubgroupConjugate
      ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map i ≫
        (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) i) :
    IsBorelSubgroup (frobeniusStableConjugate k Ω G i hc) :=
  hi.comp_iso _

/-- Explicit geometric Borel conjugacy applies to the canonically transported
Frobenius pullback of a supplied Borel. -/
theorem IsBorelSubgroup.subgroupConjugate_frobenius_of_borelConjugacy
    (hi : IsBorelSubgroup i) (hconj : BorelConjugacyStatement.{u}) :
    SubgroupConjugate
      ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map i ≫
        (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) i := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  let a := galoisBaseMap k Ω σ
  let e := descentBaseChangeIso (algebraBaseMap k Ω) a (galoisBaseMap_over k Ω σ) G
  have : IsIso a := isIso_SpecMap_iff.mpr σ.bijective
  have hFi : IsBorelSubgroup ((baseChange a).map i ≫ e.hom) :=
    (hi.baseChange_of_isIso a).comp_iso e
  exact (hconj Ω ((baseChange (algebraBaseMap k Ω)).obj G)).2 _ _ _ _ hFi hi

/-- A supplied geometric Borel has a Borel conjugate, with the same source,
whose explicit transported range agrees on every test scheme. -/
theorem IsBorelSubgroup.exists_frobeniusStableConjugate_range_of_borelConjugacy
    (hi : IsBorelSubgroup i) (hconj : BorelConjugacyStatement.{u}) :
    ∃ j : B ⟶ (baseChange (algebraBaseMap k Ω)).obj G,
      IsBorelSubgroup j ∧ SubgroupConjugate i j ∧
        SubgroupFunctor.range
          ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map j ≫
            (descentBaseChangeIso (algebraBaseMap k Ω)
              (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
              (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) =
          SubgroupFunctor.range j := by
  let hc := hi.subgroupConjugate_frobenius_of_borelConjugacy k Ω G hconj
  exact ⟨Langlands.GroupScheme.frobeniusStableConjugate k Ω G i hc,
    hi.frobeniusStableConjugate k Ω G hc,
    subgroupConjugate_frobeniusStableConjugate k Ω G i hc,
    frobeniusStableConjugate_range_eq k Ω G i hc⟩

/-- The supplied-Borel construction expressed by the all-test Galois action. -/
theorem IsBorelSubgroup.exists_frobeniusStableConjugate_of_borelConjugacy
    (hi : IsBorelSubgroup i) (hconj : BorelConjugacyStatement.{u}) :
    ∃ j : B ⟶ (baseChange (algebraBaseMap k Ω)).obj G,
      IsBorelSubgroup j ∧ SubgroupConjugate i j ∧
        SubgroupFunctor.galoisTransport k Ω G
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range j) =
          SubgroupFunctor.range j := by
  obtain ⟨j, hj, hc, hF⟩ :=
    hi.exists_frobeniusStableConjugate_range_of_borelConjugacy k Ω G hconj
  refine ⟨j, hj, hc, ?_⟩
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _
  rw [SubgroupFunctor.descentTransport_range]
  exact hF

/-- Borel conjugacy and Lang's theorem supply an actual geometric Borel fixed
by Frobenius on every test scheme. -/
theorem exists_frobeniusStableBorel_of_borelConjugacy
    (hconj : BorelConjugacyStatement.{u}) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of Ω)))
      (i : B ⟶ (baseChange (algebraBaseMap k Ω)).obj G),
      IsBorelSubgroup i ∧
        SubgroupFunctor.galoisTransport k Ω G
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
          SubgroupFunctor.range i := by
  obtain ⟨B, i, hi⟩ := (hconj Ω ((baseChange (algebraBaseMap k Ω)).obj G)).1
  obtain ⟨j, hj, _, hF⟩ :=
    hi.exists_frobeniusStableConjugate_of_borelConjugacy k Ω G hconj
  exact ⟨B, j, hj, hF⟩

/-- An actual geometric Borel inclusion together with its all-test
Frobenius invariance. -/
structure FrobeniusStableBorelData where
  obj : GroupScheme (Spec (CommRingCat.of Ω))
  inclusion : obj ⟶ (baseChange (algebraBaseMap k Ω)).obj G
  isBorel : IsBorelSubgroup inclusion
  frobeniusInvariant :
    SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range inclusion) =
      SubgroupFunctor.range inclusion

/-- Choose and retain an actual Frobenius-stable geometric Borel from
the explicit Borel-conjugacy statement. -/
def frobeniusStableBorelDataOfBorelConjugacy
    (hconj : BorelConjugacyStatement.{u}) : FrobeniusStableBorelData k Ω G :=
  Classical.choice <| by
    obtain ⟨B, i, hi, hF⟩ := exists_frobeniusStableBorel_of_borelConjugacy k Ω G hconj
    exact ⟨⟨B, i, hi, hF⟩⟩

end Langlands.GroupScheme
