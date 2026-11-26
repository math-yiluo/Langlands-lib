import Langlands.TraceFormula.AdelicRegularTwistedConjugacy
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistProof
import Langlands.TraceFormula.GeneralLinearWeilNormOne

/-! # Closedness of rational regular elliptic twisted orbits in Weil coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism Langlands.BaseChange

namespace Langlands.TraceFormula

local instance weilTwistedOrbitAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilTwistedOrbitSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section Transfer

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n : ℕ} {σ : L ≃ₐ[K] L}

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 2000 in
/-- The adelic matrix comparison intertwines twisted conjugation on norm-one points. -/
theorem generalLinearWeilNormOne_twistedConj
    (e : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGL L n)
    (he : ⇑e = cyclicWeilAdelicMap K L n)
    (x r : normOneSubgroup K Wₙ) :
    e (twistedConj Θₙ x r).val = twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv)
      (e x.val) (e r.val) := by
  have htw : e (adelicAut K (unitGaloisAut K L GLₙ σ) x.val) =
      AdelicGLTransport.adelicEquiv n σ.toRingEquiv (e x.val) := by
    let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
    calc
      _ = cyclicWeilAdelicMap K L n (adelicAut K (unitGaloisAut K L GLₙ σ) x.val) := congrFun he _
      _ = t (cyclicWeilAdelicMap K L n x.val) := (generalLinearWeilAdelicTwist K L n).2.1 σ x.val
      _ = _ := congrArg t (congrFun he x.val).symm
  change e (x.val⁻¹ * r.val * adelicAut K (unitGaloisAut K L GLₙ σ) x.val) =
    (e x.val)⁻¹ * e r.val * AdelicGLTransport.adelicEquiv n σ.toRingEquiv (e x.val)
  rw [map_mul, map_mul, map_inv, htw]

end Transfer

set_option maxHeartbeats 1800000 in
/-- The rational sigma-elliptic twisted orbit is closed in the actual norm-one group. -/
theorem generalLinearWeilTwistedClosedOrbit : GeneralLinearWeilTwistedClosedOrbitStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n r δ hr hδ
  obtain ⟨g, hg, hgell⟩ := hδ
  have hn : n ≠ 0 := by
    have hpos := hgell.2.natDegree_pos
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hpos
    exact hpos.ne'
  obtain ⟨e, he⟩ := (generalLinearWeilAdelicTwist K L n).1
  let e₁ := generalLinearWeilNormOneHomeomorph K L n e he
  let H := normOneSubgroup K Wₙ
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let O := Set.range fun x : AdelicGL.determinantNormOne L n =>
    twistedConj t x.val (AdelicGL.rational L n δ)
  have hO : IsClosed O := isClosed_range_adelic_normOne_twistedConj hcyc hn δ ⟨g, hg, hgell.1⟩
  have hr' : e r.val.val = AdelicGL.rational L n δ := (congrFun he _).trans hr
  have hpre : (Set.range fun x : H => twistedConj Θₙ x r.val) =
      (fun x : H => e x.val) ⁻¹' O := by
    apply Set.ext
    intro z
    change (∃ x : H, twistedConj Θₙ x r.val = z) ↔
      (∃ y : AdelicGL.determinantNormOne L n, twistedConj t y.val (AdelicGL.rational L n δ) = e z.val)
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨e₁ x, ?_⟩
      change twistedConj t (e x.val) (AdelicGL.rational L n δ) = e (twistedConj Θₙ x r.val).val
      rw [generalLinearWeilNormOne_twistedConj (σ := σ) e he, hr']
    · rintro ⟨y, hy⟩
      let x := e₁.symm y
      have hx : e x.val = y.val := congrArg Subtype.val (e₁.apply_symm_apply y)
      refine ⟨x, Subtype.ext (e.injective ?_)⟩
      rw [generalLinearWeilNormOne_twistedConj (σ := σ) e he, hr', hx]
      exact hy
  change IsClosed (Set.range fun x : H => twistedConj Θₙ x r.val)
  rw [hpre]
  exact hO.preimage (e.continuous.comp continuous_subtype_val)

end Langlands.TraceFormula
