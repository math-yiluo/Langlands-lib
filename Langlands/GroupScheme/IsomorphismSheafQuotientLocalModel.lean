import Langlands.GroupScheme.IsomorphismSheafQuotientDescent
import Langlands.GroupScheme.IsomorphismSchemeLocalChart
import Langlands.GroupScheme.IsomorphismSchemeActionTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Local outer quotient models before a global Isom scheme is supplied -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace LocalGroupIso.ActionQuotient

variable {S U : Scheme.{u}} {G H A : GroupScheme S}
    (b : U ⟶ S) (a : AutomorphicAction A G)

theorem act_baseChangeFamily {T : Over U}
    (e : LocalGroupIso G H ((Over.map b).obj T))
    (d : T ⟶ ((GroupScheme.baseChange b).obj A).X) :
    (act a (GroupScheme.baseChangePointsEquiv b A T d) e).baseChangeFamily b =
      act (a.baseChange b) d (e.baseChangeFamily b) := by
  simpa only [act, map_inv] using
    LocalGroupIso.baseChangeFamily_twist b e a d⁻¹

end LocalGroupIso.ActionQuotient

namespace GroupIsomorphismScheme

variable {S U : Scheme.{u}} {G H A : GroupScheme S}
    (b : U ⟶ S)
    (I : GroupIsomorphismScheme
      ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H))
    (a : AutomorphicAction A G)
    (O : OuterIsomorphismScheme I (a.baseChange b))

open LocalGroupIso LocalGroupIso.ActionQuotient

theorem localChart_refine_baseChangeFamily {T : Over S} {T' : Over U}
    (p : T ⟶ (Over.map b).obj I.parameter) (k : (Over.map b).obj T' ⟶ T)
    (p' : T' ⟶ I.parameter) (hp' : (Over.map b).map p' = k ≫ p) :
    (((I.localChart b).app (op T) ⟨p⟩).refine k).baseChangeFamily b =
      I.universalIso.refine p' := by
  rw [I.localChart_app, refine_comp, ← hp',
    ← fromBaseChangeFamily_refine, baseChangeFamily_fromBaseChangeFamily]

theorem localQuotient_orbit_iff {T : Over S}
    (p q : T ⟶ (Over.map b).obj I.parameter)
    (hpq : p ≫ I.localChartProjection b = q ≫ I.localChartProjection b) :
    p ≫ (Over.map b).map O.classMap = q ≫ (Over.map b).map O.classMap ↔
      ∃ d : T ⟶ A.X, act a d ((I.localChart b).app (op T) ⟨p⟩) =
        (I.localChart b).app (op T) ⟨q⟩ := by
  let T' := ChangeOfBase.test b p
  let k := ChangeOfBase.testIso b p
  let p₀ := ChangeOfBase.testPoint b p
  let q₀ : T' ⟶ I.parameter := Over.homMk q.left (by
    change q.left ≫ I.parameter.hom = p.left ≫ I.parameter.hom
    exact (congrArg (fun r => r.left) hpq).symm)
  have hp₀ : (Over.map b).map p₀ = k.hom ≫ p := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  have hq₀ : (Over.map b).map q₀ = k.hom ≫ q := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  let ep := (I.localChart b).app (op T) ⟨p⟩
  let eq := (I.localChart b).app (op T) ⟨q⟩
  have hep : (ep.refine k.hom).baseChangeFamily b = I.universalIso.refine p₀ :=
    I.localChart_refine_baseChangeFamily b p k.hom p₀ hp₀
  have heq : (eq.refine k.hom).baseChangeFamily b = I.universalIso.refine q₀ :=
    I.localChart_refine_baseChangeFamily b q k.hom q₀ hq₀
  have hact (d : T ⟶ A.X) (d₀ : T' ⟶ ((GroupScheme.baseChange b).obj A).X)
      (hd : k.hom ≫ d = GroupScheme.baseChangePointsEquiv b A T' d₀) :
      act a d ep = eq ↔
        lift d₀ p₀ ≫ I.actionHom (a.baseChange b) = q₀ := by
    have hbc : ((act a d ep).refine k.hom).baseChangeFamily b =
        act (a.baseChange b) d₀ (I.universalIso.refine p₀) := by
      rw [act_refine, hd, act_baseChangeFamily, hep]
    constructor
    · intro h
      have hf := congrArg (fun e : LocalGroupIso G H T =>
        (e.refine k.hom).baseChangeFamily b) h
      rw [hbc, heq] at hf
      apply (I.bijective T').1
      change I.universalIso.refine (lift d₀ p₀ ≫ I.actionHom (a.baseChange b)) =
        I.universalIso.refine q₀
      rw [I.refine_actionHom]
      exact hf
    · intro h
      have hf : act (a.baseChange b) d₀ (I.universalIso.refine p₀) =
          I.universalIso.refine q₀ := by
        change (I.universalIso.refine p₀).twist (a.baseChange b) d₀⁻¹ = _
        rw [← I.refine_actionHom, h]
      have hh : (act a d ep).refine k.hom = eq.refine k.hom := by
        apply (baseChangeEquiv b).injective
        change ((act a d ep).refine k.hom).baseChangeFamily b =
          (eq.refine k.hom).baseChangeFamily b
        rw [hbc, heq, hf]
      have hg := congrArg (fun e : LocalGroupIso G H ((Over.map b).obj T') =>
        e.refine k.inv) hh
      simpa only [refine_comp, k.inv_hom_id, refine_id] using hg
  have hclass :
      (p ≫ (Over.map b).map O.classMap = q ≫ (Over.map b).map O.classMap) ↔
        p₀ ≫ O.classMap = q₀ ≫ O.classMap := by
    constructor <;> intro h <;> apply Over.OverMorphism.ext
    · exact congrArg (fun r => r.left) h
    · exact congrArg (fun r => r.left) h
  constructor
  · intro h
    obtain ⟨d₀, hd₀, -⟩ := O.orbit T' p₀ q₀ (hclass.mp h)
    let d := k.inv ≫ GroupScheme.baseChangePointsEquiv b A T' d₀
    have hd : k.hom ≫ d = GroupScheme.baseChangePointsEquiv b A T' d₀ := by
      dsimp only [d]
      rw [k.hom_inv_id_assoc]
    exact ⟨d, (hact d d₀ hd).mpr hd₀⟩
  · rintro ⟨d, hd⟩
    let d₀ := (GroupScheme.baseChangePointsEquiv b A T').symm (k.hom ≫ d)
    have hd₀ : k.hom ≫ d = GroupScheme.baseChangePointsEquiv b A T' d₀ :=
      ((GroupScheme.baseChangePointsEquiv b A T').apply_symm_apply _).symm
    have h := (hact d d₀ hd₀).mp hd
    apply hclass.mpr
    rw [← h]
    exact (O.invariant T' d₀ p₀).symm

/-- A new-base outer quotient supplies the actual local quotient model on the old base. -/
def localQuotientPresentation
    [LocallyOfFinitePresentation O.classMap.left]
    [Etale O.parameter.hom] [IsSeparated O.parameter.hom] :
    LocalGroupIso.ActionQuotient.LocalPresentation (H := H) a (Over.mk b) where
  isomParameter := (Over.map b).obj I.parameter
  isomIso := I.localChartIso b
  isomProjection := I.localChartProjection b
  isomIso_snd := I.localChartIso_hom_snd b
  parameter := (Over.map b).obj O.parameter
  projection := Over.homMk O.parameter.hom rfl
  classMap := (Over.map b).map O.classMap
  comm := by
    apply Over.OverMorphism.ext
    exact Over.w O.classMap
  flat := O.flat
  locallyOfFinitePresentation := inferInstanceAs (LocallyOfFinitePresentation O.classMap.left)
  surjective := O.surjective
  separated := inferInstanceAs (IsSeparated O.parameter.hom)
  locallyQuasiFinite :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale O.parameter.hom
  locallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType O.parameter.hom)
  kernel T p q := by
    have hbase
        (h : p ≫ (Over.map b).map O.classMap = q ≫ (Over.map b).map O.classMap) :
        p ≫ I.localChartProjection b = q ≫ I.localChartProjection b := by
      apply Over.OverMorphism.ext
      have hh := congrArg (fun r => r.left ≫ O.parameter.hom) h
      change (p.left ≫ O.classMap.left) ≫ O.parameter.hom =
        (q.left ≫ O.classMap.left) ≫ O.parameter.hom at hh
      change p.left ≫ I.parameter.hom = q.left ≫ I.parameter.hom
      simpa only [Category.assoc, Over.w O.classMap] using hh
    constructor
    · intro h
      exact ⟨hbase h, (I.localQuotient_orbit_iff b a O p q (hbase h)).mp h⟩
    · rintro ⟨hpq, hact⟩
      exact (I.localQuotient_orbit_iff b a O p q hpq).mpr hact

/-- Smoothness of the local Isom parameter supplies finite presentation of its class map. -/
def localQuotientPresentationOfSmooth
    [Smooth I.parameter.hom] [Etale O.parameter.hom] [IsSeparated O.parameter.hom] :
    LocalGroupIso.ActionQuotient.LocalPresentation (H := H) a (Over.mk b) := by
  have : LocallyOfFinitePresentation (O.classMap.left ≫ O.parameter.hom) := by
    rw [Over.w O.classMap]
    infer_instance
  let : LocallyOfFinitePresentation O.classMap.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp
      O.classMap.left O.parameter.hom
  exact I.localQuotientPresentation b a O

end GroupIsomorphismScheme

end Langlands.GroupScheme
