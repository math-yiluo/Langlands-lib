import Langlands.GroupScheme.Reductive.BorelCompatibleRootDatumComparison
import Langlands.GroupScheme.Reductive.AdjointChartTransport
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.FppfQuotientUniqueness
import Langlands.GroupScheme.Torus.HomFibreLocality
import Langlands.LinearAlgebra.RootDatumNegation

/-! # Actual simple-root quotient transitions for Borel-compatible field charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {k : Type u} [Field k] {I J : Type u} [Fintype I]
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)

/-- The base on the actual field character and cocharacter lattices. -/
def fieldBase : (fieldRealization k P).Base :=
  b.map (fieldRealizationEquiv k P)

@[simp] theorem fieldBase_support :
    (fieldBase (k := k) P b).support = b.support := by
  classical
  simp [fieldBase, fieldRealizationEquiv, SplitExistence.rootPairingMapEquiv]

@[simp] theorem fieldBase_isPos (a : J) :
    (fieldBase (k := k) P b).IsPos a ↔ b.IsPos a := by
  have h := Langlands.RootDatumNegation.height_map P b (fieldRealizationEquiv k P) a
  change (fieldBase (k := k) P b).height a = b.height a at h
  simp only [RootPairing.Base.isPos_iff, h]

end CoordinateRootDatum

section Field

variable {k : Type u} [Field k]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of k)) I' ⟶ H}
  (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hj : IsMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  (b : P.Base) (c : Q.Base)
  (f : G ≅ H)
  (t : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ≅
    splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I')
  (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
  (hP : haveI := hG.isAffineHom; IsRootDatumOf i (CoordinateRootDatum.fieldRealization k P))
  (hQ : haveI := hH.isAffineHom; IsRootDatumOf j (CoordinateRootDatum.fieldRealization k Q))
  (n : I → ℤ) (n' : I' → ℤ)
  (hn : ∀ a : J, ∑ l, P.root a l * n l ≠ 0)
  (hn' : ∀ a : J', ∑ l, Q.root a l * n' l ≠ 0)
  (hb : ∀ a : J, b.IsPos a ↔ 0 < ∑ l, P.root a l * n l)
  (hc : ∀ a : J', c.IsPos a ↔ 0 < ∑ l, Q.root a l * n' l)
  (hpar :
    (Dynamic.parabolic
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I n) ≫ i)).comap f.inv =
    Dynamic.parabolic
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I' n') ≫ j))

/-- Actual Borel-compatible group and coordinate torus isomorphisms over a
field induce a based coordinate comparison, including the all-test formula. -/
def basedCoordinateIsoOfBorelCompatibleFieldIso : BasedCoordinateIso i j P Q b c := by
  let S := Spec (CommRingCat.of k)
  let eP := CoordinateRootDatum.fieldRealizationEquiv k P
  let eQ := CoordinateRootDatum.fieldRealizationEquiv k Q
  let ν := splitTorus.exponentCocharacter S I n
  let ν' := splitTorus.exponentCocharacter S I' n'
  have hν : haveI := hG.isAffineHom; IsRegularCocharacter i ν := by
    intro α hα
    obtain ⟨a, rfl⟩ := hP.2.1.symm ▸ hα
    rw [CoordinateRootDatum.fieldRealization_root,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact hn a
  have hν' : haveI := hH.isAffineHom; IsRegularCocharacter j ν' := by
    intro α hα
    obtain ⟨a, rfl⟩ := hQ.2.1.symm ▸ hα
    rw [CoordinateRootDatum.fieldRealization_root,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact hn' a
  have hb' : ∀ a, (CoordinateRootDatum.fieldBase (k := k) P b).IsPos a ↔
      0 < latticePairing (splitTorus.commGroupScheme S I)
        ((CoordinateRootDatum.fieldRealization k P).root a) ν := by
    intro a
    rw [CoordinateRootDatum.fieldBase_isPos, CoordinateRootDatum.fieldRealization_root,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact hb a
  have hc' : ∀ a, (CoordinateRootDatum.fieldBase (k := k) Q c).IsPos a ↔
      0 < latticePairing (splitTorus.commGroupScheme S I')
        ((CoordinateRootDatum.fieldRealization k Q).root a) ν' := by
    intro a
    rw [CoordinateRootDatum.fieldBase_isPos, CoordinateRootDatum.fieldRealization_root,
      splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact hc a
  let d := borelCompatibleRootDatumComparison hG hH
    (isSplitTorus_splitTorus I) (isSplitTorus_splitTorus I') hi hj
    (CoordinateRootDatum.fieldBase (k := k) P b)
    (CoordinateRootDatum.fieldBase (k := k) Q c)
    f t hsq hP hQ ν ν' hν hν' hb' hc' hpar
  let e := CoordinateRootDatum.equivOfFieldRealizationEquiv k Q P d.rootEquiv
  have he (m : I' → ℤ) :
      splitTorus.exponentCharacter S I (e.weightMap m) =
        t.hom ≫ splitTorus.exponentCharacter S I' m := by
    have h : eP.weightEquiv (e.weightMap m) =
        d.rootEquiv.weightMap (eQ.weightMap m) := by
      change eP.weightEquiv (eP.weightEquiv.symm _) = _
      exact eP.weightEquiv.apply_symm_apply _
    rw [RootPairing.Equiv.weightEquiv_apply,
      CoordinateRootDatum.fieldRealizationEquiv_weightMap,
      CoordinateRootDatum.fieldRealizationEquiv_weightMap, d.characters] at h
    exact h
  refine
    { groupIso := f
      torusIso :=
        { hom := CommGroupScheme.groupHom t.hom
          inv := CommGroupScheme.groupHom t.inv
          hom_inv_id := congrArg Additive.toMul t.hom_inv_id
          inv_hom_id := congrArg Additive.toMul t.inv_hom_id }
      rootEquiv := e
      sourcePairing := ?_
      targetPairing := ?_
      simple_iff := ?_
      square := hsq
      characters := ?_ }
  · intro m v
    rw [← CoordinateRootDatum.fieldRealization_pairing k P, hP.1]
    exact splitTorus.latticePairing_exponentCharacter_exponentCocharacter I k m v
  · intro m v
    rw [← CoordinateRootDatum.fieldRealization_pairing k Q, hQ.1]
    exact splitTorus.latticePairing_exponentCharacter_exponentCocharacter I' k m v
  · intro a
    have h := d.simple_iff a
    rw [CoordinateRootDatum.fieldBase_support, CoordinateRootDatum.fieldBase_support] at h
    exact h.symm
  · intro U x m
    have h := congrArg (fun χ => Gm.pointsEquiv S U
      (x ≫ (CommGroupScheme.groupHom χ).hom.hom)) (he m)
    change Gm.pointsEquiv S U
      (x ≫ (CommGroupScheme.groupHom (splitTorus.exponentCharacter S I (e.weightMap m))).hom.hom) =
      Gm.pointsEquiv S U
        ((x ≫ (CommGroupScheme.groupHom t.hom).hom.hom) ≫
          (CommGroupScheme.groupHom (splitTorus.exponentCharacter S I' m)).hom.hom) at h
    rw [splitTorus.pointsEquiv_exponentCharacter,
      splitTorus.pointsEquiv_exponentCharacter] at h
    exact h.symm

end Field

namespace BasedCoordinateIso

variable {S : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme S}
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {b : P.Base} {c : Q.Base}
  (d : BasedCoordinateIso i j P Q b c)
  {D D' : GroupScheme S}
  {q : splitTorus S I ⟶ D} {q' : splitTorus S I' ⟶ D'}
  {F : SubgroupFunctor (splitTorus S I)}
  (hq : RelativeRoot.IsFppfQuotient F q)
  (a : D ⟶ D')
  (ha : q ≫ a = d.torusIso.hom ≫ q')
  (e : D ≅ splitTorus S b.support) (e' : D' ≅ splitTorus S c.support)
  (he : q ≫ e.hom = splitTorus.characterProjection S (fun r : b.support => P.root r))
  (he' : q' ≫ e'.hom = splitTorus.characterProjection S (fun r : c.support => Q.root r))

include hq ha he he' in
/-- Full fppf quotient cancellation determines the actual quotient map in
simple-root coordinates from the actual torus comparison. -/
theorem quotientChart_comp :
    a ≫ e'.hom = e.hom ≫ (splitTorus.coordinatePermutationIso S d.simpleRootEquiv).hom := by
  apply FppfQuotientComparison.hom_ext hq
  rw [← Category.assoc, ha, Category.assoc, he', d.simpleRootProjection_comp,
    ← he, Category.assoc]

include hq ha he he' in
/-- The actual quotient transition, expressed in the two charts, is exactly
the simple-root coordinate permutation. -/
theorem quotientChart_transition :
    e.inv ≫ a ≫ e'.hom =
      (splitTorus.coordinatePermutationIso S d.simpleRootEquiv).hom := by
  rw [d.quotientChart_comp hq a ha e e' he he', e.inv_hom_id_assoc]

end BasedCoordinateIso

end Langlands.GroupScheme
