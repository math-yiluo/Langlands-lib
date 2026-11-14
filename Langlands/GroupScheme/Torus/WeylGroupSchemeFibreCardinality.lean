import Langlands.GroupScheme.Reductive.RootDatumWeylProof
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Geometric Weyl cardinalities from full coordinate root data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual point Weyl quotient of a split maximal torus has the order of
any of its full root data. -/
theorem natCard_relativeWeylGroup_eq_rootDatum
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : @IsRootDatumOf k _ T G hG.isAffineHom J i P) :
    Nat.card (relativeWeylGroup i) = Nat.card P.weylGroup := by
  let := hG.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  obtain ⟨himage, hker⟩ := weylGroup k G hG T hT i hi J P hP
  calc
    Nat.card (relativeWeylGroup i) = Nat.card (weylImage i) := by
      unfold relativeWeylGroup
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (weylAction i)).toEquiv
    _ = Nat.card (P.weylGroup.map (RootPairing.Equiv.weightHom P)) := by rw [himage]
    _ = Nat.card P.weylGroup := by
      let f := (RootPairing.Equiv.weightHom P).domRestrict P.weylGroup
      have hf : Function.Injective f := fun a b h =>
        Subtype.ext (RootPairing.Equiv.weightHom_injective P h)
      have hc := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      simpa only [f, MonoidHom.domRestrict_range] using hc.symm

/-- An equivalence of full root data induces an equivalence of their Weyl
groups by conjugation. -/
def rootDatumWeylGroupEquiv
    {J J' M M' N N' : Type u} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N']
    {P : RootDatum J M N} {Q : RootDatum J' M' N'}
    (e : RootPairing.Equiv P Q) : P.weylGroup ≃* Q.weylGroup where
  toFun w := ⟨StarActionIndependence.conjAut e w,
    StarActionIndependence.conjAut_mem_weylGroup e w.property⟩
  invFun w := ⟨StarActionIndependence.conjAut e.symm w,
    StarActionIndependence.conjAut_mem_weylGroup e.symm w.property⟩
  left_inv w := by
    have hs : e.symm.weightEquiv = e.weightEquiv.symm := by ext; rfl
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro x
    change e.symm.weightEquiv (e.weightEquiv
      (w.val.weightEquiv (e.weightEquiv.symm (e.symm.weightEquiv.symm x)))) =
        w.val.weightEquiv x
    rw [hs]
    simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  right_inv w := by
    have hs : e.symm.weightEquiv = e.weightEquiv.symm := by ext; rfl
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro x
    change e.weightEquiv (e.symm.weightEquiv
      (w.val.weightEquiv (e.symm.weightEquiv.symm (e.weightEquiv.symm x)))) =
        w.val.weightEquiv x
    rw [hs]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  map_mul' w z := Subtype.ext (map_mul (StarActionIndependence.conjAut e) w.val z.val)

/-- Realizing a full coordinate root datum over a field leaves its Weyl
cardinality unchanged. -/
theorem CoordinateRootDatum.natCard_weylGroup_fieldRealization
    {I J : Type u} [Fintype I] (k : Type u) [Field k]
    (P : RootDatum J (I → ℤ) (I → ℤ)) :
    Nat.card (CoordinateRootDatum.fieldRealization k P).weylGroup =
      Nat.card P.weylGroup :=
  Nat.card_congr (rootDatumWeylGroupEquiv
    (CoordinateRootDatum.fieldRealizationEquiv k P)).toEquiv.symm

end Langlands.GroupScheme
