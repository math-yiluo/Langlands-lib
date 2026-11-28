import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistence
import Langlands.GroupScheme.Rational.NumberFieldCocycleRealTriviality

/-! # Moving one component of a factored cocycle through a twist -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {F L : Type u} [Field F] [Field L] [Algebra F L]

local notation "U" => Over.mk (algebraBaseMap F L)
local notation "BL" => GroupScheme.baseChange (algebraBaseMap F L)

variable {G H J T : GroupScheme (Spec (CommRingCat.of F))}

private def restrictionChart (e : LocalGroupIso H J U) (i : T ⟶ H) :
    LocalGroupHom T J U where
  toFun a := (e.toFun a).toMonoidHom.comp ((pointsMap i).app (Opposite.op _)).hom
  naturality r a z := by
    change e.toFun (r ≫ a) ((r ≫ z) ≫ i.hom.hom) = r ≫ e.toFun a (z ≫ i.hom.hom)
    rw [Category.assoc, e.naturality]

private def conjugateChart (e : LocalGroupIso H J U) (j : H ⟶ G) (g : U ⟶ G.X) :
    LocalGroupHom J G U where
  toFun a := (MulAut.conj (a ≫ g)⁻¹).toMonoidHom.comp
    (((pointsMap j).app (Opposite.op _)).hom.comp (e.toFun a).symm.toMonoidHom)
  naturality r a z := by
    change ((r ≫ a) ≫ g)⁻¹ * ((e.toFun (r ≫ a)).symm (r ≫ z) ≫ j.hom.hom) *
      (((r ≫ a) ≫ g)⁻¹)⁻¹ = r ≫ ((a ≫ g)⁻¹ * ((e.toFun a).symm z ≫ j.hom.hom) *
        (((a ≫ g)⁻¹)⁻¹))
    have h := e.symm.naturality r a z
    change (e.toFun (r ≫ a)).symm (r ≫ z) = r ≫ (e.toFun a).symm z at h
    simp only [Category.assoc, h, inv_inv, MonObj.comp_mul, GrpObj.comp_inv]

private theorem conjugateChart_apply (e : LocalGroupIso H J U) (j : H ⟶ G)
    (g : U ⟶ G.X) {Z : Over (Spec (CommRingCat.of F))} (a : Z ⟶ U) (z : Z ⟶ J.X) :
    (conjugateChart e j g).toFun a z =
      (a ≫ g)⁻¹ * ((e.toFun a).symm z ≫ j.hom.hom) * (a ≫ g) := by
  change (a ≫ g)⁻¹ * ((e.toFun a).symm z ≫ j.hom.hom) * ((a ≫ g)⁻¹)⁻¹ = _
  rw [inv_inv]

variable [FiniteDimensional F L] [IsGalois F L] [NumberField F]
  {A : GroupScheme (Spec (CommRingCat.of F))}

/-- Suppose a cocycle is the product of values from two coefficient groups. The
second acts on the first through conjugation, and fixes the subgroup supplying
the first cocycle. If the second cocycle trivializes in the ambient group,
the first can be transported to a form of its coefficient group. A Hasse
kernel for those forms then trivializes the product. -/
theorem isTrivial_of_component_cocycles_with_firstMap
    (i : T ⟶ H) (j : H ⟶ G) (k : A ⟶ G) (hH : IsSimplyConnected H)
    (act : AutomorphicAction A H)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ A.X) (y : Z ⟶ H.X),
      act.act x y ≫ j.hom.hom = (x ≫ k.hom.hom) * (y ≫ j.hom.hom) * (x ≫ k.hom.hom)⁻¹)
    (hfixed : ∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ A.X) (z : Z ⟶ T.X),
      act.act x (z ≫ i.hom.hom) = z ≫ i.hom.hom)
    (ξ : Cocycle G U) (α : Cocycle T U) (β : Cocycle A U)
    (hkernel : ∀ J : GroupScheme (Spec (CommRingCat.of F)),
      ∀ e : LocalGroupIso H J U, e.HasDiscrepancy act β →
      ∀ ℓ : T ⟶ J,
        (BL).map ℓ = (BL).map i ≫ e.toBaseChangeIso.hom →
      ∀ δ : Cocycle J U, δ.LocallyTrivial → δ.IsTrivial)
    (hα : α.RealLocallyTrivial) (hβ : (β.map k).IsTrivial)
    (hprod : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ U),
      ξ.toFun a b = ((α.toFun a b ≫ i.hom.hom) ≫ j.hom.hom) *
        (β.toFun a b ≫ k.hom.hom)) : ξ.IsTrivial := by
  obtain ⟨hU₁, hU₂, hU₃⟩ := fieldExtension_fpqc F L
  let : Surjective (U).hom := hU₁
  let : Flat (U).hom := hU₂
  let : QuasiCompact (U).hom := hU₃
  obtain ⟨J, e, _, he⟩ := finiteGaloisTwistExistence F L A H
    hH.isSemisimple.isConnectedReductive.isAffineHom act β
  let E := restrictionChart e i
  have hE : E.IsIndependent := by
    intro Z a b z
    change e.toFun a (z ≫ i.hom.hom) = e.toFun b (z ≫ i.hom.hom)
    simpa only [hfixed] using he a b (z ≫ i.hom.hom)
  let ℓ := E.descend hE
  have hℓ {Z : Over (Spec (CommRingCat.of F))} (a : Z ⟶ U) (z : Z ⟶ T.X) :
      z ≫ ℓ.hom.hom = e.toFun a (z ≫ i.hom.hom) := by
    rw [E.comp_descend]
    have h := E.comp_value hE (𝟙 Z) a z
    simp only [Category.id_comp] at h
    change E.value hE z = e.toFun a (z ≫ i.hom.hom) at h
    exact h
  have hℓL : (BL).map ℓ = (BL).map i ≫ e.toBaseChangeIso.hom := by
    apply hom_ext_points
    intro Z z
    apply (baseChangePointsEquiv (algebraBaseMap F L) J Z).injective
    rw [baseChangePointsEquiv_comp, Grp.comp_hom_hom, ← Category.assoc]
    let a := @LocalGroupIso.baseChangeTestPoint _ U Z
    let z' := baseChangePointsEquiv (algebraBaseMap F L) T Z z
    have hi := baseChangePointsEquiv_comp (algebraBaseMap F L) i Z z
    have he' := e.toBaseChangeIso_hom_points Z (z ≫ ((BL).map i).hom.hom)
    exact (hℓ a z').trans ((congrArg (e.toFun a) hi.symm).trans he'.symm)
  obtain ⟨g, hg⟩ := hβ
  let C := conjugateChart e j g
  have hC : C.IsIndependent := by
    intro Z a b z
    let y := (e.toFun b).symm z
    have hy : (e.toFun a).symm z = act.act (β.toFun a b) y := by
      apply (e.toFun a).injective
      rw [MulEquiv.apply_symm_apply, he a b y]
      exact (e.toFun b).apply_symm_apply z |>.symm
    change (conjugateChart e j g).toFun a z = (conjugateChart e j g).toFun b z
    rw [conjugateChart_apply, conjugateChart_apply]
    have hb : β.toFun a b ≫ k.hom.hom = (a ≫ g) * (b ≫ g)⁻¹ := hg a b
    dsimp only [y] at hy
    rw [hy, hact, hb]
    group
  let m := C.descend hC
  have hm {Z : Over (Spec (CommRingCat.of F))} (a : Z ⟶ U) (z : Z ⟶ J.X) :
      z ≫ m.hom.hom = (a ≫ g)⁻¹ * ((e.toFun a).symm z ≫ j.hom.hom) * (a ≫ g) := by
    rw [C.comp_descend]
    have h := C.comp_value hC (𝟙 Z) a z
    simp only [Category.id_comp] at h
    rw [h]
    exact conjugateChart_apply e j g a z
  let eL := e.toBaseChangeIso
  have hJ := (isSimplyConnected_fieldExtension_iff (K := L) J).mp
    (IsSimplyConnected.of_iso eL.symm (isSimplyConnectedFieldExtension F L H hH))
  have htriv := hkernel J e he ℓ hℓL (α.map ℓ)
    ((hα.map ℓ).locallyTrivial_of_isSimplyConnected hJ)
  obtain ⟨f, hf⟩ := htriv.map m
  refine IsTrivial.of_twist (f := g) ⟨f, fun a b => ?_⟩
  rw [← hf a b]
  change (a ≫ g)⁻¹ * ξ.toFun a b * (b ≫ g) = (α.toFun a b ≫ ℓ.hom.hom) ≫ m.hom.hom
  have hb : β.toFun a b ≫ k.hom.hom = (a ≫ g) * (b ≫ g)⁻¹ := hg a b
  rw [hm a, hℓ a, MulEquiv.symm_apply_apply, hprod a b, hb]
  group

/-- A Hasse kernel for all the transported coefficient forms suffices for
the componentwise reduction. -/
theorem isTrivial_of_component_cocycles
    (i : T ⟶ H) (j : H ⟶ G) (k : A ⟶ G) (hH : IsSimplyConnected H)
    (act : AutomorphicAction A H)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ A.X) (y : Z ⟶ H.X),
      act.act x y ≫ j.hom.hom = (x ≫ k.hom.hom) * (y ≫ j.hom.hom) * (x ≫ k.hom.hom)⁻¹)
    (hfixed : ∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ A.X) (z : Z ⟶ T.X),
      act.act x (z ≫ i.hom.hom) = z ≫ i.hom.hom)
    (ξ : Cocycle G U) (α : Cocycle T U) (β : Cocycle A U)
    (hkernel : ∀ J : GroupScheme (Spec (CommRingCat.of F)),
      ∀ e : LocalGroupIso H J U, e.HasDiscrepancy act β →
      ∀ δ : Cocycle J U, δ.LocallyTrivial → δ.IsTrivial)
    (hα : α.RealLocallyTrivial) (hβ : (β.map k).IsTrivial)
    (hprod : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ U),
      ξ.toFun a b = ((α.toFun a b ≫ i.hom.hom) ≫ j.hom.hom) *
        (β.toFun a b ≫ k.hom.hom)) : ξ.IsTrivial :=
  isTrivial_of_component_cocycles_with_firstMap i j k hH act hact hfixed ξ α β
    (fun J e he _ _ => hkernel J e he) hα hβ hprod

end Langlands.GroupScheme.Cocycle
