import Langlands.GroupScheme.RepresentedPresheafTorsor
import Langlands.GroupScheme.RelativeLevi.ParabolicRadicalBaseChange
import Langlands.GroupScheme.RelativeLevi.ModuliTrivialization
import Langlands.GroupScheme.RelativeLevi.TorsorStatement
import Langlands.GroupScheme.HomScheme.ChartCoverTransport

/-! # The natural radical action and torsor assembly for actual Levi images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S S' : Scheme.{u}} {G P U : GroupScheme S}
    (i : P ⟶ G) (r : U ⟶ P) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hr : IsRelativeUnipotentRadical r)

/-- Actual conjugation makes the Levi presheaf a natural simply transitive
radical presheaf, without assuming a global Levi image exists. -/
def moduliAction :
    PresheafTorsor.Action U (moduliFunctorOfParabolic hi hG) where
  act {Z} g F := F.conjugate (pulledBackPoint P Z (g ≫ r.hom.hom))
  one_act {Z} F := by
    apply LeviImage.ext
    change conjugateImage (pulledBackPointHom P Z (1 ≫ r.hom.hom)) F.val = F.val
    rw [MonObj.one_comp, map_one, conjugateImage_one]
  mul_act {Z} g h F := by
    apply LeviImage.ext
    change conjugateImage (pulledBackPointHom P Z ((g * h) ≫ r.hom.hom)) F.val =
      conjugateImage (pulledBackPointHom P Z (g ≫ r.hom.hom))
        (conjugateImage (pulledBackPointHom P Z (h ≫ r.hom.hom)) F.val)
    rw [MonObj.mul_comp, map_mul, conjugateImage_mul]
  naturality {Z Z'} a g F := by
    exact LeviImage.restrict_smul (restrictionStable_of_parabolic hi hG) r a g F
  simplyTransitive {Z} F F' := by
    obtain ⟨g, hg, huniq⟩ := LeviImage.existsUnique_conjugate
      ((baseChange Z.hom).map i) ((baseChange Z.hom).map r)
      (hG.baseChange Z.hom) (hi.baseChange hG Z.hom)
      (hr.baseChange_parabolic hi hG Z.hom) F F'
    refine ⟨(pulledBackPointEquiv U Z).symm g, ?_, ?_⟩
    · change F.conjugate (pulledBackPoint P Z
        ((pulledBackPointEquiv U Z).symm g ≫ r.hom.hom)) = F'
      rw [← pulledBackPoint_comp]
      change F.conjugate
        ((pulledBackPointEquiv U Z ((pulledBackPointEquiv U Z).symm g)) ≫ _) = F'
      rw [Equiv.apply_symm_apply]
      exact hg
    · intro v hv
      apply (pulledBackPointEquiv U Z).injective
      rw [Equiv.apply_symm_apply]
      apply huniq
      change F.conjugate (pulledBackPoint U Z v ≫ _) = F'
      rw [pulledBackPoint_comp]
      exact hv

/-- A representation of the actual presheaf gives precisely the
representation interface required by the published torsor target. -/
def moduliRepresentationOfPresheaf {X : Over S}
    (R : (moduliFunctorOfParabolic hi hG).RepresentableBy X) :
    ModuliRepresentation P X where
  pointsEquiv _ := R.homEquiv
  naturality a x := congrArg Subtype.val (R.homEquiv_comp a x)

include hr in
/-- Every smooth affine surjective model of the actual Levi presheaf
supplies all the conclusions of the relative Levi torsor target. -/
theorem exists_torsor_of_smoothAffineModel
    (M : PresheafTorsor.SmoothAffineModel (moduliFunctorOfParabolic hi hG)) :
    ∃ (X : Over S) (_ : ModObj U.X X) (ρ : ModuliRepresentation P X),
      ρ.IsEquivariant r ∧ Flat X.hom ∧ Surjective X.hom ∧
        QuasiCompact X.hom ∧ IsIso (ModObj.leftSMul U.X X) := by
  let A := moduliAction i r hG hi hr
  let R := M.represents
  let := A.representedAction R
  let ρ := moduliRepresentationOfPresheaf (i := i) (hi := hi) (hG := hG) R
  let : Smooth M.scheme.hom := M.smooth
  let : IsAffineHom M.scheme.hom := M.affine
  refine ⟨M.scheme, inferInstance, ρ, ?_, inferInstance, M.surjective,
    inferInstance, A.representedAction_leftSMul_isIso R⟩
  intro T g x
  exact A.representedAction_equivariant R g x

namespace LeviImage

/-- Ambient isomorphisms give equivalences of actual Levi images. -/
def ambientEquiv {B : Scheme.{u}} {H J : GroupScheme B} (e : H ≅ J) :
    LeviImage H ≃ LeviImage J where
  toFun := mapIso e
  invFun := mapIso e.symm
  left_inv F := by
    apply ext
    change (F.val.comap e.inv).comap e.hom = F.val
    rw [← SubgroupFunctor.comap_comp, e.hom_inv_id, SubgroupFunctor.comap_id]
  right_inv F := by
    apply ext
    change (F.val.comap e.hom).comap e.inv = F.val
    rw [← SubgroupFunctor.comap_comp, e.inv_hom_id, SubgroupFunctor.comap_id]

end LeviImage

open TorusSubgroupModuli

/-- The canonical direct/iterated comparison on Levi images. -/
def moduliBaseChangeEquiv (b : S' ⟶ S) (T : Over S') :
    LeviImage ((baseChange T.hom).obj ((baseChange b).obj P)) ≃
      LeviImage ((baseChange ((Over.map b).obj T).hom).obj P) :=
  LeviImage.ambientEquiv (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl P)

theorem restrict_moduliBaseChangeEquiv (b : S' ⟶ S) {T M : Over S'}
    (a : T ⟶ M)
    (F : LeviImage ((baseChange M.hom).obj ((baseChange b).obj P))) :
    (moduliBaseChangeEquiv (P := P) b T
      (F.restrict (restrictionStable_of_parabolic (hi.baseChange hG b)
        (hG.baseChange b)) a)).val =
      restrictImage ((Over.map b).map a) (moduliBaseChangeEquiv (P := P) b M F).val := by
  obtain ⟨K, l, hl, hF⟩ := F.exists_presentation
  have he : F = LeviImage.ofHom l hl := LeviImage.ext hF.symm
  subst F
  change (restrictImage a (SubgroupFunctor.range l)).comap
      (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl P).inv =
    restrictImage ((Over.map b).map a)
      ((SubgroupFunctor.range l).comap
        (Descent.pullbackComparison b M.hom (M.hom ≫ b) rfl P).inv)
  rw [restrictImage_range, ← SubgroupFunctor.range_comp_iso,
    ← SubgroupFunctor.range_comp_iso, restrictImage_range]
  exact congrArg SubgroupFunctor.range (familyHom_pushFamily b l a).symm

/-- The Levi presheaf of a changed-base parabolic is naturally the
restriction of the original Levi presheaf to that base. -/
def moduliPresheafBaseChangeIso (b : S' ⟶ S) :
    moduliFunctorOfParabolic (hi.baseChange hG b) (hG.baseChange b) ≅
      (Over.map b).op ⋙ moduliFunctorOfParabolic hi hG :=
  NatIso.ofComponents (fun T => (moduliBaseChangeEquiv (P := P) b T.unop).toIso)
    (fun a => by
      apply TypeCat.homEquiv.injective
      funext F
      exact LeviImage.ext
        (restrict_moduliBaseChangeEquiv (i := i) (hG := hG) (hi := hi)
          (b := b) (a := a.unop) (F := F)))

end Langlands.GroupScheme.RelativeLevi
