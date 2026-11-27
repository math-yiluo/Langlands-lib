import Langlands.AbelianScheme.InvariantRelativeDifferentials
import Langlands.AbelianScheme.LieAdditivityProof
import Langlands.AbelianScheme.ArtinianHodgeInjectivity
import Langlands.AlgebraicGeometry.AffineCechDeRhamHodgeFrames
import Langlands.AlgebraicGeometry.AffineCechDeRhamCoverPullback
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge

/-! # Inversion on the relative differential frame of an abelian scheme -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open Langlands.Scheme Langlands.Scheme.Modules

/-- The affine comparison for one-forms commutes with pullback along a morphism over the base. -/
lemma oneFormsSectionsEquiv_pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (a : X ⟶ Y) (ha : a ≫ g = f) {V : Y.Opens} {W : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (e : W ≤ a ⁻¹ᵁ V)
    (ω : Ω[(sectionRing g V)⁄R]) :
    oneFormsSectionsEquiv f W hW (RelativeForms.mapOne (sectionAlgHomOver a ha e) ω) =
      (relativeDifferentialsMap a ha).app W
        (sectionPullbackLE a (relativeDifferentials g) e (oneFormsSectionsEquiv g V hV ω)) := by
  let : Module (sectionRing f W) Γ(relativeDifferentials f, W) :=
    inferInstanceAs (Module Γ(X, W) Γ(relativeDifferentials f, W))
  let : Module (sectionRing g V) Γ(relativeDifferentials g, V) :=
    inferInstanceAs (Module Γ(Y, V) Γ(relativeDifferentials g, V))
  let r := sectionAlgHomOver a ha e
  obtain ⟨x, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R (sectionRing g V) ω
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    rw [Derivation.tensorProductTo_tmul, (RelativeForms.mapOne r).map_smulₛₗ,
      RelativeForms.mapOne_d, map_smul, oneFormsSectionsEquiv_D, map_smul, oneFormsSectionsEquiv_D]
    change (a.appLE V W e s) • (relativeDifferentialsDerivation f).app W (a.appLE V W e t) = _
    rw [sectionPullbackLE_smul, Scheme.Modules.Hom.app_smul]
    congr 1
    rw [app_sectionPullbackLE_eq_adjoint, relativeDifferentialsMap_adjoint_app]
    exact (relativeDifferentialsDerivation f).app_restrict (homOfLE e) (a.app V t)
  | add x y hx hy =>
    simpa only [map_add, sectionPullbackLE_add] using congrArg₂ (· + ·) hx hy

end Langlands.AlgebraicGeometry.AffineCechDeRham

namespace Langlands.AbelianScheme

open Langlands.Scheme Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.CechResolution (comp_app_apply)

variable {R : Type u} [CommRing R] (B : AbelianScheme (Spec (CommRingCat.of R)))

private lemma injective_unit_appTop :
    Function.Injective (GroupScheme.identitySection B.toGrp).appTop.hom := by
  have : IsIso B.X.hom.appTop := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    _ _ _ inferInstance inferInstance inferInstance ⊤
  have hs := congrArg Scheme.Hom.appTop (GroupScheme.identitySection_comp B.toGrp)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hs
  intro x y he
  obtain ⟨x', rfl⟩ := (ConcreteCategory.bijective_of_isIso B.X.hom.appTop).surjective x
  obtain ⟨y', rfl⟩ := (ConcreteCategory.bijective_of_isIso B.X.hom.appTop).surjective y
  apply congrArg (B.X.hom.appTop : Γ(Spec (CommRingCat.of R), ⊤) → Γ(B.X.left, ⊤))
  exact (ConcreteCategory.congr_hom hs x').symm.trans (he.trans (ConcreteCategory.congr_hom hs y'))

variable {κ : Type u} [Fintype κ]
  (E : SheafOfModules.free (R := B.X.left.ringCatSheaf) κ ≅ relativeDifferentials B.X.hom)

include E in
private lemma pullbackSection_unit_injective :
    Function.Injective (pullbackSection (GroupScheme.identitySection B.toGrp)
      (relativeDifferentials B.X.hom)) := by
  let e := GroupScheme.identitySection B.toGrp
  let M := relativeDifferentials B.X.hom
  let b := globalSectionBasis E ⊤
  let b' := globalSectionBasis (globalFreePullbackIso e E) (e ⁻¹ᵁ ⊤)
  intro s t hst
  have h := (pullbackSection_eq_sectionPullback e M s).symm.trans
    (hst.trans (pullbackSection_eq_sectionPullback e M t))
  apply b.equivFun.injective
  funext i
  apply injective_unit_appTop B
  change (e.app ⊤).hom (b.equivFun s i) = (e.app ⊤).hom (b.equivFun t i)
  rw [← basis_coordinates_map (sectionPullback e M ⊤) b b'
    (sectionPullback_globalSectionBasis e E ⊤) s i,
    ← basis_coordinates_map (sectionPullback e M ⊤) b b'
    (sectionPullback_globalSectionBasis e E ⊤) t i, h]

private lemma cotangentMap_inversion :
    GroupScheme.cotangentMap (groupHom (-(𝟙 B))) = -(𝟙 (GroupScheme.cotangentAtIdentity B.toGrp)) := by
  have m : groupHom (𝟙 B + -(𝟙 B)) = groupHom (𝟙 B) * groupHom (-(𝟙 B)) := rfl
  have z : groupHom (0 : B ⟶ B) = 1 := rfl
  rw [add_neg_cancel, z] at m
  have p := GroupScheme.cotangentMap_mul (groupHom (𝟙 B)) (groupHom (-(𝟙 B)))
  rw [← m, GroupScheme.cotangentMap_one] at p
  rw [show groupHom (𝟙 B) = 𝟙 B.toGrp from rfl, GroupScheme.cotangentMap_id] at p
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans p.symm)

include E in
/-- Inversion negates every global relative one-form over an affine base when the
relative cotangent sheaf has a finite free frame. -/
lemma inversion_globalForm (ω : Γ(relativeDifferentials B.X.hom, ⊤)) :
    (relativeDifferentialsMap ι[B.X].left (Over.w ι[B.X])).app ⊤
      (pullbackSection ι[B.X].left (relativeDifferentials B.X.hom) ω) = -ω := by
  let ν := groupHom (-(𝟙 B))
  let e := GroupScheme.identitySection B.toGrp
  let a : B.X.left ⟶ B.X.left := ν.hom.hom.left
  let h : a ≫ B.X.hom = B.X.hom := Over.w ν.hom.hom
  let Ω := relativeDifferentials B.X.hom
  let c := (GroupScheme.identityPullbackIso ν).app Ω
  let ω' := pullbackSection a Ω ω
  let z := pullbackSection e ((Scheme.Modules.pullback a).obj Ω) ω'
  have hc : c.inv.app ⊤ z = pullbackSection e Ω ω :=
    Langlands.AlgebraicGeometry.RelativeProjectiveSpace.pullbackSection_comp_eq
      e a (GroupScheme.identitySection_naturality ν) Ω ω
  have hj : c.hom.app ⊤ (pullbackSection e Ω ω) = z := by
    rw [← hc, ← comp_app_apply, c.inv_hom_id]
    rfl
  change (relativeDifferentialsMap a h).app ⊤ ω' = -ω
  apply pullbackSection_unit_injective B E
  rw [pullbackSection_eq_sectionPullback, sectionPullback_naturality, ← pullbackSection_eq_sectionPullback]
  change ((Scheme.Modules.pullback e).map (relativeDifferentialsMap a h)).app ⊤ z = _
  rw [← hj]
  change (GroupScheme.cotangentMap ν).app ⊤ (pullbackSection e Ω ω) =
    pullbackSection e Ω (-ω)
  rw [cotangentMap_inversion, pullbackSection_eq_sectionPullback, pullbackSection_eq_sectionPullback,
    map_neg]
  rfl

/-- The actual inversion map carries each local frame vector to the negative of
that frame vector on the inverse-image chart. -/
lemma hodgeOneBasis_inversion {V W : B.X.left.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ ι[B.X].left ⁻¹ᵁ V) (i : κ) :
    RelativeForms.mapOne (sectionAlgHomOver ι[B.X].left (Over.w ι[B.X]) h)
        (hodgeOneBasis B.X.hom E V hV i) = -hodgeOneBasis B.X.hom E W hW i := by
  let a : B.X.left ⟶ B.X.left := ι[B.X].left
  let M := relativeDifferentials B.X.hom
  let α := relativeDifferentialsMap a (Over.w ι[B.X])
  let s := frameSection E i
  apply (oneFormsSectionsEquiv B.X.hom W hW).injective
  rw [oneFormsSectionsEquiv_pullback a (Over.w ι[B.X]) hV hW h,
    oneFormsSectionsEquiv_hodgeOneBasis, map_neg,
    oneFormsSectionsEquiv_hodgeOneBasis]
  have H (T : B.X.left.Opens) :
      (SheafOfModules.sectionsMap E.hom (SheafOfModules.freeSection i)).val (op T) =
        sectionRes M s T :=
    ((SheafOfModules.sectionsMap E.hom (SheafOfModules.freeSection i)).property
      (homOfLE (le_top : T ≤ ⊤)).op).symm
  rw [H V, H W]
  change α.app W (sectionPullbackLE a M h (sectionRes M s V)) = _
  rw [sectionPullbackLE, show sectionPullback a M V (sectionRes M s V) =
      sectionRes ((Scheme.Modules.pullback a).obj M) (pullbackSection a M s) (a ⁻¹ᵁ V)
      from (pullbackSection_restrict a M s V).symm]
  rw [sectionRes_res]
  have hn := PresheafOfModules.naturality_apply α.val (homOfLE (le_top : W ≤ ⊤)).op
    (pullbackSection a M s)
  change α.app W (sectionRes ((Scheme.Modules.pullback a).obj M) (pullbackSection a M s) W) =
    sectionRes M (α.app ⊤ (pullbackSection a M s)) W at hn
  rw [hn, show α.app ⊤ (pullbackSection a M s) = -s from inversion_globalForm B E s]
  exact map_neg _ _

end Langlands.AbelianScheme
