import Langlands.AlgebraicGeometry.SectionDifferentialsSquare
import Langlands.AbelianScheme.CotangentBaseChangeProof
import Langlands.AbelianScheme.LieFunctor
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Identity and composition for actual group cotangent base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S T U : AlgebraicGeometry.Scheme.{u}}

/-- The canonical cotangent base-change isomorphism, with its actual comparison
map as forward morphism. -/
def cotangentBaseChangeIso (b : T ⟶ S) (G : GroupScheme S) :
    (pullback b).obj G.cotangentAtIdentity ≅
      ((baseChange b).obj G).cotangentAtIdentity := by
  letI : IsIso (cotangentBaseChangeMap b G) := cotangentBaseChangeIsIso S T b G
  exact asIso (cotangentBaseChangeMap b G)

@[simp]
lemma cotangentBaseChangeIso_hom (b : T ⟶ S) (G : GroupScheme S) :
    (cotangentBaseChangeIso b G).hom = cotangentBaseChangeMap b G := rfl

lemma cotangentBaseChangeMap_eq_section (b : T ⟶ S) (G : GroupScheme S) :
    cotangentBaseChangeMap b G =
      Langlands.Scheme.sectionDifferentialsSquareMap (Limits.pullback.fst G.X.hom b) b
        Limits.pullback.condition ((baseChange b).obj G).identitySection
        G.identitySection (identitySection_baseChange_fst b G) := rfl

private lemma sectionDifferentialsSquareMap_groupHom
    {G H : GroupScheme S} (f : G ⟶ H) :
    Langlands.Scheme.sectionDifferentialsSquareMap f.hom.hom.left (𝟙 S)
        (by simpa only [Category.comp_id] using f.hom.hom.w)
        G.identitySection H.identitySection
        (by simpa only [Category.id_comp] using identitySection_naturality f) =
      (pullbackId S).hom.app H.cotangentAtIdentity ≫ cotangentMap f := by
  rw [Langlands.Scheme.sectionDifferentialsSquareMap_id_base
    f.hom.hom.left f.hom.hom.w G.identitySection H.identitySection
    (identitySection_naturality f)]
  change _ =
    (pullbackId S).hom.app H.cotangentAtIdentity ≫
      (((pullbackCongr (identitySection_naturality f)).inv.app
          (Langlands.Scheme.relativeDifferentials H.X.hom) ≫
        (pullbackComp G.identitySection f.hom.hom.left).inv.app
          (Langlands.Scheme.relativeDifferentials H.X.hom)) ≫
        (pullback G.identitySection).map
          (Langlands.Scheme.relativeDifferentialsMap f.hom.hom.left f.hom.hom.w))
  simp only [Category.assoc]
  rfl

/-- Identity base change agrees with the actual group identity comparison. -/
lemma cotangentBaseChangeMap_id (G : GroupScheme S) :
    cotangentBaseChangeMap (𝟙 S) G =
      (pullbackId S).hom.app G.cotangentAtIdentity ≫
        cotangentMap (baseChangeIdIso G).hom := by
  rw [cotangentBaseChangeMap_eq_section]
  simpa only [baseChangeIdIso_hom_left] using
    sectionDifferentialsSquareMap_groupHom (baseChangeIdIso G).hom

private lemma sectionDifferentialsSquareMap_comp_transport
    {X Y Z S T U : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    (gh : X ⟶ Z) (bc : U ⟶ S) (hgh : g ≫ h = gh) (hbc : b ≫ c = bc)
    {fX : X ⟶ U} {fY : Y ⟶ T} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX ≫ b) (wh : h ≫ fZ = fY ≫ c)
    (eX : U ⟶ X) (eY : T ⟶ Y) (eZ : S ⟶ Z)
    (hg : eX ≫ g = b ≫ eY) (hh : eY ≫ h = c ≫ eZ) :
    (pullback b).map (Langlands.Scheme.sectionDifferentialsSquareMap h c wh eY eZ hh) ≫
        Langlands.Scheme.sectionDifferentialsSquareMap g b wg eX eY hg =
      Langlands.SchemeModule.RigidifiedModule.compHom b c bc hbc
          ((pullback eZ).obj (Langlands.Scheme.relativeDifferentials fZ)) ≫
        Langlands.Scheme.sectionDifferentialsSquareMap gh bc
          (by rw [← hgh, Category.assoc, wh, ← Category.assoc, wg, Category.assoc, hbc])
          eX eZ (by rw [← hgh, ← Category.assoc, hg, Category.assoc, hh,
            ← Category.assoc, hbc]) := by
  subst gh
  subst bc
  rw [Langlands.SchemeModule.RigidifiedModule.compHom_rfl]
  exact Langlands.Scheme.sectionDifferentialsSquareMap_comp g h b c wg wh
    eX eY eZ hg hh

/-- Sequential actual cotangent base change agrees with base change along the
composite and the actual group composition comparison. -/
lemma cotangentBaseChangeMap_comp (b : T ⟶ S) (c : U ⟶ T) (G : GroupScheme S) :
    (pullback c).map (cotangentBaseChangeMap b G) ≫
        cotangentBaseChangeMap c ((baseChange b).obj G) =
      (pullbackComp c b).hom.app G.cotangentAtIdentity ≫
        cotangentBaseChangeMap (c ≫ b) G ≫
          cotangentMap (baseChangeCompIso b c G).inv := by
  let f := (baseChangeCompIso b c G).inv
  have hseq := Langlands.Scheme.sectionDifferentialsSquareMap_comp
    (Limits.pullback.fst ((baseChange b).obj G).X.hom c)
    (Limits.pullback.fst G.X.hom b) c b
    Limits.pullback.condition Limits.pullback.condition
    ((baseChange c).obj ((baseChange b).obj G)).identitySection
    ((baseChange b).obj G).identitySection G.identitySection
    (identitySection_baseChange_fst c ((baseChange b).obj G))
    (identitySection_baseChange_fst b G)
  have hcmp := sectionDifferentialsSquareMap_comp_transport
    f.hom.hom.left (Limits.pullback.fst G.X.hom (c ≫ b)) (𝟙 U) (c ≫ b)
    (Limits.pullback.fst ((baseChange b).obj G).X.hom c ≫
      Limits.pullback.fst G.X.hom b) (c ≫ b)
    (baseChangeCompIso_inv_fst b c G) (Category.id_comp _)
    (by
      change f.hom.hom.left ≫ ((baseChange (c ≫ b)).obj G).X.hom =
        ((baseChange c).obj ((baseChange b).obj G)).X.hom ≫ 𝟙 U
      exact f.hom.hom.w.trans (Category.comp_id _).symm) Limits.pullback.condition
    ((baseChange c).obj ((baseChange b).obj G)).identitySection
    ((baseChange (c ≫ b)).obj G).identitySection G.identitySection
    (by simpa only [Category.id_comp] using identitySection_naturality f)
    (identitySection_baseChange_fst (c ≫ b) G)
  rw [sectionDifferentialsSquareMap_groupHom,
    Langlands.SchemeModule.RigidifiedModule.compHom_id_left] at hcmp
  simp only [eqToHom_refl, Category.comp_id] at hcmp
  change (pullback (𝟙 U)).map (cotangentBaseChangeMap (c ≫ b) G) ≫
      (pullbackId U).hom.app ((baseChange (c ≫ b)).obj G).cotangentAtIdentity ≫
        cotangentMap f = _ at hcmp
  rw [reassoc_of% (pullbackId U).hom.naturality (cotangentBaseChangeMap (c ≫ b) G)]
    at hcmp
  have hcancel := (cancel_epi ((pullbackId U).hom.app
    ((pullback (c ≫ b)).obj G.cotangentAtIdentity))).mp hcmp
  rw [cotangentBaseChangeMap_eq_section, cotangentBaseChangeMap_eq_section]
  rw [hseq, ← hcancel]
  rfl

end Langlands.GroupScheme
