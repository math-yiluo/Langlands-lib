/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.EtaleSetStagePresheafLocallyInjective
import WeilConjectures.AlgebraicGeometry.EtaleSetStagePresheafLocallySurjective

/-! # Sheaf-level continuity on the original affine étale site

Source: Stacks Project, Étale Cohomology Tag 09YQ and Sites Tags 0A35 and 09YN.
(blueprint: lem-weil-pbc-sets-stage-sheaf-colimit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The canonical stage push-pull sheaves have the limit push-pull sheaf as their
colimit on the original affine étale site. This is a sheaf colimit assertion:
it only requires local representatives and local eventual equality, and does not
assert that evaluation at an affine object preserves the colimit.

Source: Stacks Project, Étale Cohomology Tag 09YQ, degree-zero proof via 0EYL and
04HR; Sites Tag 0A35, equation-compute-pullback-to-limit, and Tag 09YN.
(blueprint: lem-weil-pbc-sets-stage-sheaf-colimit).

Proof:
1. Restrict to the cofinal upper tail of i₀. Present the limit affine étale site
   as the filtered colimit of the stage sites using the affine-site colimit theorem.
   Its object, arrow, and covering descent clauses descend every finite diagram
   occurring in an inverse-image representative or a local equality.
2. The inverse-image formula of 0A35 expresses a section locally by a section
   on an object of the original site and an arrow from the limit object to its
   base change. Descend that arrow to a stage; the adjunction unit gives the
   corresponding section of the stage inverse image. Equal representatives have
   their witnessing arrows and equations at a common later stage. Sheafification
   thus gives the limit push-pull sheaf from the presheaf colimit of stage sheaves.
3. Transport through the affine/full restriction equivalences. The unit and
   composition equations of the affine inverse-image comparison identify the
   resulting maps with etaleSetSectionComparison, including pullback pasting.
4. A compatible family of maps from the stage sheaves to any sheaf factors
   uniquely through this sheafification. Local existence in step 2 defines the
   factorization; local equality makes it independent of representatives, and
   the sheaf axiom glues it. This proves the colimit universal property. The
   supplied point and component equations transport it to E and K.
Empty objects are covered by the empty cover and hence have their unique section;
no nonemptiness of a section set is assumed. -/
theorem etaleSetStageSheaf_isColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1))) :
    let ρ := (Scheme.fullAffineEtaleInclusion (D.obj (op i₀))).sheafPushforwardContinuous
      (Type (u + 1)) (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (D.obj (op i₀)).smallEtaleTopology
    let A := fun j : Over (op i₀) ↦ ρ.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).sheafPushforwardContinuous
        (Type (u + 1)) ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        ((D.obj j.left).smallGrothendieckTopology (P := @Etale) (Q := @Etale))).obj
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G))
    let L := ρ.obj
      ((@Functor.sheafPushforwardContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀)))
        (Type (u + 1)) _ ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (c.pt.smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (Etale.isContinuous_overPullback (c.π.app (op i₀)))).obj
          ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G))
    ∀ (E : (Over (op i₀))ᵒᵖ ⥤
        Sheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀))) (Type (u + 1)))
      (K : Cocone E),
      (∀ j : Over (op i₀), E.obj (op j) = A j) → K.pt = L →
      (∀ (j k : Over (op i₀)) (a : k ⟶ j)
        (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((E.map a.op).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp a.left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W.obj)) →
      (∀ (j : Over (op i₀)) (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((K.ι.app (op j)).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
            (c.π.app (op i₀)) (c.w j.hom) G W.obj)) →
      Nonempty (IsColimit K) := by
  dsimp only
  intro E K hobj hpt hmap hleg
  let J := Scheme.fullAffineEtaleTopology (D.obj (op i₀))
  let F := E ⋙ sheafToPresheaf J (Type (u + 1))
  let a := colimit.desc F ((sheafToPresheaf J (Type (u + 1))).mapCocone K)
  have hinj : Presheaf.IsLocallyInjective J a :=
    etaleSetStagePresheaf_locallyInjective D c hc i₀ G E K hobj hpt hmap hleg
  have hsurj : Presheaf.IsLocallySurjective J a :=
    etaleSetStagePresheaf_locallySurjective D c hc i₀ G E K hobj hpt hmap hleg
  let H := Sheaf.sheafifyCocone (colimit.cocone F)
  let hH := Sheaf.isColimitSheafifyCocone (colimit.cocone F) (colimit.isColimit F)
  let q := hH.desc K
  have hfac : toSheafify J (colimit F) ≫ q.hom = a := by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc]
    have hι : (H.ι.app i).hom =
        colimit.ι F i ≫ toSheafify J (colimit F) := by
      simpa only [colimit.cocone_ι, colimit.cocone_x] using
        Sheaf.sheafifyCocone_ι_app_val (colimit.cocone F) i
    rw [← hι]
    change (H.ι.app i ≫ q).hom = _
    rw [hH.fac]
    exact (colimit.ι_desc ((sheafToPresheaf J (Type (u + 1))).mapCocone K) i).symm
  have hqinj : Sheaf.IsLocallyInjective q :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J a hfac
  have hqsurj : Sheaf.IsLocallySurjective q :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have : IsIso (hH.desc K) :=
    (Sheaf.isLocallyBijective_iff_isIso q).mp ⟨hqinj, hqsurj⟩
  exact ⟨IsColimit.ofPointIso hH⟩

end AlgebraicGeometry
