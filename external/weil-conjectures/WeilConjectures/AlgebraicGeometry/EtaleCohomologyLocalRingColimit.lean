/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural
import WeilConjectures.AlgebraicGeometry.EtaleRestrictedCohomologyNeighbourhoodColimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyTriangleLaws
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Étale cohomology over a local ring as a colimit

Source: Stacks Project, Étale Cohomology, Tag 09AX, proof, and Tags 03Q6 and 09YQ;
Cohomology on Sites, Tag 03F3
(blueprint: lem-weil-pbc-etale-cohomology-local-ring-colimit).

The diagram is a presentation of the actual object-cohomology presheaf, with its arrows
specified as well as its objects. The object cohomology H^q(U, F) is Ext from the
sheafified free abelian sheaf on the representable `uliftYoneda U` (Mathlib's
`Sheaf.cohomologyPresheaf` construction, written out because the coefficients
`AddCommGrpCat.{u + 1}` lie above the site's morphism universe; the form of the existing
AbelianHigherDirectImagePresheaf). The conclusion supplies the restriction comparison,
the unique factorizations of the local-scheme morphism, and a colimit cocone whose legs
are the pullbacks followed by inverse-image composition. `Sheaf.H` is the recorded Ext
encoding of abelian-sheaf cohomology; its K-injective comparison is a comparison theorem.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyMap_pullback_triangle_named
    {S T U V : Scheme.{u}} (a : U ⟶ S) (b : T ⟶ U) (c : V ⟶ T)
    (ba : T ⟶ S) (cb : V ⟶ U) (cba : V ⟶ S)
    (hba : ba = b ≫ a) (hcb : cb = c ≫ b) (hcba : cba = cb ≫ a)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) q) :
    Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} c ba cba
        (by rw [hcba, hcb, hba, Category.assoc])).inv.app F) q
      (Etale.cohomologyMap c ((Etale.upperStar AddCommGrpCat.{u + 1} ba).obj F) q
        (Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} b a ba hba).inv.app F) q
          (Etale.cohomologyMap b
            ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) q ξ))) =
    Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} cb a cba hcba).inv.app F) q
      (Etale.cohomologyMap cb
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) q ξ) := by
  subst ba
  subst cb
  subst cba
  have h := (Etale.cohomologyTriangleMap_laws S F q).2 V T U c b a (b ≫ a)
    ((c ≫ b) ≫ a) rfl (Category.assoc c b a)
  have hh := congrArg (fun f => f ξ) h
  dsimp only [Etale.cohomologyTriangleMap, AddMonoidHom.comp_apply] at hh
  exact hh.symm

/-- Object cohomology on open subschemes identifies with cohomology of the restricted
sheaf, and its canonical pullbacks to the local scheme form a colimit cocone.
Source: Stacks Project, Tags 09AX (proof), 03Q6, 09YQ and 03F3
(blueprint: lem-weil-pbc-etale-cohomology-local-ring-colimit).

Proof:
1. Use etaleOpenObjectCohomology_natural for the comparison e and its naturality.
2. Mathlib's fromSpecStalkOfMem supplies g and its factorization. Cancel the open
   immersion to prove uniqueness and compatibility with inclusions.
3. Conjugate the diagram's maps by d followed by e. Naturality of e identifies the
   resulting transitions with cohomological pullback and inverse-image composition.
4. The triangle laws for fixed-base cohomology identify the two successive pullbacks
   with the direct pullback. Thus the prescribed maps form a cocone B with point the
   local-scheme cohomology and comparison b equal to the identity.
5. Apply etaleRestrictedCohomology_neighbourhood_colimit to B. Its proof restricts to
   affine neighbourhoods, uses their stated scheme limit and fixed-base cohomology
   continuity, and transfers the colimit property by cofinality.
6. If a class has zero image, injectivity of b makes its coprojection equal to that
   of zero. Mathlib's filtered-colimit equality criterion gives a smaller
   neighbourhood on which the class is zero.
-/
theorem etaleCohomology_localRing_colimit
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : X) (q : ℕ)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : P = (Functor.flip ((uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).op ⋙
        Abelian.extFunctor q)).obj F)
    (D : (OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (d : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
      D.obj (op U) ≅ P.obj
        (op (Scheme.Etale.mk (Scheme.Opens.ι U.1))))
    (hD : ∀ (U V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x) (f : V ⟶ U),
      D.map f.op = (d U).hom ≫ P.map
        (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
          (A := Scheme.Etale.mk (Scheme.Opens.ι V.1))
          (B := Scheme.Etale.mk (Scheme.Opens.ι U.1)) (X.homOfLE f.le)
          (X.homOfLE_ι f.le) trivial).op ≫ (d V).inv) :
    ∃ e : ∀ U : X.Opens, P.obj
        (op (Scheme.Etale.mk U.ι)) ≅
        AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q),
      (∀ (U V : X.Opens) (h : V ≤ U),
        P.map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι) (X.homOfLE h)
              (X.homOfLE_ι h) trivial).op ≫
            (e V).hom =
          (e U).hom ≫ AddCommGrpCat.ofHom
            (Etale.cohomologyMap (X.homOfLE h)
              ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map
              ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
                (X.homOfLE_ι h).symm).inv.app F) q)) ∧
      ∃ (g : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
          Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1))
        (hg : ∀ U, X.fromSpecStalk x = g U ≫ (Scheme.Opens.ι U.1)),
        (∀ U (g' : Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1)),
          g' ≫ (Scheme.Opens.ι U.1) = X.fromSpecStalk x → g' = g U) ∧
        ∃ (B : Cocone D)
          (b : B.pt ≅ AddCommGrpCat.of
            (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
              (X.fromSpecStalk x)).obj F) q)),
          (∀ U, B.ι.app (op U) ≫ b.hom =
            (d U).hom ≫ (e U.1).hom ≫ AddCommGrpCat.ofHom
              (Etale.cohomologyMap (g U)
                ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
              AddCommGrpCat.ofHom (Sheaf.H.map
                ((Etale.upperStarComp AddCommGrpCat.{u + 1} (g U) (Scheme.Opens.ι U.1)
                  (X.fromSpecStalk x) (hg U)).inv.app F) q)) ∧
          Nonempty (IsColimit B) ∧
          ∀ U (ξ : D.obj (op U)), (B.ι.app (op U) ≫ b.hom) ξ = 0 →
            ∃ (V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)
              (f : V ⟶ U), D.map f.op ξ = 0 := by
  classical
  obtain ⟨e, he⟩ := etaleOpenObjectCohomology_natural F q P hP
  let g := fun U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x =>
    Scheme.Opens.fromSpecStalkOfMem U.1 x U.2
  have hg : ∀ U, X.fromSpecStalk x = g U ≫ (Scheme.Opens.ι U.1) := by
    intro U
    exact (Scheme.Opens.fromSpecStalkOfMem_ι U.1 x U.2).symm
  refine ⟨e, he, g, hg, ?_⟩
  refine ⟨?_, ?_⟩
  · intro U g' h
    apply (cancel_mono (Scheme.Opens.ι U.1)).mp
    exact h.trans (hg U)
  · let eD := fun U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x =>
      d U ≪≫ e U.1
    have htrans : ∀ (U V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)
        (f : V ⟶ U), D.map f.op = (eD U).hom ≫ AddCommGrpCat.ofHom
          (Etale.cohomologyMap (X.homOfLE f.le)
            ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
          AddCommGrpCat.ofHom (Sheaf.H.map
            ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE f.le)
              (Scheme.Opens.ι U.1) (Scheme.Opens.ι V.1)
              (X.homOfLE_ι f.le).symm).inv.app F) q) ≫ (eD V).inv := by
      intro U V f
      dsimp [eD]
      rw [hD U V f]
      have hn := he U.1 V.1 f.le
      calc
        _ = (d U).hom ≫
            (P.map (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk (Scheme.Opens.ι V.1))
              (B := Scheme.Etale.mk (Scheme.Opens.ι U.1)) (X.homOfLE f.le)
              (X.homOfLE_ι f.le) trivial).op ≫ (e V.1).hom) ≫
              (e V.1).inv ≫ (d V).inv := by simp
        _ = _ := by rw [hn]; simp only [Category.assoc]
    let θ := fun U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x =>
      (eD U).hom ≫ AddCommGrpCat.ofHom
        (Etale.cohomologyMap (g U)
          ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((Etale.upperStarComp AddCommGrpCat.{u + 1} (g U) (Scheme.Opens.ι U.1)
            (X.fromSpecStalk x) (hg U)).inv.app F) q)
    have hθ : ∀ (U V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)
        (f : V ⟶ U), D.map f.op ≫ θ V = θ U := by
      intro U V f
      have hgu : g U = g V ≫ X.homOfLE f.le := by
        apply (cancel_mono (Scheme.Opens.ι U.1)).mp
        rw [Category.assoc, X.homOfLE_ι, ← hg V, ← hg U]
      rw [htrans U V f]
      dsimp only [θ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      ext ξ
      change Sheaf.H.map _ q (Etale.cohomologyMap _ _ q
        (Sheaf.H.map _ q (Etale.cohomologyMap _ _ q ((eD U).hom ξ)))) = _
      exact cohomologyMap_pullback_triangle_named (Scheme.Opens.ι U.1) (X.homOfLE f.le)
        (g V) (Scheme.Opens.ι V.1) (g U) (X.fromSpecStalk x)
        (X.homOfLE_ι f.le).symm hgu (hg U) F q ((eD U).hom ξ)
    let B : Cocone D :=
      { pt := AddCommGrpCat.of
          (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (X.fromSpecStalk x)).obj F) q)
        ι := { app := fun U => θ U.unop
               naturality := by
                 intro U V f
                 simpa using hθ U.unop V.unop f.unop } }
    let b := Iso.refl B.pt
    have hb : ∀ U, B.ι.app (op U) ≫ b.hom = θ U := by
      intro U
      exact Category.comp_id _
    have hcolim := etaleRestrictedCohomology_neighbourhood_colimit F x q D eD htrans
      g hg B b hb
    refine ⟨B, b, ?_, hcolim, ?_⟩
    · intro U
      simpa only [θ, eD, Iso.trans_hom, Category.assoc] using hb U
    · intro U ξ hξ
      have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
        preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
      have hz : B.ι.app (op U) ξ = B.ι.app (op U) 0 := by
        apply (ConcreteCategory.bijective_of_isIso b.hom).injective
        change b.hom (B.ι.app (op U) ξ) = 0 at hξ
        simpa only [map_zero] using hξ
      obtain ⟨V, f, _, hf⟩ :=
        Concrete.isColimit_exists_of_rep_eq D hcolim.some ξ 0 hz
      exact ⟨V.unop, f.unop, by simpa using hf⟩

end AlgebraicGeometry
