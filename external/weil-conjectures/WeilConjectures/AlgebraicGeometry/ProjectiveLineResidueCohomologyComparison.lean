/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Cohomology of compatible projective-line residue fibres

Source: Stacks Project, Tags 04DY, 03SI and 01F8.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

private theorem cohomologyMap_comp_explicit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) :
    cohomologyMap f ((g)^*[AddCommGrpCat.{u + 1}].obj F) q
        (cohomologyMap g F q x) =
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).hom.app F) q
        (cohomologyMap fg F q x) := by
  subst fg
  exact (cohomologyPullbackFunctorial f g F q).2.1 x

private theorem cohomology_square_equivalences
    {X Y X' Y' : Scheme.{u}}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (u : Y ⟶ X) (v : Y' ⟶ X')
    [IsUniversalHomeomorphism u] [IsUniversalHomeomorphism v]
    (h : v ≫ f = g ≫ u)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (u)^*[AddCommGrpCat.{u + 1}].obj F ≅ G) (q : ℕ) :
    ∃ (b₁ : Sheaf.H F q ≃+ Sheaf.H G q)
      (b₂ : Sheaf.H ((f)^*[AddCommGrpCat.{u + 1}].obj F) q ≃+
        Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj G) q),
      ∀ y, b₂ (cohomologyMap f F q y) = cohomologyMap g G q (b₁ y) := by
  let c₁ := upperStarComp AddCommGrpCat.{u + 1} v f (g ≫ u) h.symm
  let c₂ := upperStarComp AddCommGrpCat.{u + 1} g u
  let e₂ := (c₁.symm ≪≫ c₂).app F ≪≫ ((g)^*[AddCommGrpCat.{u + 1}]).mapIso e
  let b₁ := (cohomologyEquiv u F q).trans
    (AddEquiv.ofBijective (Sheaf.H.map e.hom q)
      (ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).mapIso e).hom))
  let b₂ := (cohomologyEquiv v ((f)^*[AddCommGrpCat.{u + 1}].obj F) q).trans
    (AddEquiv.ofBijective (Sheaf.H.map e₂.hom q)
      (ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).mapIso e₂).hom))
  refine ⟨b₁, b₂, ?_⟩
  intro y
  change Sheaf.H.map e₂.hom q
      (cohomologyMap v ((f)^*[AddCommGrpCat.{u + 1}].obj F) q
        (cohomologyMap f F q y)) =
    cohomologyMap g G q (Sheaf.H.map e.hom q (cohomologyMap u F q y))
  rw [cohomologyMap_map, cohomologyMap_comp_explicit v f (g ≫ u) h.symm,
    cohomologyMap_comp_explicit g u (g ≫ u) rfl]
  simp only [e₂, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, NatTrans.comp_app, Functor.mapIso_hom,
    ← Sheaf.H.map_comp_apply, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp, c₁, c₂]
  rw [Sheaf.H.map_comp_apply]
  rfl

/-- A commuting residue square of universal homeomorphisms conjugates cohomology
pullback, with the sheaf obtained by restriction from the original projective line.
This statement does not involve stalks or the derived exchange morphism.

Source: Stacks Project, topological invariance Tags 04DY and 03SI, functoriality
Tag 01F8, applied to the residue square in the proof of Tag 095T.
(blueprint: lem-weil-pbc-p1-residue-cohomology-comparison).

Proof: base change ρA and ρB to the projective lines. They remain universal
homeomorphisms, so their cohomology pullbacks are additive equivalences by
topological invariance. The equality hρA identifies the pullback of F₀ to the
k-fibre with the original restriction of F to that fibre: compose the canonical
inverse-image composition isomorphisms and commute inverse image with forgetting
module coefficients. Compose the first cohomology equivalence with the induced
coefficient isomorphism to obtain b₁. The square hρ similarly identifies pullback
along ρB of the residue-target sheaf with pullback along ι of the k-fibre sheaf;
compose the second cohomology equivalence with this coefficient isomorphism for
b₂. Functoriality of cohomology pullback for composition, its naturality in
coefficients, and associativity coherence of inverse image give the displayed
equation. In degree zero this is ordinary restriction of sections; the same
functoriality proves every higher degree. No torsion assumption, strict-local
exchange, or proper-base-change theorem is needed. -/
theorem Etale.projectiveLine_residueCohomologyComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {S : Scheme.{u}} {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    {k k' : Type u} [Field k] [Field k']
    (jA : Spec (.of A) ⟶ S) (φ : A →+* B) [IsLocalHom φ]
    (σ : Spec (.of k) ⟶ S) (ι : Spec (.of k') ⟶ Spec (.of k))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    [IsUniversalHomeomorphism ρA] [IsUniversalHomeomorphism ρB]
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ jA = σ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _ jA)^*[ModuleCat.{u + 1} Λ].obj F
    let rA := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
    let i₀ := Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))
    let G₀ := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((ProjectiveSpace.map _ rA)^*[ModuleCat.{u + 1} Λ].obj F₀)
    let G := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)
    ∃ (b₁ : Sheaf.H G₀ q ≃+ Sheaf.H G q)
                (b₂ : Sheaf.H ((ProjectiveSpace.map _ i₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q ≃+
                  Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj G) q),
                (∀ y, b₂ (Etale.cohomologyMap (ProjectiveSpace.map _ i₀) G₀ q y) =
                  Etale.cohomologyMap (ProjectiveSpace.map _ ι) G q (b₁ y)) := by
  let j := ProjectiveSpace.map (ULift.{u} (Fin 2)) jA
  let r := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let u := ProjectiveSpace.map (ULift.{u} (Fin 2)) ρA
  let v := ProjectiveSpace.map (ULift.{u} (Fin 2)) ρB
  let f := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) ι
  let σP := ProjectiveSpace.map (ULift.{u} (Fin 2)) σ
  let F₀ := (j)^*[ModuleCat.{u + 1} Λ].obj F
  let FAb := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let G₀ := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
    ((r)^*[ModuleCat.{u + 1} Λ].obj F₀)
  let G := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
    ((σP)^*[ModuleCat.{u + 1} Λ].obj F)
  have hσP : σP = (u ≫ r) ≫ j := by
    dsimp [σP, u, r, j]
    rw [← ProjectiveSpace.map_comp, ← ProjectiveSpace.map_comp, Category.assoc, hρA]
  have hsquare : v ≫ f = g ≫ u := by
    dsimp [v, f, g, u]
    rw [← ProjectiveSpace.map_comp, ← ProjectiveSpace.map_comp, hρ]
  have : IsUniversalHomeomorphism u :=
    MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
      (ProjectiveSpace.isPullback_map _ ρA).flip inferInstance
  have : IsUniversalHomeomorphism v :=
    MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
      (ProjectiveSpace.isPullback_map _ ρB).flip inferInstance
  obtain ⟨ej⟩ := pullback_forget_modules_iso Λ j F
  obtain ⟨er⟩ := pullback_forget_modules_iso Λ r F₀
  obtain ⟨eσ⟩ := pullback_forget_modules_iso Λ σP F
  let e : (u)^*[AddCommGrpCat.{u + 1}].obj G₀ ≅ G :=
    ((u)^*[AddCommGrpCat.{u + 1}]).mapIso
      (er ≪≫ ((r)^*[AddCommGrpCat.{u + 1}]).mapIso ej) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} u r).symm.app
      ((j)^*[AddCommGrpCat.{u + 1}].obj FAb) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} (u ≫ r) j σP hσP).symm.app FAb ≪≫ eσ.symm
  exact cohomology_square_equivalences f g u v hsquare G₀ G e q


end AlgebraicGeometry
