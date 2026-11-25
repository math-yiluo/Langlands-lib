/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ExternalSectionsComponents
import WeilConjectures.AlgebraicGeometry.ExternalOpenCoefficientNormalized
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # External section components on open subschemes

Source: Stacks Project, Tag 0BED, omitted degree-zero canonical-cup verification;
Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-external-sections-open-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarMap_openImage {A B : Scheme.{w}}
    (h : B ⟶ Spec (CommRingCat.of k)) (j : A ⟶ B) [IsOpenImmersion j]
    (U : A.Opens) (r : k) :
    (j.appIso U).hom (scalarMap h (j ''ᵁ U) r) = scalarMap (j ≫ h) U r := by
  rw [Scheme.Hom.appIso_hom]
  change (A.presheaf.map (eqToHom (j.preimage_image_eq U).symm).op).hom
      ((j.app (j ''ᵁ U)).hom (scalarMap h (j ''ᵁ U) r)) = _
  rw [scalarMap_pullback]
  simp only [scalarMap, RingHom.comp_apply]
  change ((A.presheaf.map (homOfLE (le_top (a := j ⁻¹ᵁ j ''ᵁ U))).op ≫
      A.presheaf.map (eqToHom (j.preimage_image_eq U).symm).op).hom)
      (((ΓSpecIso (CommRingCat.of k)).inv ≫ (j ≫ h).appTop).hom r) = _
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def scalarRestrictIso {A B : Scheme.{w}}
    (h : B ⟶ Spec (CommRingCat.of k)) (j : A ⟶ B) [IsOpenImmersion j]
    (hA : A ⟶ Spec (CommRingCat.of k)) (hc : j ≫ h = hA)
    (M : B.Modules) (U : A.Opens) :
    scalarObj h M (op (j ''ᵁ U)) ≅ scalarObj hA (M.restrict j) (op U) := by
  refine ModuleCat.isoMk (M.restrictAppIso j U).symm ?_
  intro r
  ext x
  change (scalarMap hA U r) •
      (show Γ(M.restrict j, U) from (M.restrictAppIso j U).inv x) =
    (M.restrictAppIso j U).inv
      ((scalarMap h (j ''ᵁ U) r) • (show Γ(M, j ''ᵁ U) from x))
  rw [smul_restrictAppIso_inv_apply]
  rw [scalarMap_openImage, hc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit external section component agrees with the external product on X times V.
Source: Stacks Project, Tag 0BED, degree-zero cup product and omitted canonical-map
verification; Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-external-sections-open-comparison).

Proof: Let j : X times V -> X times Y be the base change of V -> Y. It is an
open immersion with image pr_2 inverse-image V. The section isomorphism for restriction
along V -> Y identifies G(V) with the global sections of G restricted to V; its scalar
action is unchanged because both structure maps to Spec(k) are composites with g.
Tensoring this isomorphism with Gamma(X,F) gives eS. Restriction of the external
coefficient to the image of j identifies its sections with global sections of its
restriction along j. Compare restriction with tensor pullback by the unique isomorphism
of the two left adjoints to j_*, normalized by the adjunction-unit equation. Apply the
module-pullback-tensor comparison, then the pullback-composition comparisons for
j followed by the two projections. The first composite is the projection to X;
the second is the projection to V followed by V -> Y. Finally identify the pullback
of G along V -> Y with its restriction by the same normalized open-immersion
comparison. These isomorphisms of coefficients and sections give eT, and are linear
over k by compatibility of their structure maps. On a pure tensor s tensor t the
unit equations send the restricted pr_1 pullback of s to its pullback on X times V,
and send the pr_2 pullback of t to the pullback of its restricted section on V.
The tensor comparison sends the tensor section to the tensor of these images.
Thus the displayed equality holds on pure tensors, and tensor induction proves it
on all tensors. For V empty, restriction and all these adjunction comparisons are
still isomorphisms, so the same proof applies without a nonemptiness assumption.
-/
theorem externalSectionsComponent_openComparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    ∃ eS : ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op V)) ≅
        ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k]
          scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)),
    ∃ eT : scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) ≅
        scalarObj (pullback.fst f (V.ι ≫ g) ≫ f)
          (externalCupCoefficients f (V.ι ≫ g) F (G.restrict V.ι)) (op ⊤),
      externalSectionsComponent f g F G V ≫ eT.hom = eS.hom ≫
        ModuleCat.ofHom
          (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι)) := by
  let j : Limits.pullback f (V.ι ≫ g) ⟶ Limits.pullback f g :=
    pullback.map f (V.ι ≫ g) f g (𝟙 X) V.ι (𝟙 _)
      (by simp) (by simp)
  have hfst : j ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g) := by
    simp [j]
  have hsnd : j ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι := by
    simp [j]
  have hj : j ''ᵁ ⊤ = pullback.snd f g ⁻¹ᵁ V := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply TopologicalSpace.Opens.ext
    change Set.range j = _
    rw [Scheme.Pullback.range_map]
    simp
  obtain ⟨κ, hκ⟩ := exists_externalOpenCoefficient_normalized f g F G V j hj hfst hsnd
  let eG : scalarObj g G (op V) ≅ scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤) :=
    (scalarPresheaf g G).mapIso (eqToIso (by simp : V.ι ''ᵁ ⊤ = V)).op ≪≫
      scalarRestrictIso g V.ι (V.ι ≫ g) rfl G ⊤
  let eS := (MonoidalCategory.tensorLeft (scalarObj f F (op ⊤))).mapIso eG
  let eR : scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) ≅
      scalarObj (pullback.fst f (V.ι ≫ g) ≫ f)
        ((externalCupCoefficients f g F G).restrict j) (op ⊤) :=
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)).mapIso
        (eqToIso hj).op ≪≫
      scalarRestrictIso (pullback.fst f g ≫ f) j (pullback.fst f (V.ι ≫ g) ≫ f)
        (by rw [← Category.assoc, hfst]) (externalCupCoefficients f g F G) ⊤
  let eK := (ModuleCat.restrictScalars (scalarMap (pullback.fst f (V.ι ≫ g) ≫ f) ⊤)).mapIso
    ((SheafOfModules.evaluation (Limits.pullback f (V.ι ≫ g)).ringCatSheaf (op ⊤)).mapIso κ)
  refine ⟨eS, eR ≪≫ eK, ?_⟩
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s t
  change κ.hom.app ⊤
      ((externalCupCoefficients f g F G).presheaf.map (eqToHom hj).op
        (tmulSection
          (scalarPullbackGlobalSection f (pullback.fst f g) F
            (pullback.snd f g ⁻¹ᵁ V) s)
          (scalarUnitSection g (pullback.snd f g) G V t))) = _
  exact hκ s t

end
end AlgebraicGeometry.Scheme.Modules
