/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalSectionsOpenComparison

/-! # Restriction compatibility of external global sections

Source: Stacks Project, Tag 0BED, the degree-zero cup product and its restriction maps.
(blueprint: lem-sc-external-global-sections-restriction-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The presheaf of sections of the external coefficient above opens of the second factor.
Source: Stacks Project, Tag 0BED. -/
abbrev externalSectionsPushforward
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : Y.Opensᵒᵖ ⥤ ModuleCat.{w} k :=
  (TopologicalSpace.Opens.map (pullback.snd f g).base).op ⋙
    scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)

/-- Sections above the top open are global sections on the fibre product.
Source: Stacks Project, Tag 0BED. -/
def externalSectionsTopIso
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    (externalSectionsPushforward f g F G).obj (op ⊤) ≅
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (op ⊤) :=
  (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)).mapIso
    (eqToIso (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- The external section comparison is a morphism of presheaves on the second factor.
Its components identify with the canonical comparisons on the open subschemes.
Source: Stacks Project, Tag 0BED, degree-zero cup product; Tags 0096 and 0097,
restriction and composition of pullback adjunctions.
(blueprint: lem-sc-external-global-sections-restriction-comparison).

Proof: Above V, restrict a global section of F to pr_2 inverse-image V using the
pullback-adjunction unit for pr_1, and pull a section of G(V) back using the unit for
pr_2. Their tensor section is bilinear over k, so it induces the component c_V.
Naturality of both units and the restriction formula for tensor sections prove
naturality of c, first on pure tensors and then by tensor induction. At the top open
these units, followed by the restriction along preimage_top, are precisely the two
maps tensorPullbackTopSection in the definition of externalGlobalSectionsTensor.
This proves the normalization equation. For V, the standard cartesian square of
open subschemes identifies X times V with pr_2 inverse-image V. Restriction of G
to V has sections G(V), with the same k-action; this gives eS after tensoring with
Gamma(X,F). Restriction along the open immersion is naturally isomorphic to tensor
pullback by uniqueness of left adjoints to pushforward. Compose this comparison
with the pullback-composition comparisons on each factor and the tensor-pullback
comparison to identify the restricted external coefficient with the external
coefficient on X times V. Its global sections give eT. The unit equations for these
comparisons carry the two pulled-back sections to the two local pulled-back
sections. Thus the square commutes on pure tensors, hence on every tensor.
All comparisons are isomorphisms for arbitrary opens, including the empty open;
no affineness, quasi-coherence, finiteness, or cover assumption is used.
-/
theorem exists_externalSectionsRestrictionComparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    ∃ c : scalarPresheaf g G ⋙
        MonoidalCategory.tensorLeft (scalarObj f F (op ⊤)) ⟶
        externalSectionsPushforward f g F G,
      c.app (op ⊤) ≫ (externalSectionsTopIso f g F G).hom =
        ModuleCat.ofHom (externalGlobalSectionsTensor f g F G) ∧
      ∀ V : Y.Opens,
        ∃ eS : (scalarPresheaf g G ⋙
            MonoidalCategory.tensorLeft (scalarObj f F (op ⊤))).obj (op V) ≅
            ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k]
              scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)),
        ∃ eT : (externalSectionsPushforward f g F G).obj (op V) ≅
            scalarObj (pullback.fst f (V.ι ≫ g) ≫ f)
              (externalCupCoefficients f (V.ι ≫ g) F (G.restrict V.ι)) (op ⊤),
          c.app (op V) ≫ eT.hom = eS.hom ≫
            ModuleCat.ofHom
              (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι)) := by
  let c : scalarPresheaf g G ⋙
      MonoidalCategory.tensorLeft (scalarObj f F (op ⊤)) ⟶
      externalSectionsPushforward f g F G :=
    { app := fun V ↦ externalSectionsComponent f g F G V.unop
      naturality := fun _ _ i ↦ externalSectionsComponent_naturality f g F G i }
  refine ⟨c, ?_, ?_⟩
  · have ht : (externalSectionsTopIso f g F G).hom =
        𝟙 (scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (op ⊤)) := by
      change (scalarPresheaf (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).map (𝟙 (op ⊤)) = _
      exact (scalarPresheaf (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).map_id (op ⊤)
    rw [ht]
    erw [Category.comp_id]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    change tmulSection
        (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ ⊤) s)
        (scalarUnitSection g (pullback.snd f g) G ⊤ t) =
      tmulSection (M := (tensorPullback (pullback.fst f g)).obj F)
        (N := (tensorPullback (pullback.snd f g)).obj G)
        (tensorPullbackTopSection (pullback.fst f g) F s)
        (tensorPullbackTopSection (pullback.snd f g) G t)
    dsimp only [scalarPullbackGlobalSection, LinearMap.comp_apply, scalarUnitSection,
      scalarRestriction, tensorPullbackTopSection]
    congr 1
    exact (presheaf_map_id_apply (M := (tensorPullback (pullback.snd f g)).obj G)
        (homOfLE (by simp : ⊤ ≤ pullback.snd f g ⁻¹ᵁ ⊤)) _).symm
  · intro V
    exact externalSectionsComponent_openComparison f g F G V

end
end AlgebraicGeometry.Scheme.Modules
