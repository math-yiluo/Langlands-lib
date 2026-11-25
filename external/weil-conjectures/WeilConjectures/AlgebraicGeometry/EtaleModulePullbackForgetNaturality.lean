/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Underlying abelian sheaves and etale module inverse image

Source: Stacks Project, Tags 03D3 and 03D7 (module inverse image and its adjunction),
and the coefficient compatibility used in Tags 03SA(3) and 09ZE.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Module inverse image commutes naturally with passage to underlying abelian sheaves.
Source: Stacks Project, Tags 03D3 and 03D7, and the restriction of module coefficients
in the proof of Tag 09ZE (first sentence).
(blueprint: lem-weil-pbc-etale-module-pullback-forget-naturality)

Proof: Unfold inverse image as left Kan extension of presheaves along the base-change functor,
followed by sheafification. The forgetful functor from modules to abelian groups preserves
colimits: a colimit abelian group carries the unique induced scalar operations, whose
relations are checked on the coprojections. Hence it commutes with the comma-category
colimits computing left Kan extension, naturally in the presheaf. It also preserves finite
limits and filtered colimits. The plus construction uses these limits for matching
families and filtered colimits over covering sieves, so forgetting commutes with each plus
construction and therefore with sheafification. Compose Mathlib
`sheafComposeNatIso` with `Functor.lanCompIsoOfPreserves`, whisker with the inclusion
of sheaves into presheaves, and use the associativity isomorphisms of functor composition
to identify the result with the two composites in the statement. Each comparison is natural in
module-sheaf morphisms, so the result is a natural isomorphism, not only an objectwise one.
There are no finiteness or torsion assumptions. For identity maps this is the canonical
identity comparison; zero rings and empty schemes give the same construction. -/
theorem exists_upperStar_forget₂_natIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty ((f)^*[ModuleCat.{u + 1} Λ] ⋙
      sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        (f)^*[AddCommGrpCat.{u + 1}]) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology U
  let L := (MorphismProperty.Over.pullback @Etale ⊤ f).op
  let P := sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Q := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let R := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj U
  have h : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := fun c ↦
      Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := U.lanCompIsoOfPreserves L
  refine ⟨?_⟩
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ U ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ U)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ U)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

end AlgebraicGeometry.Etale
