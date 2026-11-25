/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
public import WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Kernel transport to an open étale chart

Source: Stacks Project, Tags 03DR, 03DT and 0GKU.
(blueprint: lem-fd-frobenius-linear-kernel-etale-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction of small abelian étale sheaves along an open immersion is left exact:
it is a pushforward along a continuous functor, hence preserves all finite limits. -/
instance etaleOpenSmallRestriction_preservesFiniteLimits {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (etaleOpenSmallRestriction j) := by
  let : (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).IsContinuous
      U.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (inferInstance : Etale j) le_rfl
  unfold etaleOpenSmallRestriction
  infer_instance

/-- Restriction of small abelian étale sheaves along an open immersion is additive, as it
preserves binary products. -/
instance etaleOpenSmallRestriction_additive {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (etaleOpenSmallRestriction j).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- An isomorphism of quasi-coherent modules induces an isomorphism of the associated
étale tensor-section sheaves, with components `((tensorPullback v).map α).app ⊤`. -/
noncomputable def Scheme.Modules.etaleTensorSectionsSheafMapIso {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (α : M ≅ N) :
    etaleTensorSectionsSheaf M ≅ etaleTensorSectionsSheaf N :=
  ObjectProperty.isoMk _ ((etaleTensorSectionsPresheafFunctor X).mapIso α)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Restriction to an open étale chart transports F, its scalar law, and its kernel.
The transported endomorphism `F'` is the conjugate of the restriction of `F` by an
isomorphism `Φ` between the restricted étale sheaf of `E` and the étale sheaf of `G`.

Source: Stacks Project, Tags 03DR (35.8.0.1), 03DT, and 0GKU, the passage to a
trivializing open in the proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-linear-kernel-etale-pullback).

Proof: use etaleTensorSectionsSheaf_openIdentification to identify restriction of
the given sheaf with the tensor-section sheaf of the ordinary module restriction.
The unit-normalized tensor/abstract pullback comparison identifies this restriction
with E_V; compose it with the supplied isomorphism to G and apply the tensor-section
functor. These natural comparisons are linear over each test object's section ring,
as their prescribed components are evaluations of module isomorphisms. Conjugate the
restricted endomorphism by their composite to define F_V. Linearity of the comparison
and its inverse transports the scalar-power law. Étale inverse image is site
restriction, hence preserves kernels; universe lifting of abelian sheaves also
preserves the sectionwise kernel universal property. Combine these comparisons with
the kernel isomorphism induced by conjugating F-1. Identity and empty open immersions
use the same comparisons; no characteristic, finite-rank, or affineness is required.
-/
theorem frobenius_linear_kernel_etale_pullback
    (p : ℕ) (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (V : S.Etale) [IsOpenImmersion V.hom] (G : V.left.Modules) [G.IsQuasicoherent]
    (α : (Modules.tensorPullback V.hom).obj E ≅ G) :
    ∃ (Φ : (etaleOpenSmallRestriction V.hom).obj (Modules.etaleTensorSectionsSheaf E) ≅
        Modules.etaleTensorSectionsSheaf G)
      (F' : Modules.etaleTensorSectionsSheaf G ⟶ Modules.etaleTensorSectionsSheaf G),
      F' = Φ.inv ≫ (etaleOpenSmallRestriction V.hom).map F ≫ Φ.hom ∧
      (∀ (W : V.left.Etale) (a : Γ(W.left, ⊤))
        (m : Γ((Modules.tensorPullback W.hom).obj G, ⊤)),
        F'.hom.app (op W) ((((Modules.tensorPullback W.hom).obj G).smul a).asHom.hom m) =
          (((Modules.tensorPullback W.hom).obj G).smul (a ^ p)).asHom.hom
            (F'.hom.app (op W) m)) ∧
      Nonempty
        (((Etale.upperStar AddCommGrpCat.{u + 1} V.hom).obj
          ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (kernel (F - 𝟙 _)))) ≅
          ((sheafCompose V.left.smallEtaleTopology
            AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (kernel (F' - 𝟙 _)))) := by
  obtain ⟨e, he⟩ := etaleTensorSectionsSheaf_openIdentification V.hom E
  let β := ((Classical.choose (Modules.exists_tensorPullbackAdjunction V.hom)).leftAdjointUniq
    (Modules.restrictAdjunction V.hom)).app E
  let Φ := e ≪≫ Modules.etaleTensorSectionsSheafMapIso (β.symm ≪≫ α)
  let R := etaleOpenSmallRestriction V.hom
  have hΦ (W : V.left.Etale) : Φ.hom.hom.app (op W) =
      (((Modules.tensorSectionsComp W.hom V.hom).inv.app E).app ⊤ ≫
        ((Modules.tensorPullback W.hom).map β.hom).app ⊤) ≫
        ((Modules.tensorPullback W.hom).map (β.inv ≫ α.hom)).app ⊤ := by
    have h1 : Φ.hom.hom.app (op W) = e.hom.hom.app (op W) ≫
        ((Modules.tensorPullback W.hom).map (β.inv ≫ α.hom)).app ⊤ := rfl
    rw [h1, he W]
    rfl
  have hlin (W : V.left.Etale) (a : Γ(W.left, ⊤))
      (x : Γ((Modules.tensorPullback (W.hom ≫ V.hom)).obj E, ⊤)) :
      Φ.hom.hom.app (op W) ((((Modules.tensorPullback (W.hom ≫ V.hom)).obj E).smul a).asHom.hom x) =
        (((Modules.tensorPullback W.hom).obj G).smul a).asHom.hom (Φ.hom.hom.app (op W) x) := by
    rw [hΦ]
    exact (congrArg _ ((congrArg _ (Modules.Hom.app_smul
      ((Modules.tensorSectionsComp W.hom V.hom).inv.app E) a x)).trans
      (Modules.Hom.app_smul ((Modules.tensorPullback W.hom).map β.hom) a _))).trans
      (Modules.Hom.app_smul ((Modules.tensorPullback W.hom).map (β.inv ≫ α.hom)) a _)
  refine ⟨Φ, Φ.inv ≫ R.map F ≫ Φ.hom, rfl, fun W a m ↦ ?_, ⟨?_⟩⟩
  · let Ψ := ((sheafToPresheaf _ _).mapIso Φ).app (op W)
    obtain ⟨x, rfl⟩ : ∃ x, Φ.hom.hom.app (op W) x = m := ⟨Ψ.inv m, Ψ.inv_hom_id_apply m⟩
    have hF' (y) : (Φ.inv ≫ R.map F ≫ Φ.hom).hom.app (op W) (Φ.hom.hom.app (op W) y) =
        Φ.hom.hom.app (op W) (F.hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj W)) y) :=
      congrArg Ψ.hom (congrArg (F.hom.app _) (Ψ.hom_inv_id_apply y))
    exact ((congrArg _ (hlin W a x).symm).trans (hF' _)).trans
      ((congrArg _ (hF _ a x)).trans ((hlin W (a ^ p) _).trans (congrArg _ (hF' x).symm)))
  · refine (Etale.upperStarIsoLocalizationRestriction _ V.hom inferInstance).app _ ≪≫
      (sheafCompose V.left.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
        (PreservesKernel.iso R (F - 𝟙 _) ≪≫ kernel.mapIso _ _ Φ Φ ?_)
    simp [Preadditive.comp_sub, Preadditive.sub_comp]

end AlgebraicGeometry.Scheme
