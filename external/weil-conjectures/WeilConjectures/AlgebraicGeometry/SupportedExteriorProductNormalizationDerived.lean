/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNormalization
public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductExistence
public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSectionsResolution
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyKFlatResolution

/-!
# The derived supported exterior product

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

The supported exterior product κ is the unique morphism normalized on K-flat representatives
and injective support resolutions by `IsResolutionSupportedExteriorProduct`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section Derived

/-- The direct supported-section pairing has a unique derived extension with its
K-flat/injective-resolution normalization. Source: the nested blueprint unit cited
above (blueprint: proposition-purity-vector-bundles).
Proof: choose K-flat representatives of the two inputs, resolve supported sections by
injectives, and totalize the ordinary pairing. The kernel vanishing on the two pulled-back
complements makes its target the product-support complex. The usual resolution comparison
maps identify the resulting morphisms for different resolutions. To check independence
and uniqueness one can use flat support-acyclic resolutions: these are obtained by the
flasque resolution of flat sheaves, with finite truncation using finite cohomological
dimension on the separated finite-type schemes. Comparison with injective support
resolutions makes the two input units invertible there. The normalization therefore
determines the map. Its comparison on arbitrary K-flat representatives is the same
chain-level pairing followed by the injective-resolution units. -/
theorem existsUnique_resolutionSupportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    ∃! κ : (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).obj K.obj ⊗
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) j).obj L.obj ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A)
        (supportedProductImmersion f g i j)).obj
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj),
      IsResolutionSupportedExteriorProduct (ModuleCat.{u + 1} A) f g i j K.obj L.obj κ :=
  existsUnique_isResolutionSupportedExteriorProduct_of_resolutions (ModuleCat.{u + 1} A) f g i j
    (by
      intro P hP n hn
      obtain ⟨I, φ, hφ, hI, hunit⟩ :=
        exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport
          A k f i P hP n hn
      refine ⟨I, φ, hφ, hI, ?_⟩
      have := hunit
      dsimp only [exteriorSupportResolutionUnit, Functor.rightDerivedFunctorUnitQ]
      infer_instance)
    (by
      intro Q hQ n hn
      obtain ⟨I, φ, hφ, hI, hunit⟩ :=
        exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport
          A k g j Q hQ n hn
      refine ⟨I, φ, hφ, hI, ?_⟩
      have := hunit
      dsimp only [exteriorSupportResolutionUnit, Functor.rightDerivedFunctorUnitQ]
      infer_instance)
    K.obj L.obj K.property L.property

/-- The supported exterior product κ, defined anew by the unique derived extension
of pullback and tensor of supported sections, normalized on K-flat representatives
and injective support resolutions. Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-smooth-purity/sec-the-trace-map-of-affine-space/
sk-prop-an/def-pur-supported-exterior-product.md
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def resolutionSupportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).obj K.obj ⊗
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) j).obj L.obj ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A)
        (supportedProductImmersion f g i j)).obj
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) :=
  (existsUnique_resolutionSupportedExteriorProduct A k f g i j K L hF).exists.choose

/-- The representative characterization of κ. Source: the nested blueprint unit cited
above (blueprint: proposition-purity-vector-bundles).
Proof: take the normalized element of the unique-existence theorem used in the definition. -/
theorem resolutionSupportedExteriorProduct_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    IsResolutionSupportedExteriorProduct (ModuleCat.{u + 1} A) f g i j K.obj L.obj
      (resolutionSupportedExteriorProduct A k f g i j K L hF) := by
  exact (existsUnique_resolutionSupportedExteriorProduct A k f g i j K L hF).exists.choose_spec

/-- Forgetting the output support after κ is the ordinary exterior product after
forgetting both input supports. Source: the nested blueprint unit cited above
(blueprint: proposition-purity-vector-bundles).
Proof: the ordinary kernel lift followed by its inclusion is the pullback and tensor
of sections. The same equality holds on every bidegree of the signed total complexes.
Apply the K-flat tensor localization and the injective-resolution units to this identity.
The support inclusions commute with these units by naturality of right derivation.
The resulting ordinary pairing is the recorded canonical Künneth map. Comparison on
support-acyclic resolutions gives the claimed identity for the derived objects. -/
theorem resolutionSupportedExteriorProduct_forgetSupport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    resolutionSupportedExteriorProduct A k f g i j K L hF ≫
      (Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk
            (supportedProductImmersion f g i j).openComplement.ι)))).app
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) =
    tensorHom
      ((Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι X.smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk i.openComplement.ι)))).app K.obj)
      ((Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι Y.smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk j.openComplement.ι)))).app L.obj) ≫
      kunnethGlobalSectionsMap A (pullback.fst f g) (pullback.snd f g) f g
        pullback.condition.symm K.obj L.obj := by
  obtain ⟨n, hn⟩ := K.property
  obtain ⟨m, hm⟩ := L.property
  obtain ⟨I₀, eI₀, hI₀, huI₀⟩ := exists_kFlat_supportResolution_iso (ModuleCat.{u + 1} A) i
    (by
      intro P hP n hn
      obtain ⟨I, φ, hφ, hI, hunit⟩ :=
        exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport
          A k f i P hP n hn
      refine ⟨I, φ, hφ, hI, ?_⟩
      have := hunit
      dsimp only [exteriorSupportResolutionUnit, Functor.rightDerivedFunctorUnitQ]
      infer_instance)
    K.obj n hn
  obtain ⟨J₀, eJ₀, hJ₀, huJ₀⟩ := exists_kFlat_supportResolution_iso (ModuleCat.{u + 1} A) j
    (by
      intro Q hQ n hn
      obtain ⟨I, φ, hφ, hI, hunit⟩ :=
        exists_quasiIso_kFlat_isIso_rightDerivedFunctorUnit_globalSectionsWithSupport
          A k g j Q hQ n hn
      refine ⟨I, φ, hφ, hI, ?_⟩
      have := hunit
      dsimp only [exteriorSupportResolutionUnit, Functor.rightDerivedFunctorUnitQ]
      infer_instance)
    L.obj m hm
  have hnorm := (isResolutionSupportedExteriorProduct_iff (ModuleCat.{u + 1} A) f g i j K.obj L.obj
    _).1 (resolutionSupportedExteriorProduct_normalization A k f g i j K L hF) I₀ J₀ hI₀ hJ₀ eI₀ eJ₀
  rw [← cancel_epi (tensorHom
    (exteriorSupportResolutionUnit (ModuleCat.{u + 1} A) i I₀ ≫
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).map eI₀.hom)
    (exteriorSupportResolutionUnit (ModuleCat.{u + 1} A) j J₀ ≫
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) j).map eJ₀.hom)),
    reassoc_of% hnorm]
  erw [resolutionSupportedExteriorPairing_comp_forgetSupport (ModuleCat.{u + 1} A) f g i j I₀ J₀
    hI₀ hJ₀ (M := externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj)
    (derivedTensorHom (ModuleCat.{u + 1} A)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map eI₀.hom)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map eJ₀.hom))]
  rw [tensorHom_comp_tensorHom_assoc, exteriorSupportResolutionUnit_comp_forgetSupport,
    exteriorSupportResolutionUnit_comp_forgetSupport, ← tensorHom_comp_tensorHom_assoc]
  erw [kunnethGlobalSectionsMap_resolution A f g I₀ J₀ hI₀ hJ₀ eI₀ eJ₀]
  rfl

end Derived

end AlgebraicGeometry.Etale
