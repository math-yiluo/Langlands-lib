/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductForgetSupport

/-!
# The Künneth map on global sections computed on K-flat representatives

Source: Stacks Project, Tag 0F1E; blueprint chap-Smooth-purity
(blueprint: definition-kunneth-map--1).

The canonical external product `kunnethGlobalSectionsMap` is defined through adjunctions,
the Leray isomorphisms and the constant-sheaf equivalence over a separably closed point.
On K-flat representatives it is the localized pullback and tensor of global sections,
followed by the unit of the derived global sections and the comparison with the derived
external product. This identifies the adjoint construction of Stacks, Remark 0F1E, with its
construction through relative cup products (Stacks, Tag 0B6C), computed on resolutions.

This compatibility is recorded here as an input (`sorry`): it requires chain-level
descriptions of the derived adjunction `Lc^* ⊣ Rc_*`, of the monoidal structure of the
derived pullbacks, of the Leray isomorphisms and of the point tensor comparison, none of
which are formalized yet. It belongs to the chapter of the Künneth map
(blueprint: definition-kunneth-map--1).

## Main statements

- `kunnethGlobalSectionsMap_resolution`
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- On K-flat representatives `P` and `Q`, the canonical Künneth map on global sections is
the tensor localization of the totalized pullback and tensor of global sections, followed by
the unit of the derived global sections of the exterior complex and the inverse comparison
with the derived external product.

This input is not proved in the project: it is the compatibility of the adjoint
construction of the Künneth map (Stacks, Remark 0F1E) with its construction by pullback and
cup product of sections (Stacks, Tag 0B6C), computed on K-flat representatives. It belongs to
the chapter of the Künneth map (blueprint: definition-kunneth-map--1). -/
theorem kunnethGlobalSectionsMap_resolution
    (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L) :
    tensorHom
        ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnitQ P ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map eP.hom)
        ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnitQ Q ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map eQ.hom) ≫
      kunnethGlobalSectionsMap Λ (pullback.fst f g) (pullback.snd f g) f g
        pullback.condition.symm K L =
    Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
      DerivedCategory.Q.map (exteriorSectionsComplex (ModuleCat.{u + 1} Λ) f g P Q) ≫
      (Sheaf.Γ (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnitQ
        (exteriorSectionsComplexTarget (ModuleCat.{u + 1} Λ) f g P Q) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (pullback f g)).map
        ((exteriorProductResolutionIso (ModuleCat.{u + 1} Λ) f g P Q hP hQ).inv ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ)
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f g)).leftDerivedFunctor.map eP.hom)
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f g)).leftDerivedFunctor.map
              eQ.hom)) := by
  sorry

end AlgebraicGeometry.Etale
