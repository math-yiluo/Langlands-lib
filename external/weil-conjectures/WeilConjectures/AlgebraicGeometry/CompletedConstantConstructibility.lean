/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations

/-!
# Finite constant models in the completed ring-sheaf presentation

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3)
(auxiliary; not a blueprint node).

The original general condensed-ring interfaces remain publicly available. This adds the
same finite-stratification condition for modules over the actual inverse-limit ring sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Finite constructible strata with pro-etale locally constant finitely presented scalar
models, in the completed ring-sheaf presentation. The model is the ordinary extension
`B tensor_A P`, with no freeness or torsion-freeness condition on P. On each stratum both
modules are pulled back to the actual inverse-image ring before slice restriction; the
canonical immersion comparison identifies that ring with the completed ring on the stratum.
For qcqs schemes this is the constructibility condition; on other schemes the source uses
its affine-local version, for which the original general interface is retained.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3)
(auxiliary; not a blueprint node). -/
def IsCompletedConstantStratified (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (M : proEtaleRingModules X (adicLisseCompletedRing X I)) : Prop :=
  ∃ s : FiniteLocallyClosedStratification X,
    (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
    ∀ a : Fin s.n, ∃ V : Sieve (⊤_ (s.domain a).ProEt),
      V ∈ ProEt.topology (s.domain a) (⊤_ (s.domain a).ProEt) ∧
      ∀ (U : (s.domain a).ProEt) (f : U ⟶ ⊤_ (s.domain a).ProEt), V f →
        ∃ P : ModuleCat.{u + 1} A, Module.FinitePresentation A P ∧
          Nonempty
            ((SheafOfModules.overFunctor.{u + 1} _ U).obj
                ((proEtaleModuleInverseImage.{u} (s.immersion a)
                  (adicLisseCompletedRing X I)).obj M) ≅
              (SheafOfModules.overFunctor.{u + 1} _ U).obj
                ((proEtaleModuleInverseImage.{u} (s.immersion a)
                  (adicLisseCompletedRing X I)).obj
                    ((completedAdicChange.{u} X (CompletedConstantReduction.base X I)).obj
                      ((adicLisseConstantModules X A).obj P))))

end AlgebraicGeometry.Scheme
