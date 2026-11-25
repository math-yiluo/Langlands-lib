/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.AdicLisseModule

/-!
# Adic-lisse modules over completed constant coefficients

Source: Stacks Project, proetale.tex, Tag 09BT, Definition `definition-adic`, clause (3)
(blueprint: def-weil-pbc-adic-lisse-module).

The index `n : ℕ` denotes exponent `n + 1`. All limits are genuine limits of sheaves.
Linearity over completed coefficients is expressed on the quotient projections, locally
lifting a scalar in a quotient to a section of the constant coefficient ring. This also
works over inverse-image coefficients without commuting inverse image with infinite limits.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Quotient-module sheaves, with quotient transitions, before completing.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def adicLisseModuleSystem (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) :
    ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (adicLisseRing X A) :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    (adicLisseConstantModules X A).obj
      (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))) (fun n : ℕ ↦
    (adicLisseConstantModules X A).map
      (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1))))

/-- The completed constant module as a sheaf over the constant coefficient ring.
Its extension to completed scalars is specified by quotient projections in the local model.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseCompletedModule (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) := limit (adicLisseModuleSystem X I N)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- A local isomorphism to the completed constant module, linear over the completed
coefficient sheaf. The abelian-sheaf isomorphism is tested on every quotient projection.
For a completed scalar `r`, locally lift its `n`th residue to a constant-ring section `a`;
the displayed equality says that the projection of `r • x` is `a` times that of `x`.
The quotient-ring maps are epimorphisms, so such lifts exist locally. This is precisely
componentwise completed-scalar linearity; it also specifies the action after inverse image.
The limit in module sheaves has the sectionwise compatible-family underlying abelian sheaf.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def IsAdicLisseLocalModel (X : Scheme.{u})
    (R₀ Rhat : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (Rₙ : ℕ → Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ρ : ∀ n : ℕ, R₀ ⟶ Rₙ n) (π : ∀ n : ℕ, Rhat ⟶ Rₙ n)
    (S : ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R₀)
    (F : ringedSiteModules.{u + 1} Rhat) (V : X.ProEt) : Prop :=
  ∃ e : ((SheafOfModules.toSheaf Rhat).obj F).over V ≅
      ((SheafOfModules.toSheaf R₀).obj (limit S)).over V,
    ∀ (n : ℕ) (W : (Over V)ᵒᵖ)
      (r : Rhat.obj.obj (op W.unop.left)) (a : R₀.obj.obj (op W.unop.left))
      (x : F.val.obj (op W.unop.left)),
      (ρ n).hom.app (op W.unop.left) a = (π n).hom.app (op W.unop.left) r →
        (limit.π S (op n)).val.app (op W.unop.left)
            (e.hom.hom.app W (r • x)) =
          a • (limit.π S (op n)).val.app (op W.unop.left) (e.hom.hom.app W x)

/-- Finite-type adic lissity on the small pro-etale site. Completeness is Mathlib's
`IsAdicComplete`, equivalent to bijectivity of the canonical residue-family map.
`Module.Finite A (N / IN)` is equivalently finite generation over `A/I`: the scalar
map is surjective and `I` annihilates this quotient. There is no freeness condition.
The sieve is a covering of the final object, hence a pro-etale covering of `X`.
Source: Tag 09BT, clause (3) (blueprint: def-weil-pbc-adic-lisse-module). -/
def IsAdicLisseModule (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (F : ringedSiteModules.{u + 1}
      ((adicLisseForget X).obj (adicLisseCompletedRing X I))) : Prop :=
  ∃ T : Sieve (⊤_ X.ProEt), T ∈ ProEt.topology X (⊤_ X.ProEt) ∧
    ∀ (V : X.ProEt) (f : V ⟶ ⊤_ X.ProEt), T f →
      ∃ N : ModuleCat.{u + 1} A, IsAdicComplete I N ∧
        Module.Finite A (N ⧸ (I • ⊤ : Submodule A N)) ∧
        IsAdicLisseLocalModel X (adicLisseRing X A)
          ((adicLisseForget X).obj (adicLisseCompletedRing X I))
          (fun n ↦ (adicLisseForget X).obj ((adicLisseRingSystem X I).obj (op n)))
          (fun n ↦ (adicLisseForget X).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
          (fun n ↦ (adicLisseForget X).map (limit.π (adicLisseRingSystem X I) (op n)))
          (adicLisseModuleSystem X I N) F V

/-- Relative finite-type adic lissity over the inverse image of completed coefficients.
Take inverse images of each quotient-module sheaf first and then their inverse limit.
The scalar test uses the image of each completed-ring projection, so its action factors
through the canonical map to the limit of inverse-image quotient rings. No preservation
of an infinite limit by inverse image is assumed, including for the identity morphism.
Source: Tag 09BT and the relative local-model clause of the blueprint
(blueprint: def-weil-pbc-adic-lisse-module). -/
def IsRelativelyAdicLisseModule {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ringedSiteModules.{u + 1} ((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing X I)))) : Prop :=
  ∃ T : Sieve (⊤_ Y.ProEt), T ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
    ∀ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt), T f →
      ∃ N : ModuleCat.{u + 1} A, IsAdicComplete I N ∧
        Module.Finite A (N ⧸ (I • ⊤ : Submodule A N)) ∧
        IsAdicLisseLocalModel Y
          ((adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (adicLisseConstantRing X A)))
          ((adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (adicLisseCompletedRing X I)))
          (fun n ↦ (adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              ((adicLisseRingSystem X I).obj (op n))))
          (fun n ↦ (adicLisseForget Y).map
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
              ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (fun n ↦ (adicLisseForget Y).map
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
              (limit.π (adicLisseRingSystem X I) (op n))))
          (adicLisseModuleSystem X I N ⋙
            proEtaleModuleInverseImage g (adicLisseConstantRing X A)) F V

end AlgebraicGeometry.Scheme
