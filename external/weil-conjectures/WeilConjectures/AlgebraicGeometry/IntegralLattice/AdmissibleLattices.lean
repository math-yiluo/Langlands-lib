/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible

/-!
# Admissible integral lattices for smooth base change

The integral object and its rationalization isomorphism are data. Both admissibility
conditions are properties, and the output condition uses one interval for every level
and all four ambient operations, with intrinsic constructibility at each cohomology sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (T : Scheme.{u}) [IsNoetherian T]
variable (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
variable (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- An integral object with a chosen isomorphism in the raw rational category.
There are no retained finite-level origins. -/
structure IntegralLattice (K : PbcRationalDerivedCategory l E T hdim hl) where
  /-- The integral constructible derived-complete object. -/
  integral : PbcIntegralCategory l E T hdim hl
  /-- The specified identification after raw scalar localization. -/
  rationalization : (pbcRationalization T (pbcIntegralDatum l E)
    (pbcUniformizer l E)).obj integral ≅ K

/-- The derived reduction along the actual completed-ring projection, transported
through the canonical associated-module-sheaf equivalence. The index is n+1. -/
def IntegralLattice.reduction {K : PbcRationalDerivedCategory l E T hdim hl}
    (L : IntegralLattice l E T hdim hl K) (n : ℕ) :
    PbcWitnessAmbient T (pbcIntegralDatum l E) n :=
  ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence).inverse.obj
    ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj L.integral.obj)

end AlgebraicGeometry.Scheme
