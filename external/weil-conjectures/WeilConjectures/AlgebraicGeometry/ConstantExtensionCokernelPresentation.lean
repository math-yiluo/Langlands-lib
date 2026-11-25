/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.ConstantExtensionCokernelAux
import WeilConjectures.AlgebraicGeometry.ConstantExtensionPresentationLift
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.AlgebraicGeometry.EtaleShortExactLocalLift
import WeilConjectures.ConstructibleSheaf.Biproduct

/-!
# Cokernel presentations of extensions with finite constant outer terms

Source: Stacks Project, Tag 093U, extension argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Locally an extension with finite constant outer terms is a cokernel of a morphism
between constant sheaves, with finitely generated source.
Source: Stacks Project, Tag 093U, extension argument, up to the pushout diagram.
(blueprint: lem-pc-constant-extension-cokernel-presentation)

Proof: Remove empty schemes from covers. On each nonempty scheme choose constant values
M and N for the outer terms. Their geometric stalks identify with M and N, so these modules
are finitely generated. Present N as a quotient of a finite free module P with kernel K.
Since the coefficient ring is finite, P and K are finite sets, hence K is finitely generated.
Local surjectivity of the epimorphism to the constant sheaf N allows the finitely many
chosen generators to be lifted simultaneously on an etale cover. The lifts define a map
r from the constant sheaf P to the middle term. Its restriction to the constant sheaf K
factors through the first term as a map g. Exactness of the constant sheaf functor makes
this the pushout of the constant presentation of N along g. Equivalently, the middle term
is the cokernel of (-g,inclusion) from the constant sheaf K to the constant sheaf M plus P.
Indeed the map (a,v) to a+r(v) is epi, and its kernel consists exactly of (-g(k),k).
The direct sum is the constant sheaf of M plus P. The resulting map need not be induced
by a module homomorphism; no local constancy of its cokernel is asserted here.
For an empty scheme choose the empty covering family. -/
theorem exists_constantExtension_cokernelPresentation {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧
        ∃ φ : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
          Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_constantExtension_presentation_lift hS
  refine ⟨𝒰, fun i ↦ ?_⟩
  exact finite_cokernelPresentation_of_local_presentation hS (h𝒰 i)

end AlgebraicGeometry.Scheme
