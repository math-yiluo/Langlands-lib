/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim

Modified by Worker 376 (2026): this module states, as a `Prop`-valued
definition, the bijectivity assertion proved inside
`tensorPiEquivPiTensor'` of Imperial FLT, commit
923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean:182-273. The hypotheses are
those of the section variables at lines 182-184, quantified inside the
proposition with explicit universe names. The map is Mathlib's existing
`TensorProduct.piRightHom R R M N`, the map `i₃` of source line 207. The
module-system keywords are replaced by plain imports. No proof, no
equivalence and none of the auxiliary source declarations are included. The
upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring a finitely presented module with an arbitrary product

The statement target `RestrictedProduct.TensorPiComparison` asserts that, for a
finitely presented module `M` over a commutative ring `R` and an arbitrary
family of `R`-modules `N i`, Mathlib's canonical map
`M ⊗[R] (Π i, N i) → Π i, M ⊗[R] N i`, `m ⊗ f ↦ (i ↦ m ⊗ f i)`, is bijective.
This module only states the target; it proves nothing.
-/

namespace RestrictedProduct

universe uR uM uι uN

/-- For every commutative ring `R`, finitely presented `R`-module `M`, index type
`ι` and family of `R`-modules `N i`, the canonical map
`TensorProduct.piRightHom R R M N : M ⊗[R] (Π i, N i) →ₗ[R] Π i, M ⊗[R] N i`
is bijective. -/
def TensorPiComparison : Prop :=
  ∀ (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] {ι : Type uι} (N : ι → Type uN)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)],
    Function.Bijective (TensorProduct.piRightHom R R M N)

end RestrictedProduct
