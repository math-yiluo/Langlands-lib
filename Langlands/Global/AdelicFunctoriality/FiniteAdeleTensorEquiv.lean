/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper

Modified by Worker 98 (2026): adapt the equivalence packaging of Imperial FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:254-270, to the Library's
canonical tensor map and proved bijectivity, with independent field universes,
Mathlib's left-factor algebra and the scoped finite-adele inclusion algebra.
Add underlying-map and pure-tensor evaluation lemmas. The upstream license is
retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorProof

/-! # The canonical finite-adele tensor algebra equivalence -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteAdeleExtension

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The canonical `A_K`-algebra equivalence `A_K ⊗[K] L ≃ₐ[A_K] A_L`. -/
def finiteAdeleTensorEquiv :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L ≃ₐ[FiniteAdeleRing (𝓞 K) K] FiniteAdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (finiteAdeleTensorMap K L) (finiteAdeleTensorMapBijective_proof K L)

/-- The equivalence has exactly the published canonical algebra map. -/
@[simp] theorem finiteAdeleTensorEquiv_toAlgHom :
    (finiteAdeleTensorEquiv K L).toAlgHom = finiteAdeleTensorMap K L := rfl

variable {K L}

/-- The equivalence evaluates by the canonical tensor map on every tensor. -/
theorem finiteAdeleTensorEquiv_apply (z : FiniteAdeleRing (𝓞 K) K ⊗[K] L) :
    finiteAdeleTensorEquiv K L z = finiteAdeleTensorMap K L z := rfl

/-- The equivalence sends a pure tensor to the inclusion times the diagonal. -/
@[simp] theorem finiteAdeleTensorEquiv_tmul (x : FiniteAdeleRing (𝓞 K) K) (l : L) :
    finiteAdeleTensorEquiv K L (x ⊗ₜ[K] l) =
      finiteAdeleInclusion x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l :=
  finiteAdeleTensorMap_tmul x l

/-- The coordinate of the equivalence on a pure tensor at a finite place of `L`. -/
theorem finiteAdeleTensorEquiv_tmul_apply (x : FiniteAdeleRing (𝓞 K) K) (l : L)
    (q : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleTensorEquiv K L (x ⊗ₜ[K] l) q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) *
        algebraMap L (q.adicCompletion L) l :=
  finiteAdeleTensorMap_tmul_apply x l q

end Langlands.Global.AdelicFunctoriality
