/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U018.Proofs

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension (absolute data)

Modified by Worker 123: extract the data commands M168.003 and M168.005 of the
pinned NYLL `ResidueAbsoluteFrobenius` source and prefix the namespace with
`Langlands.NYLL`. The source's private M168.002 `residueFrobeniusLimitPoint`
is written in place as the `toFun` of M168.003, its only use among the adapted
rows, so it does not become a separate declaration. The source import is
replaced by the published `Langlands.NYLL` M168.001 data and the published
M167.018 proof. The source's `variable` block, universes, `open` commands,
types, bodies and noncomputable section are retained. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The compatible Frobenius coordinates as a continuous homomorphism into
the finite-Galois inverse limit.

The compatible family attached to one profinite integer (the source's private
`residueFrobeniusLimitPoint`) is written in place as `toFun`. -/
def residueFrobeniusToLimit :
    ZHatMul →ₜ* limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  toFun z :=
    { val := fun E => finiteResidueFrobeniusIntermediate k Omega E.unop z
      property := by
        intro E F f
        algebraize [Subsemiring.inclusion <| leOfHom f.1]
        have : IsScalarTower k F.unop E.unop :=
          IsScalarTower.of_algebraMap_eq (congrFun rfl)
        let : Finite F.unop := Module.finite_of_finite k
        let : Finite E.unop := Module.finite_of_finite k
        change AlgEquiv.restrictNormalHom F.unop
            (finiteResidueFrobeniusFromZHat k E.unop z) =
          finiteResidueFrobeniusFromZHat k F.unop z
        exact restrictNormalHom_finiteResidueFrobeniusFromZHat
          (k := k) (E := F.unop) (F := E.unop) z }
  map_one' := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_mul x y
  continuous_toFun := by
    have hcontinuous (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
          inferInstance (krullTopology k E.unop)
          (finiteResidueFrobeniusIntermediate k Omega E.unop) :=
      (finiteResidueFrobeniusIntermediate k Omega E.unop).continuous_toFun
    let (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        TopologicalSpace (E.unop ≃ₐ[k] E.unop) :=
      ((InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega).obj E).toProfinite.toTop.str
    apply Continuous.subtype_mk
    exact continuous_pi fun E => by
      change @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
        inferInstance inferInstance
        (finiteResidueFrobeniusIntermediate k Omega E.unop)
      rw [show
        (inferInstance : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) =
          krullTopology k E.unop by
        change (⊥ : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) = krullTopology k E.unop
        exact (@DiscreteTopology.eq_bot _ (krullTopology k E.unop) inferInstance).symm]
      exact hcontinuous E

/-- The canonical continuous Frobenius-parameter homomorphism
`ℤ̂ → Gal(Omega/k)` for a Galois algebraic extension of a finite field. -/
def residueAbsoluteFrobenius : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit k Omega).symm).comp
    (residueFrobeniusToLimit k Omega)

end
end Langlands.NYLL.LocalClassFieldTheory
