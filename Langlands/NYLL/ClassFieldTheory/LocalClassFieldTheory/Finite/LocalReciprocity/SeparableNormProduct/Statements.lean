/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 177: extracted M164.002 and M164.003 as Prop-valued statement
targets with a trailing `Statement` in their names, added the Langlands.NYLL
namespace prefix, and renamed the local instance M164.001 to
Langlands.NYLL.PortInternal.M164.d001, which remains a local instance.
The source proofs are omitted. The imports are unchanged.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.AlgebraTower

/-!
# Separable field norms as products of embeddings: statement targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
SeparableNormProduct.lean, lines 28–33 (local instance, M164.001),
37–46 (M164.002) and 69–74 (M164.003).
The ambient field `Ω` is only assumed separably closed, not normal over `k`.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The source's local `Fintype` instance on the embeddings of a finite separable
extension, built from a primitive-element power basis (M164.001). -/
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M164.d001
    {k E T : Type} [Field k] [Field E] [Field T]
    [Algebra k E] [Algebra k T]
    [FiniteDimensional k E] [Algebra.IsSeparable k E] :
    Fintype (E →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k E)

/-- The embeddings of a finite separable tower above a power-basis generator
split into embeddings of the lower field and their extensions. -/
def prod_embeddings_algebraMap_powerBasisGen_eqStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {L E : Type} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) : Prop :=
  ∏ σ : E →ₐ[k] Ω, σ (algebraMap L E pb.gen) =
    ((@Finset.univ (L →ₐ[k] Ω) (PowerBasis.AlgHom.fintype pb)).prod
      (fun σ => σ pb.gen)) ^ Module.finrank L E

/-- Mapping the norm of an element of a finite separable extension into a
separably closed field gives the product of all base-field embeddings. -/
def algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement
    (k Ω E : Type) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) : Prop :=
  algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x

end Langlands.NYLL.LocalClassFieldTheory
