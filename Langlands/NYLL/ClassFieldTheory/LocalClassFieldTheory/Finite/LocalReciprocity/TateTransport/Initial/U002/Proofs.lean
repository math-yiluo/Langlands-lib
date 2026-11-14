/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of the source-private theorem res_norm_eq (M100.002)
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Rename it to the public
Langlands.NYLL.PortInternal.M100.d002 (no longer private) and import only the
published TateTransport Initial Statements module. Omit the unused namespace
openings, noncomputable section and section name, keep the source section
variables, and state the theorem as the published Statement applied to the
source parameters. The proof body is unchanged. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.Statements

/-!
# Norms under restriction along a group isomorphism

The proof that restricting a representation along a group isomorphism does
not change its norm map.
-/

namespace Langlands.NYLL.PortInternal.M100

variable {R Q P : Type} [CommRing R]
  [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]

/-- Source private `LocalClassFieldTheory.res_norm_eq` (M100.002): the norm of the
restriction of `A` along a group isomorphism `e` is the norm of `A`. -/
theorem d002 (e : Q ≃* P) (A : Rep R P) : d002Statement e A := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  apply congrArg ModuleCat.ofHom
  change Representation.norm Ares.ρ = Representation.norm A.ρ
  simp only [Representation.norm]
  exact Fintype.sum_equiv e.toEquiv
    (fun q : Q => Ares.ρ q)
    (fun p : P => A.ρ p) (fun _ => rfl)

end Langlands.NYLL.PortInternal.M100
