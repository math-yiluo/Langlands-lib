/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Rep.Res

/-!
# Cyclic generators and norms under group isomorphisms

Adapted by Worker 66 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

section CyclicGenerator

variable {Q P : Type} [Group Q] [Group P]

/-- A generator remains a generator after applying a group isomorphism. -/
def map_cyclicGeneratorStatement (e : Q ≃* P) (g : Q)
    (hg : ∀ q : Q, q ∈ Subgroup.zpowers g) : Prop :=
    ∀ p : P, p ∈ Subgroup.zpowers (e g)

end CyclicGenerator

end
end Langlands.NYLL.LocalClassFieldTheory

namespace Langlands.NYLL.PortInternal.M100

noncomputable section

section GroupEquiv

variable {R Q P : Type} [CommRing R]
  [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]

/-- Source private `LocalClassFieldTheory.res_norm_eq` (M100.002): the norm of the
restriction of `A` along a group isomorphism `e` is the norm of `A`. -/
def d002Statement (e : Q ≃* P) (A : Rep R P) : Prop :=
    let Ares : Rep R Q :=
      Rep.res e.toMonoidHom A
    ModuleCat.ofHom Ares.norm.hom.toLinearMap =
      ModuleCat.ofHom A.norm.hom.toLinearMap

end GroupEquiv

end
end Langlands.NYLL.PortInternal.M100
