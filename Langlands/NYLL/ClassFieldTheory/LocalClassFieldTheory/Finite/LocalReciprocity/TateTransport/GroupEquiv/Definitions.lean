/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.U002.Proofs

/-!
# Cyclic Tate short complexes under a group isomorphism

Adapted by Worker 66 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

The fixed-field realization of an abstract extension changes both the
presentation of its cyclic group and the presentation of its coefficient
module.  This file records the first of the two functorial comparisons needed
to transport the local class-field-axiom theorem: reindexing a representation
along a group isomorphism.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open CategoryTheory

section GroupEquiv

variable {R Q P : Type} [CommRing R]
  [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]

/-- Reindexing along a group isomorphism preserves the cyclic `H⁰`
short complex. -/
def normHomCompSubResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.normHomCompSub A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · simpa [Ares, i] using (Langlands.NYLL.PortInternal.M100.d002 e A).symm
  · rfl

/-- Reindexing along a group isomorphism preserves the cyclic `H⁻¹`
short complex. -/
def subCompNormHomResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.subCompNormHom A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · rfl
  · simpa [Ares, i] using (Langlands.NYLL.PortInternal.M100.d002 e A).symm

/-- Homology-level group-reindexing comparison in degree zero. -/
def normHomCompSubHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A (e g)).homology :=
  ShortComplex.homologyMapIso (normHomCompSubResEquivIso e A g)

/-- Homology-level group-reindexing comparison in degree minus one. -/
def subCompNormHomHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A (e g)).homology :=
  ShortComplex.homologyMapIso (subCompNormHomResEquivIso e A g)

end GroupEquiv

end
end Langlands.NYLL.LocalClassFieldTheory
