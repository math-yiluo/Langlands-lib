/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.FormalModuleSupportSucc
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Constant support of a coherent formal module

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 30.26.11 (Tag 0CYV),
first sentence of the proof of (1)
(blueprint: lem-weil-pbc-formal-system-support-constant).
-/

@[expose] public section

universe u

open Opposite

namespace AlgebraicGeometry

/-- Every positive level of a coherent formal module has the same support as level one.
The index `op n` denotes level `n + 1`, and `op 0` denotes level one. Support is the
nonzero-stalk locus, following def-weil-pbc-closed-subset-proper-over-base (2).

Source: Stacks Project, Tag 0CYV, first sentence of the proof of (1)
(blueprint: lem-weil-pbc-formal-system-support-constant).

Proof: (1) Fix a positive level k and a point x. Put A = O_{X,x}, a = I_x and
M = (F_{k+1})_x. The defining conditions of def-weil-pbc-coherent-formal-module and
lem-weil-pbc-ideal-module-product-stalk (1), (4) identify (F_k)_x with M/a^k M and give
 a^(k+1) M = 0. Stalks preserve the quotient isomorphism by def-weil-pbc-module-stalk.
(2) If M/a^k M = 0, then M = a^k M = a^(2k) M = 0, since 2k >= k+1.
Conversely, M = 0 gives M/a^k M = 0. Thus consecutive levels have zero stalks at
exactly the same points; no finiteness or Nakayama lemma is required.
(3) By the support definition, consecutive levels have equal supports. Induction on
the level gives equality with level one. The Noetherian and coherence hypotheses
are retained from the source even though this argument does not use them. -/
theorem formalModule_support_eq {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (n : ℕ) :
    {x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((F.obj.obj (op 0)).presheaf.stalk x)} := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (formalModule_support_succ I F n).trans ih

end AlgebraicGeometry
