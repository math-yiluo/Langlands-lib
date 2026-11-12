/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# The NYLL profinite-integer closure model

Modified by Worker 120: extract M008.001–018 from the pinned NYLL source,
prefix the public namespace, give the private support and anonymous instances
stable `PortInternal.M008` names, and omit the unused TopologicalGeneration
import. The closure model, instance constructions and reduction map are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

open scoped Topology

namespace Langlands.NYLL.PortInternal.M008

structure d001 where
  modulus : ℕ
  positive : 0 < modulus

instance d002 (i : d001) : NeZero i.modulus :=
  ⟨Nat.ne_of_gt i.positive⟩

def d003 (n : ℕ) (hn : 0 < n) : d001 :=
  ⟨n, hn⟩

abbrev d004 : Type 0 :=
  ∀ i : d001, ZMod i.modulus

def d005 : ℤ →+* d004 where
  toFun a i := (a : ZMod i.modulus)
  map_zero' := by
    funext i
    exact Int.cast_zero
  map_one' := by
    funext i
    exact Int.cast_one
  map_add' a b := by
    funext i
    exact Int.cast_add a b
  map_mul' a b := by
    funext i
    exact Int.cast_mul a b

def d006 : Subring d004 :=
  d005.range

abbrev d007 : Type 0 :=
  d006.topologicalClosure

end Langlands.NYLL.PortInternal.M008

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

/-- The profinite completion `ℤ̂ = lim ℤ/nℤ` over all positive moduli.

This is deliberately a `def`, rather than an `abbrev`: clients use the
reduction maps instead of depending on the closure subtype. -/
def ZHat : Type 0 :=
  d007

/-- The closure model equips `ZHat` with its canonical commutative ring structure. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d009 : CommRing ZHat := by
  change CommRing d007
  infer_instance

/-- The closure model equips `ZHat` with its subspace topology. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d010 : TopologicalSpace ZHat := by
  change TopologicalSpace d007
  infer_instance

/-- Ring operations on `ZHat` are continuous for the closure-model topology. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d011 : IsTopologicalRing ZHat := by
  change IsTopologicalRing d007
  infer_instance

/-- The closure-model topology on `ZHat` is Hausdorff. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d012 : T2Space ZHat := by
  change T2Space d007
  infer_instance

/-- The profinite integer model is totally disconnected. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d013 : TotallyDisconnectedSpace ZHat := by
  change TotallyDisconnectedSpace d007
  infer_instance

/-- The profinite integer closure model is compact. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d014 : CompactSpace ZHat :=
  Topology.IsClosedEmbedding.compactSpace
    (Subring.isClosed_topologicalClosure d006).isClosedEmbedding_subtypeVal

/-- `ZHat` as Mathlib's bundled profinite additive group. -/
def zHatProfiniteAddGrp : ProfiniteAddGrp :=
  ProfiniteAddGrp.of ZHat

/-- The multiplicative presentation of `ZHat` remains totally disconnected. -/
instance _root_.Langlands.NYLL.PortInternal.M008.d016 : TotallyDisconnectedSpace (Multiplicative ZHat) := by
  change TotallyDisconnectedSpace ZHat
  infer_instance

/-- The multiplicative presentation of `ZHat` as Mathlib's bundled profinite
group.  Its multiplication is addition in `ZHat`. -/
def zHatMulProfiniteGrp : ProfiniteGrp :=
  ProfiniteGrp.of (Multiplicative ZHat)

/-- The canonical continuous reduction `ℤ̂ → ℤ/nℤ`. -/
def zHatReduction (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ZHat (ZMod n) where
  toFun x := (show d007 from x).1 (d003 n hn)
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    change Continuous
      (fun x : d007 => x.1 (d003 n hn))
    exact (continuous_apply (d003 n hn)).comp continuous_subtype_val

end Langlands.NYLL.ClassFormation
