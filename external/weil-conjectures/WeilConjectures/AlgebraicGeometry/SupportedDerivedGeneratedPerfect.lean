/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfectCore

/-! # Building supported derived objects from a perfect complex

Source: Stacks Project, proof of Lemma 48.4.3(3) (Tag 0E4G), using Lemmas 36.15.4
(Tag 0A9A) and 13.37.3 (Tag 09SN)
(blueprint: lem-sc-supported-derived-generated-perfect).

Coproducts are specified by colimiting cofans, so the statement does not require a chosen
coproduct instance. Distinguished triangles are taken in the ambient derived category;
the sequence objects lie in its full quasi-coherent subcategory.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- Every quasi-coherent derived object supported off a quasi-compact open is built from
one perfect supported complex by successive cones and a sequential homotopy colimit.
Source: Stacks Project, proof of Lemma 48.4.3(3), Tags 0E4G, 0A9A and 09SN
(blueprint: lem-sc-supported-derived-generated-perfect).

Proof:
1. Apply `lem-pc-supported-perfect-generator` to the closed complement of V to obtain E.
2. Support and quasi-coherence are preserved by shifts and cones, using the long exact
cohomology sequence. Direct sums exist by `lem-pc-derived-qcoh-direct-sums` and agree
with ambient sums; their cohomology is computed by sums by
`lem-pc-derived-ambient-direct-sums`. Thus sums preserve support. By
`lem-pc-perfect-object-compact`, E is compact in the quasi-coherent category and in its
supported full subcategory, whose sums agree. It generates that subcategory in the sense
of `def-pc-generators`.
3. Apply `lem-pc-compact-generators-build-objects` to this singleton compact generating
family. Rotate its transition triangles: their cones are sums of shifts of E, since
shifting such a sum again gives a sum of shifts. Prepend a zero term; its first cone is
the original first term, a sum of shifts of E. Prepending zero leaves the telescope
unchanged. The telescope triangle is precisely the sequential derived colimit asserted.
-/
theorem supported_derived_generated_perfect (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
      (∀ (k : ℤ) (y : Y), y ∈ V →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y))) ∧
      ∀ Q : schemeDerivedQCohCategory Y,
        (∀ (k : ℤ) (y : Y), y ∈ V →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) →
        ∃ (X : ℕ → schemeDerivedQCohCategory Y)
          (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj),
          IsZero (X 0).obj ∧
          (∀ n : ℕ, ∃ (I : Type u) (m : I → ℤ)
            (C : Cofan (fun i : I ↦ E.obj⟦m i⟧)), Nonempty (IsColimit C) ∧
            ∃ (a : (X (n + 1)).obj ⟶ C.pt)
              (b : C.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
              Triangle.mk (t n) a b ∈ distTriang (schemeDerivedCategory Y)) ∧
          ∃ (S : Cofan (fun n : ℕ ↦ (X n).obj)), Nonempty (IsColimit S) ∧
            ∃ (s : S.pt ⟶ S.pt) (q : S.pt ⟶ Q.obj)
              (r : Q.obj ⟶ S.pt⟦(1 : ℤ)⟧),
              (∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1)) ∧
              Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang (schemeDerivedCategory Y) := by
  obtain ⟨htri, ⟨E, hEperf, hEsupp, hdet⟩⟩ :=
    supported_perfect_generator Y (V : Set Y)ᶜ (by
      simpa using V.isOpen.isClosed_compl) (by simpa using hV)
  refine ⟨E, hEperf, ?_, ?_⟩
  · intro k y hy
    exact hEsupp k y (by simpa using hy)
  · intro Q hQ
    apply supported_derived_generated_perfect_core Y V E Q htri
      (perfectObjectCompact Y E hEperf) hEsupp
    · intro K hK
      exact hdet K (fun k y hy ↦ hK k y (by
        simpa only [Set.mem_compl_iff, not_not, SetLike.mem_coe] using hy))
    · intro k y hy
      exact hQ k y (by simpa only [Set.mem_compl_iff, not_not, SetLike.mem_coe] using hy)

end AlgebraicGeometry
