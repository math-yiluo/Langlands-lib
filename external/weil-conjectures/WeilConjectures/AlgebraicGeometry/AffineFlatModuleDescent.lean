/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.RingTheory.FlatModuleTensorModel
import WeilConjectures.RingTheory.FpModuleTensorModelComparison

/-!
# Eventual flatness for finitely presented modules over affine inverse limits

Source: Stacks Project, Algebra, Lemma 10.168.1 (Tag 02JO), part (3)
(blueprint: lem-pc-affine-flat-module-descent).
-/

@[expose] public section

universe v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/--
Source: Stacks Project, Algebra, Lemma 10.168.1 (Tag 02JO), part (3)
(blueprint: lem-pc-affine-flat-module-descent).

1. Finite presentation over the base gives finite presentation of the
   prescribed algebra and module stages; the directed colimit criteria
   identify their limits. Apply `lem-weil-pbc-limit-module-finite-presentation`
   to obtain a finite-type Noetherian approximation.
2. At each prime of the limit algebra, localization-colimit and
   localization-tensor lemmas identify the localized approximations and their
   module colimit with the localization of the given flat module.
3. Apply `lem-weil-pbc-colimit-eventually-flat` to each localized system,
   obtaining a stage whose localized module is flat at that prime.
4. `lem-weil-pbc-openness-of-flatness` gives open flat loci at each stage;
   tensor base change and the affine local criterion make them persistent.
5. Quasi-compactness of the limit spectrum makes finitely many inverse images
   of those open loci cover it, hence one sufficiently late inverse image.
6. The complement at that stage is a closed set. Its ideal generates the unit
   ideal at the limit, and the finite unit relation lifts to a later stage,
   whose entire spectrum lies in its flat locus.
7. The prime-local criterion `lem-pc-affine-sections-flat-over-base` makes
   that Noetherian model module flat over its model base ring.
8. Finite-presentation algebra descent through
   `lem-weil-pbc-colimit-category-fp-algebras` and module-map descent through
   `lem-pc-fp-module-map-descent-affine` compare the model algebra and module
   with every sufficiently late prescribed stage by isomorphisms.
9. `lem-weil-pbc-flat-module-base-change` transports model flatness across
   those isomorphisms to every later prescribed module.
-/
theorem exists_eventually_flat_of_finitePresentation
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {Ai Bi Ni : Type w}
    [CommRing Ai] [CommRing Bi] [AddCommMonoid Ni]
    [Algebra (F.obj i : Type v) Ai] [Algebra (F.obj i : Type v) Bi]
    [Module Bi Ni] [Module.FinitePresentation Bi Ni]
    [Algebra.FinitePresentation (F.obj i : Type v) Ai]
    [Algebra.FinitePresentation (F.obj i : Type v) Bi]
    (f : Ai →ₐ[(F.obj i : Type v)] Bi)
    (hflat : letI : Module Ai Ni := Module.compHom Ni f.toRingHom
      letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
        (c.ι.app i).hom.toAlgebra
      letI : Algebra Ai ((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai) :=
        Algebra.TensorProduct.rightAlgebra
      Module.Flat ((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai)
        (((c.pt : Type v) ⊗[(F.obj i : Type v)] Ai) ⊗[Ai] Ni)) :
    (letI : Module Ai Ni := Module.compHom Ni f.toRingHom;
    ∃ j₀ : I, i ≤ j₀ ∧
      ∀ (j : I) (h₀ : i ≤ j₀) (h₁ : j₀ ≤ j),
        (letI : Algebra (F.obj i : Type v) (F.obj j : Type v) :=
        (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra;
          letI : Algebra Ai ((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai) :=
            Algebra.TensorProduct.rightAlgebra;
          Module.Flat ((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai)
            (((F.obj j : Type v) ⊗[(F.obj i : Type v)] Ai) ⊗[Ai] Ni))) := by
  let : Algebra (F.obj i : Type v) (c.pt : Type v) :=
    (c.ι.app i).hom.toAlgebra
  obtain ⟨P, Q, L, cP, cQ, aPQ, cL, mQL, aP, hP, hQ, hL, hPL, e, he, eM⟩ :=
    exists_flat_module_tensor_model (C := (c.pt : Type v)) f hflat
  let : CommRing P := cP
  let : CommRing Q := cQ
  let : Algebra P Q := aPQ
  let : AddCommMonoid L := cL
  let : Module Q L := mQL
  let : Algebra.FinitePresentation ℤ P := hP
  let : Algebra.FinitePresentation P Q := hQ
  let : Module.FinitePresentation Q L := hL
  obtain ⟨j₀, hi, hmodel⟩ :=
    exists_eventually_tensor_model_equiv F c hc f P Q L aP e he eM
  let : Module Ai Ni := Module.compHom Ni f.toRingHom
  let : Module P L := Module.compHom L (algebraMap P Q)
  have : Module.Flat P L := hPL
  refine ⟨j₀, hi, ?_⟩
  intro j h₀ h₁
  let : Algebra (F.obj i : Type v) (F.obj j : Type v) :=
    (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra
  let : Algebra Ai ((F.obj j : Type v) ⊗[F.obj i] Ai) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨aPj, ⟨ej⟩⟩ := hmodel j h₀ h₁
  let := aPj
  exact Module.Flat.of_linearEquiv ej.symm

end AlgebraicGeometry
