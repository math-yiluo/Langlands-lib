/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective

/-!
# Effective etale descent for finite etale schemes

Source: Stacks Project, Descent, Tags 023V, 0245, 02LA, 02VN, and the
blueprint's `lem-galois-descent` (blueprint: lem-galois-descent).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- For a surjective etale map `g : Y' ⟶ Y`, the base-change functor from
finite etale schemes over `Y` to finite etale schemes over `Y'` with descent
data is an equivalence (blueprint: lem-galois-descent).

The pullback square identifies each image with `P ×_Y Y'`; the transport
equation says its datum is the canonical comparison of the two pullbacks,
and the final equation says morphisms are sent to their base changes.

Proof plan from the node, following Stacks:

1. The singleton etale surjection is an etale covering and hence an fpqc
   covering by `lem-weil-pbc-fpqc-finer-than-etale` (Topologies, Tag 022C).
   This requires a quasi-compact covering family, not a quasi-compact `g`.
2. Base change preserves finite etale morphisms
   (`def-weil-pbc-finite-etale-category`). Identify both iterated pullbacks
   with `P ×_Y Y''` by `def-pc-fibre-product`. Over the triple product the
   comparisons satisfy the cocycle; the same identifications show every
   base-changed morphism is compatible (`proposition-jacobian-over-ground-field--1`).
3. Apply `lem-galois-fpqc-morphisms-descend` (Descent, Tag 02W0) to the
   covering in Step 1. Compatible maps between the canonical objects
   descend uniquely, giving full faithfulness.
4. A finite morphism is affine (`def-weil-finite-integral-morphism` and
   `pqf-def-affine-morphism`). Apply
   `lem-galois-fpqc-affine-descent-effective` (Descent, Tag 0245) to obtain
   `P` over `Y` and an isomorphism of its canonical datum with the given one.
5. Its base change is finite etale since it is isomorphic to the given
   finite etale object. Descend these properties by
   `lem-weil-pbc-fpqc-descend-finite` (Tag 02LA) and
   `lem-galois-fpqc-descend-etale` (Tag 02VN). Thus `P` is finite etale,
   and the compatible isomorphism from Step 4 gives essential surjectivity.
6. Choose such preimages. Full faithfulness supplies a quasi-inverse on
   morphisms and makes the chosen isomorphisms natural, giving equivalence. -/
theorem finiteEtaleDescent {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g] :
    ∃ (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
      (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left),
      Nonempty F.IsEquivalence ∧
      (∀ P : Y.FiniteEtale,
        ∃ hq : q P ≫ P.obj.hom = (F.obj P).obj.V.hom ≫ g,
          IsPullback (q P) (F.obj P).obj.V.hom P.obj.hom g ∧
          ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y')
            (h : f₁ ≫ g = f₂ ≫ g) (z : Over.mk f₁ ⟶ (F.obj P).obj.V),
            ((F.obj P).obj.datum.transport f₁ f₂ h z).left ≫ q P =
              z.left ≫ q P) ∧
      ∀ P Q : Y.FiniteEtale, ∀ f : P ⟶ Q,
        (F.map f).hom.hom.left ≫ q Q = q P ≫ f.hom.left := by
  obtain ⟨F, q, h⟩ := finiteEtaleDescent_data g
  obtain ⟨hff⟩ := finiteEtaleDescent_fullyFaithful g F q h
  have : F.Faithful := hff.faithful
  have : F.Full := hff.full
  have : F.EssSurj := finiteEtaleDescent_essSurj g F q h
  exact ⟨F, q, ⟨{}⟩, h⟩

end AlgebraicGeometry
