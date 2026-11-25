/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!

# Quasi-domination

Let `x : X ⟶ S` and `y : Y ⟶ S` be morphisms of schemes with `y` separated. A
*quasi-domination of `X` over `Y`* is a morphism `hom : U ⟶ Y` over `S`, defined on a dense
open `U ⊆ X`, whose graph is closed in the full fibre product `Y ×ₛ X`. Closedness is
demanded in `Y ×ₛ X`, not merely in `Y ×ₛ U`, where it would be automatic from separatedness
of `y`; it is exactly this stronger requirement that is propagated by the partial-section
extension theorem `AlgebraicGeometry.exists_admissibleBlowup_extend_section`.

## Main definitions

- `AlgebraicGeometry.QuasiDomination`: the data of a quasi-domination of `X` over `Y`;
- `AlgebraicGeometry.QuasiDomination.graph`: the graph `U ⟶ Y ×ₛ X` of a quasi-domination;
- `AlgebraicGeometry.QuasiDomination.Extends`: a quasi-domination extends a morphism defined
  on a smaller open (blueprint: `definition-quasi-domination--1`).

## Main results

- `AlgebraicGeometry.QuasiDomination.of_isSeparated`: a morphism to a separated target is a
  quasi-domination of its own source (blueprint:
  `corollary-extension-proper-target--1`);
- `AlgebraicGeometry.QuasiDomination.U_eq_top`: a quasi-domination over a universally closed
  target is defined everywhere (blueprint:
  `lemma:nagata-conrad-quasi-domination-proper-target`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

/-- Blueprint `definition-quasi-domination--1`:
Quasi-domination.

A quasi-domination of `x : X ⟶ S` over a separated `y : Y ⟶ S` is a morphism `hom : U ⟶ Y`
over `S`, defined on a dense open `U ⊆ X`, whose graph `U ⟶ Y ×ₛ X` has closed range.

```text
    U ──hom──→ Y
    │          │
U.ι │          │ y
    ↓          ↓
    X ───x───→ S
```

The graph is the morphism `U ⟶ Y ×ₛ X` induced by this square, and the condition is that
its range be closed.
-/
structure QuasiDomination (x : X ⟶ S) (y : Y ⟶ S) [IsSeparated y] where
  /-- The dense open of `X` on which the quasi-domination is defined. -/
  U : X.Opens
  /-- The open `U` is dense in `X`. -/
  dense_coe : Dense (U : Set X)
  /-- The morphism to `Y` defined on `U`. -/
  hom : U.toScheme ⟶ Y
  /-- The morphism `hom` is a morphism over `S`. -/
  comm : hom ≫ y = U.ι ≫ x
  /-- The graph of `hom` is closed in the full fibre product `Y ×ₛ X`. -/
  isClosed_range_lift : IsClosed (Set.range (pullback.lift hom U.ι comm))

namespace QuasiDomination

variable {x : X ⟶ S} {y : Y ⟶ S} [IsSeparated y]

/-- The graph `U ⟶ Y ×ₛ X` of a quasi-domination. -/
def graph (q : QuasiDomination x y) : q.U.toScheme ⟶ pullback y x :=
  pullback.lift q.hom q.U.ι q.comm

@[reassoc (attr := simp)]
theorem graph_fst (q : QuasiDomination x y) : q.graph ≫ pullback.fst y x = q.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd (q : QuasiDomination x y) : q.graph ≫ pullback.snd y x = q.U.ι :=
  pullback.lift_snd _ _ _

/-- The graph of a quasi-domination has closed range in `Y ×ₛ X`. This is the defining
condition, restated in terms of `AlgebraicGeometry.QuasiDomination.graph`. -/
theorem isClosed_range_graph (q : QuasiDomination x y) : IsClosed (Set.range q.graph) :=
  q.isClosed_range_lift

/-- Blueprint `definition-quasi-domination--1`: the quasi-domination `q` *extends* the
morphism `f' : U' ⟶ Y` defined on an open `U' ⊆ X`, i.e. `U' ⊆ U` and `q.hom` restricts to
`f'` on `U'`. -/
def Extends (q : QuasiDomination x y) {U' : X.Opens} (f' : U'.toScheme ⟶ Y) : Prop :=
  ∃ h : U' ≤ q.U, X.homOfLE h ≫ q.hom = f'

/-- A quasi-domination extends its own morphism. -/
theorem extends_hom (q : QuasiDomination x y) : q.Extends q.hom :=
  ⟨le_rfl, by simp⟩

/-- The graph of a morphism to a separated target is closed when the other leg is an
isomorphism: the graph is then a section of the separated `pullback.snd y x`, hence a closed
immersion. -/
theorem isClosed_range_lift_of_isIso {W : Scheme.{u}} (hom : W ⟶ Y) (j : W ⟶ X) [IsIso j]
    (h : hom ≫ y = j ≫ x) : IsClosed (Set.range (pullback.lift hom j h)) := by
  have : IsClosedImmersion (pullback.lift hom j h ≫ pullback.snd y x) := by
    rw [pullback.lift_snd]; infer_instance
  have : IsClosedImmersion (pullback.lift hom j h) :=
    IsClosedImmersion.of_comp (pullback.lift hom j h) (pullback.snd y x)
  exact (pullback.lift hom j h).isClosedEmbedding.isClosed_range

/-- Blueprint `corollary-extension-proper-target--1`: **a morphism to a
separated target is a quasi-domination of its own source**.

For a separated `y : Y ⟶ S` and any `hom : U ⟶ Y`, the pair `(U, hom)` is a quasi-domination
of `U` over `Y`: the open `U ⊆ U` is dense, and the graph is a section of the separated
`Y ×ₛ U ⟶ U`, hence a closed immersion. -/
def of_isSeparated {U : Scheme.{u}} (y : Y ⟶ S) [IsSeparated y] (hom : U ⟶ Y) :
    QuasiDomination (hom ≫ y) y where
  U := ⊤
  dense_coe := by simp
  hom := (⊤ : U.Opens).ι ≫ hom
  comm := by rw [Category.assoc]
  isClosed_range_lift :=
    have : IsIso ((⊤ : U.Opens).ι) := inferInstanceAs (IsIso U.topIso.hom)
    isClosed_range_lift_of_isIso _ _ _

/-- Blueprint `prose-A-14`: **a quasi-domination
over a universally closed target is defined everywhere**.

The projection `pullback.snd y x : Y ×ₛ X ⟶ X` is universally closed, being a base change of
`y`, so the closed range of the graph maps onto a closed subset of `X`. That subset is `U`,
which is therefore closed as well as dense, hence all of `X`. -/
theorem U_eq_top [UniversallyClosed y] (q : QuasiDomination x y) : q.U = ⊤ := by
  have hcl : IsClosed ((pullback.snd y x).base '' Set.range q.graph) :=
    (pullback.snd y x).isClosedMap _ q.isClosed_range_graph
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, q.graph_snd,
    Scheme.Opens.range_ι] at hcl
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_top, ← q.dense_coe.closure_eq, hcl.closure_eq]

end QuasiDomination

end AlgebraicGeometry

end
