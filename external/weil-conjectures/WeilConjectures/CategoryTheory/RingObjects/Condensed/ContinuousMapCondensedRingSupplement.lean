/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Topology.ContinuousMapCondensedRing

/-!
# Continuous-map condensed rings with arbitrary coefficient universe

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-condensed-ring/`
`def-sfb-continuous-map-condensed-ring.md`
(blueprint: proposition-pro-etale-site-separably-closed--3).

The upstream continuous-map construction fixes the coefficient ring in `Type 0`.
These universe-polymorphic versions retain the same sections, restrictions and canonical
ring-object construction, allowing independent universes for the profinite sets and ring.
The common coefficient universe is `max u v + 1`, so sheafification is available.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace Profinite


end Profinite
