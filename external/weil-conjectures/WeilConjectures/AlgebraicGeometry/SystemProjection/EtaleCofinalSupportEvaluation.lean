/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData

/-! # Evaluation of the normalized cofinal support comparison

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.Etale.SystemProjection.CofinalRepeatSupport.kappa
  WeilConjectures.SemilinearSections.systemRing WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

end AlgebraicGeometry.Etale.SystemProjection
