/-
This file belongs to the Library. It states a theorem of the NYLL library (M105.013) with the ring
and the module as explicit arguments, in the form the Library's old port of NYLL used, and proves it
by NYLL's `ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow`. NYLL
(https://github.com/n-yamaguchi-0729/NYLL) is Copyright (c) 2026 Naganori Yamaguchi and released
under the Apache License, Version 2.0; its licence and notice are in `licenses/NYLL/`.
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower

/-! # Completeness from a positive ideal power, with explicit ring and module -/

namespace Langlands.CommutativeAlgebra.AdicCompleteness

universe u v

/-- Completeness of a module for a positive power of an ideal implies its
completeness for the ideal. The ring and module are explicit arguments. -/
theorem isAdicComplete_of_isAdicComplete_pow (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) {n : ℕ} (hn : 0 < n)
    [IsAdicComplete (I ^ n) M] : IsAdicComplete I M :=
  _root_.ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow
    (R := R) (M := M) I hn

end Langlands.CommutativeAlgebra.AdicCompleteness
