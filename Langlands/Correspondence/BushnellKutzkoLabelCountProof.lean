import Langlands.Correspondence.BushnellKutzkoLabelCount
import Langlands.Correspondence.BushnellKutzkoExtendedLabels
import Langlands.Correspondence.BushnellKutzkoPolarPartCardinality

/-!
# Counting Bushnell–Kutzko labels by polar parts

The proof of `BushnellKutzkoLabelCountStatement` uses ordered support, successive
finite-field root counts, and the free Galois action on generating coefficients.
-/

namespace Langlands.Henniart

open LabelCounting

/-- Bushnell–Kutzko labels of final ramification index one are counted by the
polar-part number, including the level-zero polynomial labels. -/
theorem bushnellKutzkoLabelCount : BushnellKutzkoLabelCountStatement := by
  intro q hq n f hn hf hfn
  constructor
  · intro m hm
    have ha : 0 < n / f := Nat.div_pos (Nat.le_of_dvd hn hfn) hf
    exact encard_eq_polarPartCount_of_equiv hq hn hf hfn hm
      (extendedLabelsEquiv hq hm ha hf)
  · exact degenerateLabelSet_encard q n hq hn

end Langlands.Henniart
