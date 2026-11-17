import Langlands.BushnellKutzko.Labels
import Langlands.Correspondence.HenniartPolarPart

/-!
# Counting Bushnell–Kutzko labels by the polar-part number

The statement of Lemma `lem:BKlabels` of the operator route note
(`operator-numerical-llc-route-2026-11-16`): the labels `(p, φ)` of Bushnell–Kutzko 1994
((1.13), (3.7)) with `e(p) = 1` are counted by `polarPartCount`. See the paired Markdown file.
-/

namespace Langlands.Henniart

open Langlands.BushnellKutzko Langlands.Henniart.Numerical

/-- For every prime power `q` and all `n ≥ 1`, `f ≥ 1` with `f ∣ n`:
for every `m ≥ 1` the set `{(p, φ) ∈ P̃_m(n/f, f; q) : e(p) = 1}` has
`polarPartCount q n f (f * m)` elements, and `P̃_0(1, n; q) = 𝔍(n, q)` has
`polarPartCount q n n 0` elements. -/
def BushnellKutzkoLabelCountStatement : Prop :=
  ∀ q : ℕ, IsPrimePow q →
    ∀ n f : ℕ, 1 ≤ n → 1 ≤ f → f ∣ n →
      (∀ m : ℕ, 1 ≤ m →
        {x ∈ extendedLabelSet m (n / f) f q | x.1.e = 1}.encard =
          (polarPartCount q n f (f * m) : ℕ∞)) ∧
      (degenerateLabelSet n q).encard = (polarPartCount q n n 0 : ℕ∞)

end Langlands.Henniart
