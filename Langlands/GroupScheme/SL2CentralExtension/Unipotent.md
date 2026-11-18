# Lifts of matrices in one root group commute

Worker 65. Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). It proves the commutativity of the preimages `U′` and `V′` of the
two root groups in a central extension. Conrad shows that a bi-additive commutator pairing
vanishes. The route here is a different, purely algebraic one with fppf-local units; it uses no
density argument.

Throughout, `X : Ext S` is the point-level data from `Setup` and `b : Bool` selects the root
group (`Mat.root false = x`, `Mat.root true = y`).

## Contents

- `Q_mul_res`, `Q_inv_res`, `Q_conj_res`: `Q` of products, inverses and conjugates of local
  lifts. `commutator_central_res`: lifts of commuting matrices have a central commutator.
  `root_commute`: matrices of one root group commute.
- `β b u₁ u₂ = comm (root b u₁) (root b u₂)`: the commutator of fppf-local lifts of `root b u₁`
  and `root b u₂`, a central point of `E` with `Q_β : Q (β b u₁ u₂) = 1`. It is natural
  (`β_res`) and additive in each variable (`β_add_left`, `β_add_right`), by the commutator
  identities of `Setup`.
- `β_conj`: conjugating by a lift of `lam b s` scales both entries by `s²` (`Mat.lam_root_conj`).
  Since `β` is central, `β b (s² u₁) (s² u₂) = β b u₁ u₂`.
- `β_unit`: `β b (s u₁) (s u₂) = β b u₁ u₂` for every unit `s`. Fppf-locally, `s` has a square
  root (`Loc.exists_root` for `X² - s`), and `β_conj` applies.
- `β_eq_one_of_units`: if `r`, `1 + r` and `r² + r + 1` are units, then `β b u v = 1` for all
  `u`, `v`. Expanding `β((1 + r) u, (1 + r) v) = β(u, v)` by bi-additivity and using
  `β(r u, r v) = β(u, v)` gives `β(u, r v) β(r u, v) β(u, v) = 1`. Applied to `r v` and `v`,
  this gives `β(u, (r² + r + 1) w) = 1` for all `w`. Since `r² + r + 1` is a unit, `β(u, v) = 1`.
- `β_eq_one`: `β b u₁ u₂ = 1` always. The polynomial `X (X + 1) (X² + X + 1)` is monic, so
  fppf-locally it takes a unit value `r` (`Loc.exists_isUnit_eval`). Then `r`, `1 + r` and
  `r² + r + 1` are units and `β_eq_one_of_units` applies. The conclusion descends by `Loc.ext`.
- `commute_of_root`: lifts of `root b u₁` and `root b u₂` commute.
