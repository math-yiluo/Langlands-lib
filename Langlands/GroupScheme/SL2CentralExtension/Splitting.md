# Canonical lifts of the root groups

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). It constructs the homomorphic lifts `x′` and `y′` of the root
groups `x` and `y` into a central extension. These are the equivariant splittings over `U` and
`V` in Conrad's proof (his Lemma 4.3.2 gives them abstractly). The construction here is explicit:
as in Conrad's uniqueness argument, `x(u)` is the commutator `[h(t), x((t² - 1)⁻¹ u)]`. The lift
is the commutator of lifts of the two factors, which does not depend on the choice of lifts.

Throughout, `X : Ext S` is the point-level data from `Setup` and `b : Bool` selects the root
group.

## Contents

- `umap g`: restriction of global units along `g : V ⟶ T`, with `umap_coe` and `umap_hd`
  (restriction of `d = t² - 1`).
- `Loc.exists_unit_sq_sub_one`: fppf-locally on `T` there are units `t` and `d` with
  `d = t² - 1`. The polynomial `X (X² - 1)` is monic, so it takes a unit value locally.
- `Xt b t d u = comm (lam b t) (root b (d⁻¹ u))`. If `d = t² - 1`, then
  `Q (Xt b t d u) = root b u` (`Q_Xt`, by `Mat.lam_root_commutator`). `Xt` is natural
  (`Xt_res`), additive in `u` (`Xt_add`, using `commute_of_root` from `Unipotent`), and
  conjugation by a lift of `lam b s` replaces `u` by `s² u` (`Xt_conj`).
- Independence of the auxiliary unit. `δ = Xt b t d u · (Xt b t' d' u)⁻¹` is central with
  `Q δ = 1`, additive in `u` and natural (`δ_central`, `δ_add`, `δ_zero`, `δ_neg`, `δ_res`). It is
  invariant under `u ↦ s² u` (`δ_conj`). Taking `s` locally with `c = s² - 1` a unit gives
  `δ(c w) = δ(s² w) δ(w)⁻¹ = 1`, hence `δ_eq_one` and `Xt_indep`:
  `Xt b t d u = Xt b t' d' u`.
- `rootLift b u : T ⟶ E.X`: the local candidates `Xt b t d (ring g u)` glue (`Loc.glue`) to a
  global point (`exists_rootLift`, `rootLift_spec`). It is defined by choice. It satisfies
  `Q (rootLift b u) = root b u` (`Q_rootLift`), naturality `rootLift_res`, and it is a
  homomorphism from the additive group (`rootLift_add`, `rootLift_zero`, `rootLift_neg`,
  `rootLift_sub`).
- `rootLift_conj`: if `Q e = lam b s`, then `e · rootLift b u · e⁻¹ = rootLift b (s² u)`.
  `rootLift_central_of_Q`: any lift of `root b u` differs from `rootLift b u` by a central
  point.
