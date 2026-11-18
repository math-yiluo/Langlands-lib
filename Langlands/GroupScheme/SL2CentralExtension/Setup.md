# Central extensions of `SL₂` on points

Worker 65. Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). It sets up the functor-of-points framework in which the existence
part of the proof is carried out.

## Restriction and group identities

- `res g = Matrix.SpecialLinearGroup.map (ring g)` restricts matrices along `g : V ⟶ T`, with
  `res_comp` (by `rfl`) and `res_id`.
- Identities in an arbitrary group: `commutator_mul_central` (central factors do not change a
  commutator), `commutator_mul_right` (`[a, bc] = [a, b][a, c]` if `[a, c]` is central),
  `commutator_mul_left` (`[ac, b] = [a, b][c, b]` if `[c, b]` is central) and
  `conj_commutator`. Here `[a, b] = a b a⁻¹ b⁻¹`.

## The structure `Ext`

`Ext S` packages the point-level data of a central extension of `SL₂` used in the proof. It
consists of:

- a group scheme `E` over `S`;
- group homomorphisms `Q T : (T ⟶ E.X) →* Mat.SL2 Γ(T.left, ⊤)` for all test objects `T`,
  natural in `T` (`Q_nat`: `Q V (g ≫ e) = res g (Q T e)`);
- `central`: a point with `Q T e = 1` commutes with every point of `E` over `T`;
- `lift`: every matrix over `T` lifts along `Q` fppf-locally on `T`;
- `sep`: two matrices over `T` that agree fppf-locally are equal.

The target statement's data give such a structure (`toExt` in
`SpecialLinearCentralExtensionSplitProof`); `Q` is `q` followed by `slEquiv`.

## Results

- `central_of_eq`: two lifts of the same matrix differ by a central point. `commutator_eq`: the
  commutator of two lifts depends only on the lifted matrices. `commutator_central`: if the
  images commute, the commutator of the lifts is central. `comp_commutator` and `comp_conj`:
  restriction commutes with commutators and conjugation.
- `comm m₁ m₂ : T ⟶ E.X`: the commutator of fppf-local lifts of two matrices, glued to a global
  point by `Loc.glue` (`exists_comm`). It is defined by choice; `comm_spec` characterizes it on
  every test map `g` with given lifts. `comm_eq`: if global lifts exist, `comm` is their
  commutator. `comm_res`: `comm` is compatible with restriction. `Q_comm`: `Q` maps `comm m₁ m₂`
  to the matrix commutator `[m₁, m₂]`.
- `ext_loc`: points of `E` that agree fppf-locally are equal.
