# Residue roots and nonzero generic torus restriction

This internal supporting unit combines the published quasi-split centralizer
comparison and root restriction results with canonical integral-torus
character specialization. It introduces no independent literature assertion.
All declarations have arbitrary universe parameter `u` and impose no
restriction on the field or residue characteristic.

For a field extension `L/k`, let `G` be quasi-split and let `a : S → G`
be a maximal split torus over `k`. Let `j : U → G_L` be a split maximal
torus over `L`, supplied with an actual map `f : S_L → U` satisfying
`f ≫ j = a_L`. The theorem
`IsQuasiSplit.root_restrict_ne_zero_of_extension_maximalTorus` proves that
every actual adjoint root `β` of `j` has nonzero restriction `f ≫ β`.
The affine and locally finite type instances on `G` are explicit.
No presentation of `U` as a base change from `k` is needed.

The proof first extends `S` to a maximal torus over `k`. Quasi-splitness
identifies that torus with the full centralizer of `S`. Base change
preserves this representability and closedness, and the representative
remains a torus. The published maximal-torus comparison then identifies
the supplied `j` with the full centralizer of `S_L`, since `j` contains
`S_L`. The same-field centralizer root theorem gives nonvanishing.

The construction `IsQuasiSplit.rootRestrictionOfExtensionMaximalTorus`
therefore sends every actual root of `j` to an actual root of the original
`a`, with no roots discarded. It restricts the character along `f`, then
uses the canonical split-torus character base-change equivalence to
recover the original character over `k`. The published weight-restriction
and field-extension comparison identify it as a root.
`rootRestrictionOfExtensionMaximalTorus_baseChange` states that its
base-changed character is exactly `f ≫ β`. This generalizes the published
`IsQuasiSplit.rootRestriction`, which requires a containing maximal torus
already given over the lower field.

For the integral consequence, let `R` be a local integral domain with
fraction field `K`. Supply split integral torus data `A` and `B` over
`R`, possibly in different ambient group models, and an actual integral
morphism `ρ : A.torus → B.torus`. Let `χ` be a character of the specified
generic torus of `B`. Let a lower field `k` map to `L = ResidueField R`.
Supply a quasi-split group `H/k`, its maximal split torus `a : S₀ → H`,
an actual isomorphism `eS : (S₀)_L ≅ A.specialFibre`, and an actual
maximal-torus inclusion `j : B.specialFibre → H_L`. The comparison
equation is precisely

```text
eS.hom ≫ (residue base change of ρ) ≫ j = a_L.
```

If the canonical specialization of `χ` through `B` is an actual root of
`j`, then `generic_restriction_ne_zero_of_quasiSplit_residue_root` proves
that `χ` restricts nontrivially along `A.genericFibreMap B ρ`.
The residue torus of `B` is split by base change of its integral splitting.
The preceding extension-field theorem therefore gives nonvanishing after
precomposing with `eS`. Vanishing of the residue restriction would
contradict this. Finally `generic_restriction_ne_zero_iff` transports
nonvanishing through the canonical specialization built from these same
integral tori.

If `k` is finite and `H` is connected reductive,
`generic_restriction_ne_zero_of_finite_residue_root` obtains quasi-splitness
from `finiteFieldQuasiSplit` and applies this criterion. The affine and
locally finite type instances remain explicit.

The actual integral morphism, residue comparison isomorphism, maximality,
comparison equation, and root membership are hypotheses, not existence
conclusions of this unit. No arbitrary lattice map replaces them. The
module does not supply the recovered models or prove the host chamber
statement.
