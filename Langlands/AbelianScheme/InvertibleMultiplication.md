# Multiplication by an invertible index over an arbitrary base

The definition `Langlands.AbelianScheme.invertibleMultiplicationIsogeny`
bundles the actual multiplication homomorphism with its proved isogeny
property, as an element of `{f : A ⟶ A // IsIsogeny f}`. The simp lemma
`invertibleMultiplicationIsogeny_val` identifies its map with `n • 𝟙 A`.

The internal adapter proves
`Langlands.AbelianScheme.multiplication_isIsogeny_of_isUnit`.
Let `S` be an arbitrary scheme, `A` an actual abelian scheme over `S`, and
`n` a natural number whose image in `Γ(S, ⊤)` is a unit. Then the actual group
scheme homomorphism `GroupScheme.multiplication A.toGrp (n : ℤ)` is an
isogeny in the published finite, flat and surjective sense.

The proof reuses the published field theorem
`multiplication_isIsogeny_of_ne_zero` and the published
`GroupScheme.fiberwiseIsogeny` criterion. For each residue-field point `s`,
the global unit maps to a unit in `κ(s)` through the map on global sections
and `Scheme.ΓSpecIso`. Thus `(n : κ(s))` is nonzero. The actual abelian scheme
obtained by base change to `Spec κ(s)` satisfies the field theorem.
`GroupScheme.multiplication_baseChange` identifies its multiplication map
with the required fibre homomorphism. The fibrewise criterion gives all
three isogeny properties over `S`.

This is a deduction from those existing Library results, with no new
geometric hypothesis or external source assertion. The index remains
invertible on `S`; the arbitrary-characteristic nonzero-integer
`MultiplicationIsogenyStatement` is not proved here. No noetherian,
affine, nonempty or reduced condition is imposed on the base. Positivity of
`n` is unnecessary: in the empty-base case a zero index may be invertible
in the zero ring and the fibrewise proof remains valid.
