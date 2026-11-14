# The Hopf algebra of integral functions

Module `Langlands.GroupScheme.IntegralModel.Smoothening.Hopf`. This is a helper
module of the proof of `Langlands.GroupScheme.IntegralModel.SmootheningStatement`.

Let `R` be a discrete valuation ring with fraction field `K`, `A` a commutative
`R`-algebra and `B = integralFunctions R K A ⊆ K ⊗[R] A`. When `A` is a Hopf
algebra, the comultiplication, counit and antipode of `A` extend to `B`, and `B`
becomes a commutative Hopf algebra with `incl : A → B` a bialgebra map. No
flatness of `A` and no finite generation of `B` is used. In geometric terms,
`Spec B` is a group scheme over `R`, and the map to `Spec A` is a group
homomorphism. The construction and the proof are internal to this project. The
ring `B` is the ring of functions satisfying condition (ET) of Bruhat–Tits II,
§1.7.3 f) (`bruhat-tits-1984-reductive-local-groups-ii`).

## Extension lemmas

- `algHom_ext_incl`: two `R`-algebra maps from `B` to a flat `R`-algebra that
  agree after composing with `incl` are equal (`algHom_ext` of the Saturation
  module).
- `extend_incl` and `extend_comp_incl`: the extension `extend f hf` restricts to
  `f` along `incl`.
- `dvd_of_exists_smul_eq`: if `s • b = 1 ⊗ a` for some `b ∈ B`, then `s` divides
  `χ a` for every `R`-point `χ` of `A`. Indeed, `χ a = point χ (s • b) =
  s * point χ b`.
- Instance `instFlat`: `B` is flat over the discrete valuation ring `R`, because
  it is torsion-free and `R` is a Dedekind domain.

## Density on pairs of points

- `detectsMaximal_point`: the forms `point φ`, for `φ` ranging over the
  `R`-points of `A`, detect the maximal ideal on `B`. If all values of `b` are
  divisible by a uniformizer `ϖ`, then `b = ϖ • b'` (`exists_eq_smul_of_dvd`).
- `productForm_point_map_incl`: the product form `point φ ⊗ point ψ` composed
  with `incl ⊗ incl` is the map `A ⊗ A → R` induced by `φ` and `ψ`.

## Comultiplication and counit

Assume `[Bialgebra R A]`.

- `comulAux = (incl ⊗ incl) ∘ Δ_A : A → B ⊗ B`.
- `comulAux_divisible` checks the hypothesis of `extend`. Let `s • b = 1 ⊗ a`.
  For each pair of points `(φ, ψ)`, the value of `comulAux a` under
  `point φ ⊗ point ψ` equals `χ a` for the `R`-point `χ = (φ ⊗ ψ) ∘ Δ_A` of `A`.
  So `s` divides it by `dvd_of_exists_smul_eq`. By `DetectsMaximal.tensor` and
  `DetectsMaximal.exists_eq_smul`, `comulAux a` is divisible by `s` in `B ⊗ B`.
- `comulInt = extend comulAux _ : B → B ⊗ B`. `comulInt_incl` and
  `comulInt_comp_incl` show that it restricts to `comulAux`, and
  `comulInt_comp_incl'` gives the linear-map form.
- `counitInt = point ε_A : B → R`, the value at the identity point.
  `counitInt_comp_incl` and `counitInt_comp_incl'` show that it restricts to
  `ε_A`.
- Instance `instBialgebra : Bialgebra R B`, built with `Bialgebra.ofAlgHom`.
  Each axiom is an equality of algebra maps from `B` into the flat algebras
  `B ⊗ (B ⊗ B)`, `R ⊗ B` and `B ⊗ R`. By `algHom_ext_incl`, it suffices to check
  it after composing with `incl`. There it reduces to the corresponding axiom of
  `A` through the `coassoc_simps` simp set, as in Mathlib's
  `Mathlib/RingTheory/Bialgebra/Quotient.lean`.
- `comulAlgHom_int` and `counitAlgHom_int` (both `rfl`) identify the structure
  maps.
- `inclBialgHom : A →ₐc[R] B` is `incl` as a bialgebra map
  (`BialgHom.ofAlgHom`), and `inclBialgHom_apply` states that it agrees with
  `incl`.

## Antipode

Assume `[HopfAlgebra R A]`.

- `antipodeAux = incl ∘ S_A`. It satisfies the hypothesis of `extend`
  (`antipodeAux_divisible`), since `χ ∘ S_A` is an `R`-point of `A` for every
  `R`-point `χ`, followed by `exists_eq_smul_of_dvd`.
- `antipodeInt = extend antipodeAux _ : B → B`, with
  `antipodeInt_incl : antipodeInt (incl a) = incl (S_A a)`.
- `lift_antipodeAlgHom_comp_comul` and `lift_id_antipodeAlgHom_comp_comul`
  state the antipode axioms of `A` as equalities of algebra maps. They come from
  `HopfAlgebra.mul_antipode_rTensor_comul` and
  `HopfAlgebra.mul_antipode_lTensor_comul`.
- Instance `instHopfAlgebra : HopfAlgebra R B`, built with
  `HopfAlgebra.ofAlgHom`. Both axioms are checked after composing with `incl`
  (`algHom_ext_incl`). There they become the antipode axioms of `A`, mapped by
  `incl`.
