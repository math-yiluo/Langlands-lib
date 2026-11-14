# Local twisted pair classes of relative Weil representations

Supporting module of Task 5003 (module
`Langlands.Automorphic.AssociatedGammaArithmeticTwist`, namespace
`Langlands.ClassField.Global.RelativeWeilGroup`). It provides the local facts about the
arithmetic side of Henniart 2000, Théorème 2.3: the global twist `(χ ∘ τ_F) ⊗ S` of a
relative Weil representation, restricted along a local map `ι : W_{F_z} → W_{E/F}`. These are
internal deductions from the Library; the only external mathematical inputs are the proved
local transfer reciprocity and geometricity theorems, and, for the last result, the
statement `ArithmeticPairEpsilonExistenceStatement`, taken as a hypothesis here. It is proved
in the Library as `Correspondence.arithmeticPairEpsilonExistence`, which `AssociatedGammaFinal`
supplies.

## Results

- `localPairClass_twist_congr`, `localPairClass_twist_dual_congr`: if two characters of
  `W_{E/F}` agree on the image of `ι`, the local pair classes of the two twists of `S` (and of
  their duals) coincide. The identity map is an equivalence of the local components; the
  classes agree by `Quotient.sound` through the zero-monodromy functor (the pattern of the
  published `localPairClass_dual`).
- `reciprocityCharacter_comp_eq_of_finiteComponent_eq`: along a local relative Weil map, the
  reciprocity character `χ ∘ τ_F` depends only on `χ_z`. Proof: the proved
  `localTransferReciprocity` gives `τ_F(ι g) = (rec_z g)⁻¹` in `C_F`, for the base candidate
  of a normalized family, which is geometric by the proved `commonClosureGeometricProof`.
- `localTwistCharacter eC χ`: the local Weil character `g ↦ χ_z(rec g)` along the base
  candidate of `eC`; `reciprocityCharacter_apply_localMap`: `(χ ∘ τ_F)(ι g)` is its value.
- `localPairClass_twist_eq`: the local pair class of a twist is the class of the twisted local
  component.
- `exists_isArithmeticPairLocalFactors`: assuming `ArithmeticPairEpsilonExistenceStatement`,
  for continuous `S`, `S'` and every Hecke character `χ` the twisted local pair has arithmetic
  local factors in the sense of `IsArithmeticPairLocalFactors`: the L-factors are the
  evaluated arithmetic pair L-factors, and the epsilon factor is the monomial supplied by the
  hypothesis. Continuity of the twisted local component comes from the published
  `isContinuous_twist` and `localComponent_isContinuous`.
