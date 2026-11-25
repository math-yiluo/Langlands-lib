# Proof: the dual of a cuspidal Whittaker function is a Whittaker function of the contragredient

Module `Langlands.Global.RankinSelberg.ContragredientDualWhittakerProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.contragredientDualWhittaker :
    ContragredientDualWhittakerStatement.{u}
```

proves `Langlands.Global.RankinSelbergGlobal.ContragredientDualWhittakerStatement` (module
`EqualDualEulerFactorizationReduction`) at an arbitrary universe `u`. Unfolded, the statement is

```lean
∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
  ∀ (S : Finset (FinitePlace F)) (x : T.Space), IsSphericalOutside F T S x →
    ∃ xd : Td.Space, IsSphericalOutside F Td S xd ∧
      cuspWhittaker F Td ψ.complex⁻¹ xd =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
```

In words: let `ψ` be a unitary character of the adeles trivial on `F`, `T` an actual cuspidal
realization of `GL_(r+1)` and `Td` an actual cuspidal realization of its contragredient. For
every vector `x` of `T` fixed by `GL_(r+1)(𝒪_v)` at every finite place `v ∉ S` there is a vector
`xd` of `Td` with the same property whose `ψ⁻¹`-Whittaker function is
`W̃_x(g) = W_x(w_n ᵗg⁻¹)`, where `W_x` is the `ψ`-Whittaker function of `x`.

## Proof as implemented

The proof is a single term that combines three Library theorems.

1. `contragredientDualWhittakerReduction` (module `ContragredientDualWhittakerReduction`)
   proves `ContragredientDualWhittakerReductionStatement.{u}`, the implication
   `Automorphic.CuspidalOperatorMultiplicityOneStatement.{u} →
   CuspidalTransposeInverseContragredientStatement.{u} → ContragredientDualWhittakerStatement.{u}`.
   The contragredient `T'` of `T` that contains the dual cusp forms is equivalent to `Td`
   (uniqueness of contragredients), hence equal to `Td` by multiplicity one; the vector `xd` of
   `Td` whose cusp form is the dual `φ̃_x` of the cusp form of `x` is spherical outside `S` and
   has `ψ⁻¹`-Whittaker function `W̃_x`.
2. `Automorphic.cuspidalOperatorMultiplicityOne` (module
   `Langlands.Automorphic.CuspidalOperatorMultiplicityOneProof`) proves
   `CuspidalOperatorMultiplicityOneStatement.{u}`: two equivalent actual irreducible cuspidal
   realizations of `GL_(r+1)` have the same underlying space of automorphic functions.
3. `cuspidalTransposeInverseContragredient` (module `CuspidalTransposeInverseContragredientProof`)
   proves `CuspidalTransposeInverseContragredientStatement.{u}`: every actual irreducible cuspidal
   realization `T` has a cuspidal realization of its contragredient containing the dual
   `φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp form of every vector of `T`.

## Declarations

- `contragredientDualWhittaker : ContragredientDualWhittakerStatement.{u}` (theorem).

## Provenance

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as `cogdell-2004-analytic-theory-gln`
(PDF page = printed page + 3):

- §1.2, printed p. 201 (PDF page 204), after Theorem 1.2: Gelfand and Kazhdan show that
  `π̃ ≅ π^ι` for `g^ι = ᵗg⁻¹`, "and in this case the Whittaker model for `π̃_v` can be obtained
  as `W(π̃_v, ψ_v⁻¹) = {W̃(g) = W(w_n ᵗg⁻¹) | W ∈ W(π_v, ψ_v)}`".
- §1.2, printed p. 202 (PDF page 205): a cusp form is determined by its Whittaker function, and
  the Multiplicity One theorem: the multiplicity of `π` in the space of cusp forms is at most one.
- §2.2, printed pp. 206–207 (PDF pages 209–210): the action `φ̃(g) = φ(g^ι) = φ(w_n g^ι)` on
  automorphic forms (p. 206), and, after Theorem 2.1, "for `W ∈ W(π, ψ)`, we set
  `W̃(g) = W(w_n g^ι) ∈ W(π̃, ψ⁻¹)`" (p. 207).

The theorem here is the global form of these remarks for the Library's actual cuspidal
realizations: the dual Whittaker function of a vector of `T` is the `ψ⁻¹`-Whittaker function of a
vector of the given contragredient realization `Td`, with the same sphericity outside `S`.
