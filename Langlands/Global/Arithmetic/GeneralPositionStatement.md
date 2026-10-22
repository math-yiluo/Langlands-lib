# Characters in general position (Harris 1998, Definition 4.5 and Lemma 4.7)

Author: Worker 35. Proposition definitions for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
The three statements and their conjunction assert no theorem truth.
No local or global Langlands correspondence is assumed.

## Mathematical content

### Mackey constituents

For an arbitrary group `G`, subgroups `H` and `K` with `H` of finite
index, a finite-dimensional complex representation `σ` of `H` and an
element `g ∈ G`:

- `conjugate H g` is the subgroup `g H g⁻¹`, defined as the preimage of
  `H` under `x ↦ g⁻¹ x g`;
- `conjugateRestriction H K g` is the canonical homomorphism
  `g H g⁻¹ ∩ K → H`, `x ↦ g⁻¹ x g`;
- `mackeyConstituent H K σ g` is the representation of `K`

\[
  \operatorname{Ind}_{gHg^{-1}\cap K}^{K}\, g(\sigma),
  \qquad g(\sigma)(x)=\sigma(g^{-1}xg).
\]

The induction is the Library's finite-index induction
`FiniteRepresentation.induce` (equivariant functions with right
translation). The restriction is `FiniteRepresentation.restrict` along
`conjugateRestriction`. The finite index of `gHg⁻¹ ∩ K` in `K` is found
by instance inference from that of `H`.

### Fields and Weil groups

Fix a prime `p` and a p-adic field `F` (`PadicField p`). All extensions
are finite intermediate fields `Extension F` of the one algebraic
closure `AlgebraicClosure F.Carrier`. `W_F = localWeilGroup F` is the
Library's local Weil group. For an intermediate field `E`, `W_E` is
`weilSubgroup F E`, the subgroup of `W_F` whose Galois projection fixes
`E` pointwise.

- `galoisClosure F F'` is `F̃`, Mathlib's normal closure of `F'` over `F`
  inside the algebraic closure.
- `IsCyclicPrimeStep F E L` says that `E ≤ L` and that `L/E` is Galois,
  with cyclic Galois group and prime degree. The relative field is
  Mathlib's `IntermediateField.extendScalars`.
- `IsInGeneralPosition F F' χ`, for a continuous character
  `χ : W_{F'} → ℂˣ`, says that there are `t ≥ 0` and fields
  `F_0, …, F_t` with `F_0 = F̃` and `F_t = F` (the bottom intermediate
  field). Each step `F_i ⊇ F_{i+1}` must satisfy `IsCyclicPrimeStep`, and
  for every `i ≤ t` and every `g ∈ W_F` the Mackey constituent
  `mackeyConstituent W_{F'} W_{F_i} χ g` must be irreducible. The
  character is used as the one-dimensional representation
  `characterLine`. Irreducibility is Mathlib's
  `Representation.IsIrreducible`: the representation is nonzero and has
  no subrepresentations other than zero and itself.
- `closureRestriction F F' χ` is the restriction `χ̃` of `χ` to
  `W_{F̃} ⊆ W_{F'}`.
- `HasExactWeilStabilizer F F' χ` says that for every `g ∈ W_F`,

\[
  g(\tilde\chi)=\tilde\chi \iff g\in W_{F'},
  \qquad g(\tilde\chi)(x)=\tilde\chi(g^{-1}xg),\ x\in W_{\tilde F}.
\]

  The conjugation action is Mathlib's `MulAut.conjNormal`, which acts on
  the normal subgroup `W_{F̃}`.

Three small results are proved, not assumed: `le_galoisClosure`
(`F' ⊆ F̃`), `galoisClosure_weilSubgroup_le` (`W_{F̃} ⊆ W_{F'}`) and the
instance `galoisClosure_normal`. The last one says that `W_{F̃}` is
normal in `W_F`, because `F̃/F` is Galois. It is proved with Mathlib's
`InfiniteGalois.normal_iff_isGalois`.

### The statements

- `GeneralPositionOfExactStabilizerStatement`: for every p-adic field `F`,
  every finite extension `F'` in the common closure and every continuous
  character `χ` of `W_{F'}`, the condition `HasExactWeilStabilizer` implies
  `IsInGeneralPosition`. The conclusion includes the existence of the
  tower.
- `ExactStabilizerCharacterStatement`: for every normalized reciprocity
  family `e` and every `r : ℕ`, there is a continuous character `χ` of
  `F'ˣ` with three properties: finite order (`χ^n = 1` for some `n > 0`),
  conductor exponent at least `r`, and the condition
  `HasExactWeilStabilizer` for its Weil-group pullback
  `weilCharacter F e F' χ`.
- `GeneralPositionCharacterStatement` (Lemma 4.7): the same, with
  `IsInGeneralPosition` in place of `HasExactWeilStabilizer`.
- `HarrisGeneralPositionStatement` is the conjunction of the three.

The first two together imply the third. That implication is not
formalized here.

## Instances, universes and scope

- The carrier universe of `F` is `uF`, and all three statements share it.
  The character line has carrier `ULift.{0} ℂ`. The Mackey constituents
  then live in universe `uF`, through `FiniteRepresentation.induce`.
- The topology on `F'ˣ` and on `W_{F'}` is the Library's canonical one
  (`fieldData F F'`, `weilSubgroup` with the subspace topology).
- `NormalizedReciprocity F e` is the Library's normalized coherent
  relation: norm, transfer, conjugation, density and completion squares,
  with the uniformizer sent to geometric Frobenius. It remains an explicit
  hypothesis. If no family satisfies it, the last two statements are
  vacuous. Existence is the separate Library proposition
  `NormalizedSystemExistence`.
- The conductor is `(fieldData F F').multiplicativeConductor χ`, the
  Library's version of Tate's exponent `a(χ)`. It is the least `n` such
  that `χ` is trivial on the unit filtration level `U^n`, with `U^0` the
  valuation units, and it is zero exactly when `χ` is unramified.
  "Arbitrarily large conductor" is read as `r ≤ a(χ)` for every `r`.
- The case `F' = F` is included. Then `F̃ = F`, `t = 0`, and the only
  constituent is the character itself.
- Every prime `p` is included, `p = 2` among them. There is no condition
  `n < p` and no bound on the degree.
- Every finite extension of `F` is `F`-isomorphic to an intermediate field
  of the algebraic closure. Quantifying over `Extension F` therefore
  covers every finite extension `F'/F`.

## Original source correspondence

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p* (1998). Page numbers are printed pages; PDF page = printed
page − 176. The passages were read directly in both the PDF and the arXiv
TeX source (`math_9611226v1.tex`).

- **Notation, p.183.** For subgroups `H`, `K` of finite index in `G` and a
  set `A` of representatives of the double cosets, the Mackey
  constituents of `Ind_H^G σ` restricted to `K` are
  `Ind_{aHa⁻¹∩K}^K a(σ)`. Here `a(σ)` is `σ` transported along the
  canonical isomorphism `aHa⁻¹ → H`, which is `x ↦ a⁻¹xa`. This matches
  `conjugateRestriction` and `mackeyConstituent`.
- **Index set.** Harris writes the double cosets as `H\G/K`, but Mackey's
  decomposition with these constituents is indexed by `K\G/H`. The Lean
  definition quantifies over all `g ∈ W_F`, so it covers every set of
  representatives under either convention. It is equivalent to Harris's
  condition, because the constituent for `kgh`, with `k ∈ K` and
  `h ∈ H`, is isomorphic to the constituent for `g`. This invariance is a
  standard fact and is not formalized here.
- **`F̃`, p.200.** `F̃` is the Galois closure of `F'` over `F`. The Lean
  definition is `galoisClosure`.
- **Definition 4.5, p.201.** `χ(*)` is a complex character of `W_{F'}`,
  "or equivalently a character of `F'ˣ`". It is in general position
  relative to `F` if there is a sequence
  `F̃ = F_0 ⊃ F_1 ⊃ ⋯ ⊃ F_t = F` such that (i) each `F_i/F_{i+1}` is cyclic
  of prime degree, and (ii) the Mackey constituents of `Ind_{F'/F} χ(*)`
  restricted to `W_{F_i}` are all irreducible, for `i = 0, …, t`. The
  Lean definition `IsInGeneralPosition` follows this, with the tower
  indexed by `Fin (t + 1)`. "Cyclic extension" is read as a Galois
  extension with cyclic Galois group. Cyclicity is redundant once the
  degree is prime, but Harris's wording is kept.
- **Lemma 4.7, p.201.** For an extension `F'/F` of local fields, there are
  characters of `F'ˣ` of arbitrarily large conductor in general position
  relative to `F`. This is `GeneralPositionCharacterStatement`. The
  passage from `F'ˣ` to `W_{F'}` is the pullback `weilCharacter` through
  the supplied reciprocity family.
- **Proof of Lemma 4.7, pp.204–206.** The first sentence (p.204) says
  that the characters constructed have finite order. The finite-order
  conjunct in both character statements comes from there. Harris writes
  `G = Γ_F`, `H = Γ_{F'}`, `G̃ = Γ_{F̃}`, and `χ̃ = χ(*) ∘ N_{F̃/F'}`. He
  states the sufficient condition for irreducibility

  \[
    H=\{g\in G \mid g(\tilde\chi)=\tilde\chi\}, \tag{4.12}
  \]

  which is `HasExactWeilStabilizer`. On p.205 he lets `K` be any subgroup
  of `G` containing `G̃`. He says it follows easily from Clifford–Mackey
  theory that (4.12) is sufficient for general position. That claim is
  `GeneralPositionOfExactStabilizerStatement`. The reduction
  "it suffices to construct characters `χ(*)` with arbitrarily large
  conductor satisfying (4.12)" (p.205), together with the construction on
  pp.205–206 through (4.13), is `ExactStabilizerCharacterStatement`.
- **Use, Proposition 4.8, pp.201–203.** Harris's weak automorphic
  induction takes `χ(*)` in general position relative to `F`. The proof
  descends through the tower `F_i` and uses that the Mackey constituents
  of each `I(a, i, χ(*))` on `W_{F_j}`, `j < i`, are among those of
  `Ind_{F'/F} χ(*)`.

### Derived choices

The following choices are derived. None of them changes the mathematical
content.

1. **Weil groups instead of Galois groups in (4.12).** Harris's proof works
   in `Γ_F`. Definition 4.5 uses `W_{F_i}`, and the Lean target uses
   `W_F` throughout. Every `g ∈ W_{F̃}` fixes `χ̃`, because the values are
   in an abelian group. The action on `χ̃` therefore factors through
   `W_F/W_{F̃}`, which is `Gal(F̃/F)`, as is `Γ_F/Γ_{F̃}`. The two stabilizer
   conditions both say that the stabilizer in `Gal(F̃/F)` is
   `Gal(F̃/F')`.
2. **`χ̃` as a restriction.** Harris's `χ(*) ∘ N_{F̃/F'}` is read on the
   Weil side as the restriction of `χ` to `W_{F̃}`. Suppose `χ` is
   `weilCharacter F e F' χ₀` for a family `e` satisfying
   `NormalizedReciprocity`. Then the norm square of `e` (`NormRelation`)
   identifies this restriction with `weilCharacter F e F̃ (χ₀ ∘ N_{F̃/F'})`,
   which is Harris's `χ̃`. In
   `GeneralPositionOfExactStabilizerStatement`, `χ` is an arbitrary
   continuous character of `W_{F'}` and no reciprocity map is involved.
   The restriction is then the intrinsic form of the condition.
3. **The tower.** Harris's sufficiency claim on p.205 concerns condition
   (ii) for every `K ⊇ G̃`. He does not discuss the tower of condition (i).
   That tower exists because `Gal(F̃/F)` is solvable: Serre, *Local
   Fields*, Ch. IV §2, Proposition 7, Corollary 5, printed p.68, for
   finite residue fields. The fixed fields of a composition series give
   steps that are cyclic of prime degree. The Lean statement includes
   the tower in the conclusion of
   `GeneralPositionOfExactStabilizerStatement`.
4. **Constituents for all elements**, as explained under "Index set"
   above.
5. **Conductor**: Tate's exponent `a(χ)`, as above. Harris does not fix
   a normalization, and every normalization in use is unbounded together
   with `a(χ)`.

### Expected argument for the first statement (not formalized)

Let `K ⊇ W_{F̃}` and `g ∈ W_F`. Since `W_{F̃}` is normal and contained in
`W_{F'}`, it lies in `gW_{F'}g⁻¹ ∩ K`. Restrict the constituent to
`W_{F̃}`. It becomes the sum, over the cosets of `gW_{F'}g⁻¹ ∩ K` in `K`,
of the characters `kg(χ̃)`. By (4.12) these characters are pairwise
distinct. A `K`-stable subspace is therefore a sum of these
`W_{F̃}`-eigenlines. `K` permutes the eigenlines transitively, so the
subspace is zero or everything. The argument needs no semisimplicity of
`W_F`-representations. It is recorded only as guidance for a proof.

### Source qualifications

- **p-adic fields.** Lemma 4.7 is stated for all local fields. The Lean
  target is restricted to p-adic fields (characteristic zero), the
  Library's setting.
- **Residue characteristic two.** On p.205 Harris composes a character
  modulo `p^N` with an embedding `(ℤ/p^Nℤ)ˣ ↪ ℂˣ`. For `p = 2` and `N ≥ 3`
  that group is not cyclic, so the literal embedding does not exist. This
  does not justify excluding `p = 2`. A proof must use a cyclic image of
  the principal units, or another correct construction, and check that
  the conductor and the exact stabilizer survive. No such repair is
  claimed. The same qualification is documented for the published
  `AuxiliaryCharacterStatement`.
- **Title.** The title of the article restricts to `n < p`, but Definition
  4.5 and Lemma 4.7 do not.

### Relation to the published auxiliary-character target

`Langlands.Global.AuxiliaryCharacterStatement`
(`Langlands/Global/Arithmetic/AuxiliaryCharacterStatement.lean`) works on
the field side. It covers any finite Galois `M/F`, an intermediate field
`L` and the norm pullback `χ ∘ N_{M/L}`. Its exact stabilizer is required
already on the valuation units of `M`, following Henniart 2000 §3.4,
condition 3. Its depth is nontriviality near one in the canonical norm.

Take `M = F̃` and `L = F'`. Unit-level exactness implies exactness for the
whole character, because `F̃`-automorphisms fixing `F'` fix `χ ∘ N`
anyway. Transporting that field-side condition to
`HasExactWeilStabilizer` uses further inputs: the norm and conjugation
squares of a normalized reciprocity family, the identification of
abstract p-adic fields with intermediate fields of the common closure,
and a comparison of the two depth notions. No implication between the
two targets is formalized.

### Retained originals

- Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p*, Invent. Math. 134 (1998). The passages used are the
  Notation section (p.183), the definition of `F̃` (p.200), Definition
  4.5, Lemma 4.7 and Proposition 4.8 (pp.201–203), and the proof of
  Lemma 4.7 with (4.12) and (4.13) (pp.204–206). Source
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- Jean-Pierre Serre, *Local Fields* (1979), Ch. IV §2, Proposition 7,
  Corollary 5, printed p.68 (PDF p.75), for solvability. Source
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## Dependencies and validation boundary

The project imports are both from Library commit
`08ce07bfdc79298778cd3e9ee6d5318c23c3b75b`:

- `Langlands.HarmonicAnalysis.Conductor`, Lean SHA256
  `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53`,
  supplies `multiplicativeConductor`.
- `Langlands.LocalFactor.CommonClosure`, Lean SHA256
  `b9031e072d4a5eea194baa9c0030d6d97223929cee5c5a9eb8e438c2bf697726`,
  supplies `Extension`, `weilSubgroup`, `FieldCharacter`,
  `ReciprocityFamily`, `NormalizedReciprocity`, `weilCharacter` and
  `fieldData`. Through its imports it also supplies `localWeilGroup`,
  `FiniteRepresentation.induce`, `restrict`, `characterLine` and
  `IsIrreducible`.

The remaining imports are Mathlib: normal closure, infinite Galois
theory and conjugation actions.

The project Lean service compiled the module under Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` with no errors
or warnings. The closing declaration `HarrisGeneralPositionStatement` has
type `Prop`, with the single universe parameter `uF`. Axiom inspection
reports only `propext`, `Classical.choice` and `Quot.sound`.

These results do not prove any of the three statements and do not
constitute independent semantic acceptance. The source qualifications
above remain obligations for any eventual proof.
