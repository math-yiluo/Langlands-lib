# The fixed-point formula over the tame fields: proof

`Langlands.Henniart.weilTameFieldFixedPoint` proves
`WeilTameFieldFixedPointStatement.{uK, uW}` (module
`Langlands.Correspondence.HenniartTameOrbitFormula`): for `p ∤ m`, `φ` of
geometric degree one, a Frobenius coset datum `D : TameWeilFrobeniusData K m φ`
and `g` in inertia, the field `E` indexed by the coset of `g` satisfies
`C_E(p^r, j) = (q_K - 1) · #{c ∈ tameOrbitClasses K D.kernel r m j : (g φ) • c = c}`
in `ℕ∞`.

The proof applies `weilTameFieldFixedPoint_of_parametrization` (module
`Langlands.Correspondence.HenniartTameFieldCount`) to the theorem
`tameWeilFrobeniusParametrization` of the Frobenius parametrization of tame
fields (module `Langlands.Correspondence.HenniartTameWeilFieldsProof`), which
is used over `E` to supply open subgroups of inertia of every index prime to
`p`.

In outline: over `E` the orbit formula with `m = 1` and `J = I_E` gives
`C_E(p^r, j) = (q_E - 1)` times the number of stable orbits, which are single
`φ_E`-fixed tame classes, where `φ_E` is the element of the Weil group of `E`
mapping to `g φ` (it has degree one since `E/K` has residue degree one). The
Weil map of `E` identifies wild inertia of `E` with wild inertia of `K`, maps
inertia of `E` onto `D.kernel`, and rescales positive upper indices by `m`
(the relative Herbrand function is `v ↦ m v`). Hence the tame classes of `E`
fixed by `φ_E` correspond to the tame classes of `K` for `D.kernel` fixed by
`g φ`, and `q_E = q_K`. Source: H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), registered as
`koch-1984-numerical-langlands-remarks`, §8, Lemmas 5–8 and formulas
(25)–(28) (PDF pp. 5–6); J.-P. Serre, *Local Fields* (1979), registered as
`serre-1979-local-fields`, IV §3 (printed pp. 73–75, PDF pp. 80–82).
