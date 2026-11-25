# Products and determinants of scalar meromorphic functions

Module `Langlands.Global.EisensteinGenericInjectivity.MeromorphicDet` shows that finite
products and determinants of scalar meromorphic functions with a common holomorphy domain are
meromorphic with that domain. The notion is the Library's `IsMeromorphicOn 𝓘(ℂ, E) f U` of the
module `Langlands.Analysis.Meromorphic.ScalarIdentity`: `U` is open and dense, `f` is
holomorphic on `U`, and near every point `f` has a holomorphic denominator that is not
identically zero. The proof of `Langlands.Global.eisensteinGenericInjectivity` applies
`isMeromorphicOn_det` to the matrix of continued Eisenstein series.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, for a
complex normed space `E` and a set `U ⊆ E`. Complete types are printed by
`PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the page of
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `isMeromorphicOn_prod`: if `U` is open and dense and each `a i`, `i ∈ s`, is meromorphic with
  holomorphy domain `U`, so is the product `∏_{i ∈ s} a i`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.isMeromorphicOn_prod.{u_1, u_2} {E : Type u_1}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {«ι» : Type u_2} (s : Finset «ι»)
    {a : «ι» → E → ℂ} (hU : IsOpen U) (hdU : Dense U)
    (ha : ∀ i ∈ s, IsMeromorphicOn (modelWithCornersSelf ℂ E) (a i) U) :
    IsMeromorphicOn (modelWithCornersSelf ℂ E) (∏ i ∈ s, a i) U
  ```
- `isMeromorphicOn_det`: if every entry `f i k` of an `m × m` matrix of functions is meromorphic
  with holomorphy domain `U`, so is `s ↦ det (f i k s)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.isMeromorphicOn_det.{u_1} {E : Type u_1}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {m : ℕ} (f : Fin m → Fin m → E → ℂ)
    (hU : IsOpen U) (hdU : Dense U)
    (hf : ∀ (i k : Fin m), IsMeromorphicOn (modelWithCornersSelf ℂ E) (f i k) U) :
    IsMeromorphicOn (modelWithCornersSelf ℂ E) (fun s => (Matrix.of fun i k => f i k s).det) U
  ```

## Proofs

- `isMeromorphicOn_prod`: induction on the finite set; the empty product is the constant `1`
  restricted to `U` (`isMeromorphicOn_const`, `IsMeromorphicOn.restrict_domain`), and the step is
  the Library lemma `IsMeromorphicOn.mul`.
- `isMeromorphicOn_det`: expand the determinant over permutations (`Matrix.det_apply'`); each
  signed product is meromorphic by `isMeromorphicOn_prod` and `IsMeromorphicOn.mul_const` (module
  `Langlands.Analysis.Meromorphic.IdentityTheorem`), and the finite sum by
  `IsMeromorphicOn.sum`.

## Sources

The notion of meromorphy is that of J. Bernstein and E. Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §3.1, printed p. 192: a
holomorphic function on an open dense `U` is meromorphic if near every point it has a holomorphic
denominator `g ≢ 0` with `g f` holomorphic. The two closure properties are elementary.
