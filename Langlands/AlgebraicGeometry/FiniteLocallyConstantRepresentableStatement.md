# Statement: finite locally constant étale sheaves are representable by finite étale schemes

`Langlands.AlgebraicGeometry.FiniteLocallyConstantRepresentableStatement.{u}` states that a
sheaf of sets on the big étale site of a scheme `S` that is étale-locally constant with
finite values is represented by a finite étale `S`-scheme. The module states the
proposition and supplies no proof.

## The formula

```lean
def FiniteLocallyConstantRepresentableStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type u),
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) F →
    (∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S, ∀ i : 𝒰.I₀,
      ∃ A : Type u, Finite A ∧
        Nonempty ((Over.map (𝒰.f i)).op ⋙ F ≅
          letI : TopologicalSpace A := ⊥
          (Over.forget (𝒰.X i)).op ⋙ continuousMapPresheaf.{u, u} A)) →
    ∃ (X : Scheme.{u}) (q : X ⟶ S), IsFinite q ∧ Etale q ∧ Nonempty (F.RepresentableBy (Over.mk q))
```

- `S` is an arbitrary scheme in universe `u`. No noetherian or quasi-compactness
  hypothesis is imposed.
- `F` is a presheaf of sets on `Over S`, the category of all `S`-schemes. It is a sheaf
  for the big étale topology `Scheme.etaleTopology.over S`, which is also the topology
  `EtaleLocalSystem.topology S` of the published local-system definitions.
- **Locally constant with finite values.** There is an étale cover `𝒰` of `S` (Mathlib's
  `Scheme.Cover` for the étale precoverage) with the following property. For every member
  `𝒰.f i : 𝒰.X i ⟶ S`, the restriction `(Over.map (𝒰.f i)).op ⋙ F` (the values of `F` on
  schemes over `𝒰.X i`) is isomorphic to the constant presheaf of a finite set `A`. The
  constant presheaf sends `V` over `𝒰.X i` to the continuous maps from `V` to `A` with the
  discrete topology (Mathlib's `continuousMapPresheaf`), that is, to the locally constant
  `A`-valued functions on `V`. The set `A` may depend on `i`.
- **Conclusion.** There are an `S`-scheme `q : X ⟶ S`, finite (`IsFinite q`) and étale
  (`Etale q`), and a representation `F.RepresentableBy (Over.mk q)`. The latter is a
  bijection, natural in `T : Over S`, between morphisms `T ⟶ Over.mk q` over `S` and
  elements of `F(T)`.

## Source and provenance

J. S. Milne, *Étale Cohomology* (1980), `milne-1980-etale-cohomology`, Chapter V,
Proposition 1.1, printed p.155 (one-based PDF p.169, proof on p.170): "Let `F` be a
locally constant sheaf on `X_et`. If `F` has finite stalks, then it is finite and is
represented by a group scheme `F` that is finite and étale over `X`." The proof is by
effective descent of the finite étale scheme representing `F` on a trivializing cover.
Conrad uses the same fact in the proof of Corollary B.3.6 (`conrad-2014-reductive-group-schemes`,
p.294): "`F/nF` is represented by a finite étale `S`-group `G_n → S`".

The Lean statement is derived from Milne's proposition with three changes, each
harmless for the descent proof:
- it is stated for sheaves of sets, not of groups;
- it uses the big étale site, as in `EtaleLocalSystem`;
- "finite stalks" is replaced by local constancy with finite value sets on a cover.

It is a prerequisite of the planned proof of
`Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement`. That proof
represents the sheaf of level-`n` structures of a local system by a finite étale scheme.
