# Locality of the analytic relation of affine test points

This module works in the setting of `SpaceChartRelation`: affine test points
`u : Spec A → F`, `v : Spec B → F` of a presheaf, a model `M` of `Spec A ×_F Spec B`, and the
relation `M.ARel P Q α β` of analytic maps `α : T ⟶ Spec(A)ᵃⁿ`, `β : T ⟶ Spec(B)ᵃⁿ`
(joint factorization through `Spec(M.C)ᵃⁿ`).

- `ExistenceReduction.TestModel.ARel.of_etale_cover`: assume
  `EtaleHomSheafStatement.{u, u}` (the Hom presheaves are sheaves on small étale sites). Let
  `e l : U l ⟶ T` be a family of étale morphisms, jointly surjective on underlying points. If
  `e l ≫ α` and `e l ≫ β` are related through `M` for every `l`, then `α` and `β` are related
  through `M`.
- `ExistenceReduction.TestModel.isPullback_of_aRel`: let `πP : Spec(A)ᵃⁿ ⟶ Y` and
  `πQ : Spec(B)ᵃⁿ ⟶ Y` satisfy `(M.f)ᵃⁿ ≫ πP = (M.g)ᵃⁿ ≫ πQ`, and assume every pair
  `α, β` with `α ≫ πP = β ≫ πQ` is related through `M`. Then
  `IsPullback (M.f)ᵃⁿ (M.g)ᵃⁿ πP πQ`.

## Proof

- `ARel.of_etale_cover`: choose `t l : U l ⟶ Spec(M.C)ᵃⁿ` relating `e l ≫ α` and
  `e l ≫ β`. For `a : V ⟶ U l` and `b : V ⟶ U l'` with `a ≫ e l = b ≫ e l'`, the maps
  `a ≫ t l` and `b ≫ t l'` have equal composites with both projections, so they are equal
  (`jointly_mono`). Hence the `t l` glue to `t : T ⟶ Spec(M.C)ᵃⁿ`
  (`exists_glue_of_etale_cover`, with the sheaf property for the target `Spec(M.C)ᵃⁿ`), and
  `t ≫ (M.f)ᵃⁿ = α`, `t ≫ (M.g)ᵃⁿ = β` hold because they hold after every `e l`
  (`hom_ext_of_etale_cover`, with the targets `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ`).
- `isPullback_of_aRel`: `PullbackCone.IsLimit.mk`; the lift of a cone is a chosen joint
  factorization of its two legs through `Spec(M.C)ᵃⁿ`, and it is unique by `jointly_mono`.

## Provenance

Derived. The descent of morphisms along étale coverings is the sheaf property of
representable functors on the étale site of analytic spaces, used for the same purpose in
Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009), proof of
Lemma 4.2.3, p.21 (`conrad-temkin-2009-nonarchimedean-analytification`), via their
Theorem 4.1.2 and Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
4.1.5 (`berkovich-1993-etale-cohomology`). In the Library this property is the proposition
`EtaleHomSheafStatement`, assumed here as a hypothesis.
