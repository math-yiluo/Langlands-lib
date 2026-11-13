# Discrepancies of axis trivializations

Worker 198 wrote this internal helper module for Task 5678. It supplies the
general structure-sheaf calculations used by
`TwoAxisCarrierIsoAbelian`. All results are in namespace
`Langlands.AlgebraicGeometry.Picard` and hold in every universe.

## Axis restriction of a discrepancy

Fix scheme maps `s : S ⟶ X` and `k : X ⟶ Z`, module sheaves `N`, `N'` on `Z`,
trivializations `α : O_X ≅ k* N` and `α' : O_X ≅ k* N'`, and an isomorphism
`g : N ≅ N'`. The discrepancy `α ≪≫ k*g ≪≫ α'⁻¹` is an automorphism of `O_X`.

`structureAutPullback_axis` computes its pullback along `s`, in the sense of the
published `structureAutPullback` (pullback of the automorphism, conjugated by the
canonical comparison `pullbackUnitIso s`). The result is
`axisRestrictionIso s k N α ≪≫ (s ≫ k)*g ≪≫ (axisRestrictionIso s k N' α')⁻¹`.
Here `axisRestrictionIso` is the published restriction of an axis trivialization
to the base. The proof unfolds both sides and uses naturality of the published
composition comparison `Scheme.Modules.pullbackComp s k`.

`structureAutPullback_refl` and its variant `structureAutPullback_refl_structureSheaf`
state that pulling back the identity automorphism gives the identity. The proof
compares global units with the published `structureAutScalar_pullback`.

## Automorphisms trivial along a section

`structureAut_eq_refl_of_section` takes `q : Y ⟶ S`, a section `t` with
`t ≫ q = 𝟙 S`, and the hypothesis that `q.app ⊤` is an isomorphism, so global
functions on `Y` are base global functions. It shows that an automorphism `δ` of
`O_Y` is the identity if `structureAutPullback t δ` is. Proof: the published
`structureAutScalar` identifies automorphisms of `O_Y` with global units, and
`structureAutScalar_pullback` turns pullback along `t` into the ring map
`t.appTop`. Since `t.appTop ∘ q.appTop` is the identity and `q.appTop` is
surjective, `t.appTop` is injective. Hence the global unit of `δ` is `1`.

## Second-axis discrepancy

Let `e : S ⟶ X`, `t : S ⟶ Y`, `i : X ⟶ Z`, `j : Y ⟶ Z` satisfy `e ≫ i = t ≫ j`.
Let `ρ` and `ρ'` be published compatible `TwoAxisRigidification`s of `N` and `N'`.
Let `g : N ≅ N'` respect the first trivializations:
`ρ.first.hom ≫ i*g.hom = ρ'.first.hom`.
`secondDiscrepancy_restrict_refl` proves that the second-axis discrepancy
`ρ.second ≪≫ j*g ≪≫ ρ'.second⁻¹` pulls back along `t` to the identity. The proof
rewrites both restrictions with `structureAutPullback_axis`. It substitutes the
compatibility equations of `ρ` and `ρ'`. Naturality of
`Scheme.Modules.pullbackCongr` along `e ≫ i = t ≫ j` then reduces the claim to
the restriction of the first-axis discrepancy, which is the identity.

The provenance is internal: categorical calculations with the Library's module
pullback comparisons and its structure-sheaf scalar interface. No literature
statement is translated.
