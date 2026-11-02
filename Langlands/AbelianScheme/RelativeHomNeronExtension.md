# Extension of homomorphisms of abelian schemes over discrete valuation rings

Authors: Worker 1042.

Module `Langlands.AbelianScheme.RelativeHomNeronExtension`. Written for task
`6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism
functor of a projective abelian scheme). It proves the hypothesis
`Langlands.AbelianScheme.NeronHomExtension.{u}` of
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityOfPieces`, and with it reduces the
target `Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement.{u}` to the single
interface `Langlands.AbelianScheme.AffineHomSchemePiecesStatement.{u}`. All declarations are in
namespace `Langlands.AbelianScheme`. The module adds no axioms.

The mathematical input is the Néron mapping property of abelian schemes over a discrete valuation
ring, taken from the Library's port of the Anthropic Fermat's Last Theorem formalisation (theorems
`NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle` and
`NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated`, with FLT's
`GoodReductionJacobian.AbelianSchemePropertyBundle` and
`GoodReductionJacobian.relativeGroupLawOfGrpObj`). This module only translates between those
statements, which are about morphisms of schemes over `Spec V` and their generic fibres
(`NeronModelInfra.genericFibreRestrict`), and the Library's group schemes and relative
homomorphisms.

## Declarations

- `isMonHom_of_map F f h₀ h₂`: let `F : C ⥤ D` be a monoidal functor between monoidal categories
  and `f : M ⟶ N` a morphism of monoid objects such that `F.map f` is a monoid morphism (for the
  monoid structures `Functor.monObjObj` on `F.obj M`, `F.obj N`). If `F.map` is injective on
  morphisms `𝟙_ C ⟶ N` (`h₀`) and on morphisms `M ⊗ M ⟶ N` (`h₂`), then `f` is a monoid
  morphism. Proof: the unit and multiplication of `F.obj M` are `ε F ≫ F.map η` and
  `μ F M M ≫ F.map μ`, and `ε F`, `μ F M M` are isomorphisms; so the images under `F` of both sides
  of each monoid-morphism equation agree, and `h₀`, `h₂` conclude (the argument of Mathlib's
  `Functor.FullyFaithful.isMonHom_preimage`).
- `genericFibre_map_injective K h`: let `V` be a domain with fraction field `K`, and `Y`, `Z`
  schemes over `Spec V` with `Y` flat and `Z` separated. Two morphisms `g g' : Y ⟶ Z` over
  `Spec V` whose base changes along `Spec K ⟶ Spec V` (`Over.pullback`) agree are equal. Proof:
  the base change of `g` is FLT's `genericFibreRestrict` of `g`, which is injective by
  `NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated`.
- `baseChange_map_surjective K G H hH`: let `V` be a discrete valuation ring with fraction field
  `K`, and `G`, `H` group objects over `Spec V` (`Grp (Over (Spec V))`) with `G` smooth over
  `Spec V` and `H` satisfying `GoodReductionJacobian.AbelianSchemePropertyBundle V H.X.hom`. Then
  every homomorphism of the base changes `G_K ⟶ H_K` (`GroupScheme.baseChange`, i.e. the image of
  `Over.pullback` on group objects) is the base change of a homomorphism `G ⟶ H`. Proof: by
  `NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle`, `H` has the Néron
  mapping property, so the underlying morphism of the given homomorphism is `genericFibreRestrict`
  of a unique morphism `φ : G ⟶ H` over `Spec V`; its base change is the given morphism. The
  sources `𝟙_` (that is, `Spec V`) and `G ⊗ G` (the fibre product over `Spec V`) are flat and `H`
  is separated (being proper), so `genericFibre_map_injective` and `isMonHom_of_map` show that `φ`
  is a monoid morphism.
- `abelianSchemePropertyBundle_baseChange B t`: for an abelian scheme `B` over `S` and
  `t : Spec V ⟶ S`, the base change `B_V` satisfies `AbelianSchemePropertyBundle V`: it is smooth
  and proper (base change), its fibres are connected (it is geometrically connected,
  `Scheme.Hom.isConnected_preimage_singleton`), and it carries the relative group law
  `GoodReductionJacobian.relativeGroupLawOfGrpObj` of its group object structure.
- `neronHomExtension : NeronHomExtension.{u}`: for abelian schemes `A`, `B` over `S`, a discrete
  valuation ring `V` with fraction field `K` and `t : Spec V ⟶ S`, the restriction
  `Langlands.GroupScheme.Cartier.restrict A.toCommGroupScheme B.toCommGroupScheme a` along
  `a : Spec K ⟶ Spec V` over `S` is surjective. Proof: by definition, `restrict a` sends `χ` to
  `(baseChangeCompIso A a).hom ≫ (GroupScheme.baseChange a.left).map χ ≫ (baseChangeCompIso B a).inv`.
  Given `χK`, conjugate it by these comparison isomorphisms to a homomorphism `A_V,K ⟶ B_V,K` of the
  base changes of `A_V` and `B_V` along `Spec K ⟶ Spec V`, and apply `baseChange_map_surjective` to
  `A_V` (smooth) and `B_V` (`abelianSchemePropertyBundle_baseChange`).
- `relativeEndomorphismRepresentability_of_affineHomSchemePiecesStatement hP`: for
  `hP : AffineHomSchemePiecesStatement.{u}`, the target
  `RelativeEndomorphismRepresentabilityStatement.{u}` holds. It is
  `relativeEndomorphismRepresentability_of_affineHomSchemePieces hP neronHomExtension`.

## Dependencies

- `Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityOfPieces` (same contribution).
- Ported FLT modules (same contribution):
  `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle`,
  `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated`.
- Library: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`.
