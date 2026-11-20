# Zariski locality of the conditions on ordinary polarized full-level data

This module proves that the propositional conditions in a `Datum` can be checked on a
covering family of opens of the base. The conditions are relative dimension, isogeny,
degree `d²`, polarization and full level. These results are inputs for gluing data along an
open cover (the existence half of the Zariski sheaf property of `moduliFunctor`). The module
introduces no statement and no hypothesis beyond the named `Prerequisites` inputs that the
polarization predicate already uses.

Throughout, `X : Scheme.{u}`, `U : I → X.Opens` with `I : Type u` and `hU : iSup U = ⊤`.
Restriction to `U i` is base change along the open immersion `(U i).ι`.

## Main results (namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`)

- `hasRelativeDimension_of_opens U hU A h`: if every base change
  `(baseChange (U i).ι).obj A` has relative dimension `g`, so does `A`. Relative dimension is
  `SmoothOfRelativeDimension g A.X.hom`. That property is local on the target, and the
  structure map of the base change is Mathlib's `pullbackHom` of `A.X.hom` on the open cover
  `X.openCoverOfIsOpenCover U hU`. So this is `IsZariskiLocalAtTarget.of_openCover`.
- `isIsogeny_of_opens U hU f h`: if every base change `(baseChange (U i).ι).map f` is an
  isogeny, so is `f`. Finiteness, flatness and surjectivity of `hom f` are each local on the
  target. `hom_prop_of_opens` applies to each of them.
- `hasDegreeSquare_of_opens U hU f hf h`: let `f` be an isogeny. If every base change
  `(baseChange (U i).ι).map f` has constant degree `d²`, so does `f`. Let `y` be a point of
  the target, and pick `i` with `y` over `U i`. Then `y` is the image of a point `y'` of
  `pullback B.X.hom (U i).ι` (`Scheme.Pullback.range_fst`). The square
  `hom_baseChange_isPullback` is Cartesian, so `Scheme.Hom.finrank_of_isPullback` identifies
  the rank of `hom f` at `y` with the rank of the base change at `y'`. The isogeny hypothesis
  supplies the finiteness and flatness instances that the rank comparison needs.
- `isFull_of_opens U hU v h`: if the pullback `pullbackTuple (U i).ι v` of an ordered tuple of
  torsion sections is full for every `i`, then `v` is full. Fullness asks for a basis at every
  geometric point `s : Spec K ⟶ X`. By `exists_lift_of_opens`, `s = s' ≫ (U i).ι` for some `i`
  and `s'`. The basis at `s'` for the pulled-back tuple is carried to a basis at `s` by the
  linear equivalence `levelBaseChangeLinear`. `fibreTuple_pullback` identifies its vectors
  with `fibreTuple v s`.
- `FullLevel.ofOpens U hU v h` is the full-level structure `⟨v, isFull_of_opens U hU v h⟩`.
  It is the selected definition of this module.
- `DualWitness.isPolarization_of_opens U hU P W lam h`: let `W : DualWitness A` and
  `lam : A ⟶ W.dual P`. Suppose that for every `i` the restriction
  `W.pullbackMap P (U i).ι (W.pullback P (U i).ι) lam` is a polarization for the pulled-back
  witness `W.pullback P (U i).ι`. Then `lam` is a polarization for `W`. The proof is below.

## Auxiliary results

- `exists_lift_of_opens U hU K s`: every morphism `s : Spec K ⟶ X` from the spectrum of a
  field factors as `s' ≫ (U i).ι` for some `i`. The spectrum has a single point, so the range
  of `s` lies in some `U i`; then `IsOpenImmersion.lift` applies.
- `hom_prop_of_opens U hU Pr f h`: let `Pr` be a property of morphisms that is local on the
  target. If it holds for `hom ((baseChange (U i).ι).map f)` for every `i`, it holds for
  `hom f`. The proof applies `IsZariskiLocalAtTarget.of_openCover` to the pullback of the open
  cover to the target abelian scheme. `hom_baseChange_isPullback` and
  `IsPullback.isoPullback_inv_snd` identify each local morphism with the cover's `pullbackHom`
  up to an isomorphism of sources.
- `Langlands.AbelianScheme.dualBaseChangeMap_comp stability universality b c A hA f`: for
  `f : A.X ⟶ dualScheme A hA`, the dual base change along `c ≫ b` equals
  `(groupHom (baseChangeCompIso b c A).hom).hom.hom ≫ D ≫
  dualSchemeMap (baseChangeCompIso b c A).hom _ _`. Here `D` is the successive base change,
  along `b` and then along `c`. The proof combines the Library coherence
  `dualSchemeBaseChangeIso_comp`, functoriality of `dualSchemeMap` (`dualSchemeMap_comp`,
  `dualSchemeMap_id`), naturality of `Over.pullbackComp`, and the fact that the comparison
  `baseChangeCompIso` has underlying map `(Over.pullbackComp c b).hom.app A.X`.

## Proof of `DualWitness.isPolarization_of_opens`

`IsPolarization` has two conjuncts.

1. *Isogeny.* By definition the restriction is `(baseChange (U i).ι).map lam` followed by
   the isomorphism `W.baseChangeIso P (U i).ι _`. Composing with the inverse isomorphism
   (`isIsogeny_of_iso`) shows that `(baseChange (U i).ι).map lam` is an isogeny.
   `isIsogeny_of_opens` concludes.
2. *Geometric points.* Let `s : Spec K ⟶ X` with `K` algebraically closed, and write
   `s = s' ≫ (U i).ι` (`exists_lift_of_opens`). The hypothesis at `s'` concerns the map
   `dualBaseChangeMap … s' (dualBaseChangeMap A W.hasDual P.universality (U i).ι
   (groupHom lam).hom.hom)`. This rewriting of the restricted map is
   `DualWitness.parameterMap_pullbackMap`. `dualBaseChangeMap_comp` expresses the map at `s`
   as its transport along the isomorphism `baseChangeCompIso (U i).ι s' A`.
   `hasFieldAmpleMumfordPresentation_iso` (module `PolarizationIsoTransport`) transports the
   ample Mumford presentation along this isomorphism.

## Provenance

Internal. The module derives standard locality facts from the Library's definitions and
published lemmas, and from Mathlib's locality of morphism properties, finite flat rank and
open immersions. It makes no literature claim. The polarization predicate follows the
sources cited in `RelativePolarization`.
