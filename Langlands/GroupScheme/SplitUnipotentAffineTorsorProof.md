# Sections of split-unipotent torsors over affine schemes

This module proves the published proposition
`Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement` (task
21d6e245-dcea-4c7a-af4a-c532ea0dd295). Let H be a split-unipotent group over
a field k, and let T be an affine scheme over k. Every fpqc torsor under the
base change of H to T has a section over T. This is the standard vanishing of
H¹ for split-unipotent groups over affine schemes. The proof goes by dévissage
along the split series down to Ga, where H¹ of the structure sheaf vanishes on
an affine scheme. The argument below is a Čech-cocycle version, worked out for
this formalization; it does not follow a particular cited text.

The proof uses the cocycle and descent API of
`Langlands.GroupScheme.TorsorCocycle`. The one-dimensional vector-group case
comes from `Langlands.GroupScheme.SplitUnipotentTorsor.VectorCocycle`.

## The vanishing predicate

Fix a commutative ring R and a group scheme H over Spec R.
`CocyclesVanish H` says the following. Take any T : Over (Spec R) with T.left
affine, and any U : Over T.left with U.left affine and U.hom flat and
surjective. Then every `Cocycle` of the base change of H to T.left on U is
trivial.

## Kernel lemmas

Suppose j : K ⟶ H and q : H ⟶ V satisfy `SubgroupFunctor.range (kernelι q) =
SubgroupFunctor.range j`, as in an fppf quotient.

- `comp_comp_eq_one`: every point of K maps to 1 under j and then q.
- `exists_comp_eq_of_comp_eq_one`: every point x of H with x ≫ q = 1 factors
  through j.
- `baseChange_comp_comp_eq_one` and `baseChange_exists_comp_eq` transfer both
  facts to the base change along any b : S' ⟶ B. They use the Library's
  `baseChangePointsEquiv` and `baseChangePointsEquiv_comp`.
- `baseChange_mono`: base change keeps j.hom.hom a monomorphism, since
  `Over.pullback b` is a right adjoint.

## The trivial group

`cocyclesVanish_of_range_id_eq_bot`: if `SubgroupFunctor.range (𝟙 H) = ⊥`,
then every point of the base change of H is 1. The proof reads points through
`baseChangePointsEquiv`. Hence every cocycle is the coboundary of 1.

## The quotient map has a section

`exists_section` assumes the following:

- H.X.left and V.X.left are affine;
- q.hom.hom.left is flat, surjective and locally of finite presentation;
- the kernel condition above holds, and `CocyclesVanish K`.

It then gives σ : V.X ⟶ H.X with σ ≫ q.hom.hom = 𝟙.

The proof views H as U' := Over.mk q.hom.hom.left over the scheme V.X.left.
U'.hom is an effective epimorphism by Mathlib's fpqc instance (flat, surjective
and quasi-compact, since both schemes are affine). Write H' and V' for the base
changes of H and V to V.X.left. The identity of H.X.left gives a point F of H'
over U'. Its images under q agree at any two points a₁, a₂ of U' over a test
scheme, since both are the structure map. So the coboundary of F takes values
in the image of K. Its lift to K is trivial by `CocyclesVanish K`, applied with
T = V.X and the cover U'; let f₂ be the trivializing point. Put J = f₂ ≫ j.
Then J and F have the same coboundary, so J⁻¹ · F agrees at any two points.
`exists_section_of_forall_eq` therefore descends it to a section s of H' over
V.X.left. Composing s with the first projection of the pullback gives σ.
Since J maps to 1 in V, the images of J⁻¹ · F and F in V agree. Cancelling
the epimorphism U'.hom then shows σ ≫ q = 𝟙.

## The induction step

`cocyclesVanish_of_section`: suppose σ is a section of q, and
`CocyclesVanish V` and `CocyclesVanish K` hold. Then `CocyclesVanish H`.
Take a cocycle ξ of H on U. The proof follows the exact sequence of pointed
sets for H¹:

1. The image of ξ in V is a coboundary of some f₀.
2. Lift f₀ through σ to a point f₁ of H; base change of σ uses
   `baseChangePointsEquiv`.
3. The twist of ξ by f₁ maps to 1 in V, so it lifts to a cocycle of K.
4. That lift is trivial, so ξ is trivial, by `IsTrivial.of_lift` and
   `IsTrivial.of_twist`.

`cocyclesVanish_of_hasSplitSeries` takes `hvec`, the vanishing for every
one-dimensional vector group over Spec R. It proves `CocyclesVanish H` for
every H with `HasSplitSeries n H` and H.X.hom affine. The proof is by
induction on n:

- For n = 0, use the trivial-group lemma.
- For n + 1, the series supplies K, V, j and q. The closed immersion j makes
  j.hom.hom a monomorphism, and K.X.hom affine as a composite of affine
  morphisms; the induction hypothesis gives `CocyclesVanish K`.
- H.X.left is affine, and V.X.left is affine by
  `IsVectorGroupOfDimension.isAffineHom_overRing`. So `exists_section` gives a
  section of q, and the step lemma with `hvec V` concludes.

## Torsors

`exists_section_of_cocyclesVanish` assumes `CocyclesVanish H`, T affine over
Spec R, and X an fpqc torsor under the base change of H to T.left. It gives a
section of X over T.left. Since X.hom is quasi-compact and T.left is affine,
X.left is quasi-compact. Mathlib's
`Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`, applied to the
property `Flat`, then gives an affine W and a flat surjective p : W ⟶ X.left.
Its locality instances are supplied by hand. U := W over T.left, through
p ≫ X.hom, is affine, flat and surjective. It is also quasi-compact, so U.hom
is an effective epimorphism. The torsor cocycle of p is trivial by
`CocyclesVanish H`, and `exists_section_of_isTrivial` gives the section.

`splitUnipotentAffineTorsorStatement_of_vector` proves the published
statement from `hvec` for all rings. Unpack the split series from
`IsSplitUnipotent`. Then apply `cocyclesVanish_of_hasSplitSeries` over
Spec k, using the assumed `IsAffineHom H.X.hom`, followed by
`exists_section_of_cocyclesVanish`. The smoothness hypothesis of the
statement is not used.

## The theorem

`splitUnipotentAffineTorsorStatement` proves
`SplitUnipotentAffineTorsorStatement.{u}`. It applies
`splitUnipotentAffineTorsorStatement_of_vector`, with `hvec` supplied by
`Cocycle.isTrivial_of_isVectorGroupOfDimension_one` from
`Langlands.GroupScheme.SplitUnipotentTorsor.VectorCocycle` (written by
Worker 1389).
