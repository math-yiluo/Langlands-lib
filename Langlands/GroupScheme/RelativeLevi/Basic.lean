import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Parabolic subgroups, unipotent radicals and Levi subgroups over a base scheme

These predicates transcribe Conrad, *Reductive group schemes* (2014), Definition 5.2.1,
the characterization in Corollary 5.2.5, and Definition 5.4.2. They neither choose a
unipotent radical or Levi subgroup nor assert that one exists.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

namespace RelativeLevi

/-- The base change of a group-scheme homomorphism to the residue field `κ(s)` of a
point `s` of the base, along `Spec κ(s) ⟶ S`. -/
abbrev residueFiberHom {H G : GroupScheme S} (f : H ⟶ G) (s : S) :
    (GroupScheme.baseChange (S.fromSpecResidueField s :
      Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj H ⟶
    (GroupScheme.baseChange (S.fromSpecResidueField s :
      Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj G :=
  (GroupScheme.baseChange (S.fromSpecResidueField s :
    Spec (CommRingCat.of (S.residueField s)) ⟶ S)).map f

/-- The base change of a group-scheme homomorphism to the geometric point
`Spec κ(s)^alg ⟶ S` over a point `s` of the base. -/
abbrev geometricFiberHom {H G : GroupScheme S} (f : H ⟶ G) (s : S) :
    geometricFiber H s ⟶ geometricFiber G s :=
  (GroupScheme.baseChange (geometricPoint S s)).map f

end RelativeLevi

open RelativeLevi

/-- A **parabolic subgroup** over a base scheme (Conrad 2014, Definition 5.2.1): `P` is
smooth and affine over `S`, the homomorphism `i : P ⟶ G` is a monomorphism of `S`-schemes,
and for every point `s` of `S` the fibre `i_s : P_s ⟶ G_s` over the residue field `κ(s)`
is a parabolic subgroup. The source states the definition for reductive `G`; this
predicate imposes no condition on `G`, and reductivity is a separate hypothesis. -/
structure IsRelativeParabolicSubgroup {P G : GroupScheme S} (i : P ⟶ G) : Prop where
  smooth : Smooth P.X.hom
  isAffineHom : IsAffineHom P.X.hom
  mono : Mono i.hom.hom
  residueFiber : ∀ s : S, IsParabolicSubgroup (residueFiberHom i s)

/-- A **unipotent radical** over a base scheme, in the sense of the characterization in
Conrad 2014, Corollary 5.2.5: `r : U ⟶ P` is a smooth closed normal subgroup whose
geometric fibre at every point `s` of `S` is the unipotent radical of the geometric fibre
`P_{s̄}`. -/
structure IsRelativeUnipotentRadical {U P : GroupScheme S} (r : U ⟶ P) : Prop where
  isClosedSubgroup : IsClosedSubgroup r
  smooth : Smooth U.X.hom
  isNormal : (SubgroupFunctor.range r).IsNormal
  geometricFiber : ∀ s : S, IsUnipotentRadical (geometricFiberHom r s)

/-- A **Levi subgroup** over a base scheme (Conrad 2014, Definition 5.4.2): `l : L ⟶ P`
is a smooth closed subgroup such that, for some unipotent radical `r : U ⟶ P` over the
base, the multiplication morphism `L ×_S U ⟶ P`, `(x, u) ↦ l(x) r(u)`, is an isomorphism
of schemes over `S`. -/
structure IsRelativeLeviSubgroup {L P : GroupScheme S} (l : L ⟶ P) : Prop where
  isClosedSubgroup : IsClosedSubgroup l
  smooth : Smooth L.X.hom
  exists_unipotentRadical : ∃ (U : GroupScheme S) (r : U ⟶ P),
    IsRelativeUnipotentRadical r ∧ IsIso (subgroupMultiplication l r)

end Langlands.GroupScheme
