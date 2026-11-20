import Langlands.GroupScheme.Commutative.MultiplicativePartExistence
import Langlands.GroupScheme.CommutingFactorRetraction
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Rational.FppfQuotientAction

/-! # Uniqueness of a multiplicative-unipotent decomposition (Milne 16.13(b))

Over a field, homomorphisms from an affine unipotent group of finite type to a group of
multiplicative type are trivial. Consequently, in a commutative group `G` with an isomorphism
`U × S → G` given by multiplication of a unipotent closed subgroup `U` and a closed subgroup `S`
of multiplicative type, `U` contains every unipotent closed subgroup and `S` contains every
closed subgroup of multiplicative type.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CommutativeDecomposition

section HomVanishing

variable {k : Type u} [Field k]

/-- Over a field, every homomorphism from an affine unipotent group of finite type to a group
of multiplicative type is trivial. -/
theorem hom_eq_zero_of_isUnipotent_of_isMultiplicativeType
    {V S : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType V.X.hom] [IsAffineHom V.X.hom]
    (hV : IsUnipotent V) (hS : IsMultiplicativeType S) (f : V ⟶ S) : f = 0 := by
  have : IsAffineHom S.X.hom := hS.isAffineHom
  have : LocallyOfFiniteType S.X.hom := hS.locallyOfFiniteType
  obtain ⟨I, q, i, -, hIa, hi, hqi, hq⟩ := affineHomImage k V S f
  have : IsAffineHom I.X.hom := hIa
  have hIu : IsUnipotent I := hq.isUnipotent hV
  have hIm : IsMultiplicativeType I := hS.of_isClosedSubgroup i hi
  have h0 : 𝟙 I = 0 := hIm.hom_eq_zero_of_isUnipotent hIu (𝟙 I)
  apply eq_zero_of_hom_eq_one
  rw [← hqi, ← Category.id_comp i, h0]
  change (q ≫ (0 : I ⟶ I) ≫ i).hom.hom = 1
  simp only [Grp.comp_hom_hom]
  change q.hom.hom ≫ (1 : I.X ⟶ I.X) ≫ i.hom.hom = 1
  rw [MonObj.one_comp, MonObj.comp_one]

end HomVanishing

section Decomposition

variable {B : Scheme.{u}} {G U S : GroupScheme B} [IsCommMonObj G.X]

/-- Any two subgroups of a commutative group commute pointwise. -/
theorem commute_of_isCommMonObj (j : U ⟶ G) (i : S ⟶ G) (T : Over B) (h : T ⟶ U.X)
    (n : T ⟶ S.X) : Commute (h ≫ j.hom.hom) (n ≫ i.hom.hom) :=
  Commute.all _ _

/-- In a commutative group, multiplication of subgroups does not depend on the order of the
factors. -/
theorem subgroupMultiplication_swap (u : U ⟶ G) (s : S ⟶ G) :
    subgroupMultiplication s u = (β_ S.X U.X).hom ≫ subgroupMultiplication u s := by
  simp only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc,
    braiding_hom_fst, braiding_hom_snd]
  exact mul_comm _ _

/-- An isomorphic multiplication map is an isomorphism of groups. -/
theorem isIso_commutingSubgroupMultiplicationHom (u : U ⟶ G) (s : S ⟶ G)
    [IsIso (subgroupMultiplication u s)] :
    IsIso (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)) := by
  have : IsIso (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)).hom.hom := by
    rw [commutingSubgroupMultiplicationHom_hom]
    infer_instance
  have : IsIso ((Mon.forget (Over B)).map
      (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)).hom) := by
    change IsIso (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)).hom.hom
    infer_instance
  have : IsIso (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)).hom :=
    isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon (Over B)).map
      (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s))) := by
    change IsIso (commutingSubgroupMultiplicationHom u s (commute_of_isCommMonObj u s)).hom
    infer_instance
  exact isIso_of_reflects_iso _ (Grp.forget₂Mon _)

/-- If the multiplication of `U` and `S` is an isomorphism and a subgroup `H` maps trivially
to `U` under the resulting projection, then `H` lies in `S`. -/
theorem range_le_of_comp_commutingFactorRetraction (u : U ⟶ G) (s : S ⟶ G)
    [IsIso (subgroupMultiplication u s)] {H : GroupScheme B} (h : H ⟶ G)
    (h0 : letI := isIso_commutingSubgroupMultiplicationHom u s
      h ≫ commutingFactorRetraction u s (commute_of_isCommMonObj u s) = 0) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range s := by
  have := isIso_commutingSubgroupMultiplicationHom u s
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← comp_commutingFactorRetraction_eq_one_iff u s (commute_of_isCommMonObj u s),
    Category.assoc, ← Grp.comp_hom_hom, h0]
  exact MonObj.comp_one y

end Decomposition

section Field

variable {k : Type u} [Field k] {G U S : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsCommMonObj G.X]

omit [LocallyOfFiniteType G.X.hom] in
/-- **Milne 2017, Theorem 16.13(b), uniqueness, multiplicative part.** If multiplication
`U × S → G` is an isomorphism with `U` a unipotent closed subgroup, then `S` contains every
closed subgroup of multiplicative type. -/
theorem range_le_of_isMultiplicativeType (u : U ⟶ G) (s : S ⟶ G) (hu : IsClosedSubgroup u)
    (hU : IsUnipotent U) [IsIso (subgroupMultiplication u s)]
    {H : GroupScheme (Spec (CommRingCat.of k))} (h : H ⟶ G) (hH : IsMultiplicativeType H) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range s := by
  have : IsAffineHom U.X.hom := isAffineHom_of_isClosedSubgroup u hu
  have := isIso_commutingSubgroupMultiplicationHom u s
  exact range_le_of_comp_commutingFactorRetraction u s h
    (hH.hom_eq_zero_of_isUnipotent hU _)

/-- **Milne 2017, Theorem 16.13(b), uniqueness, unipotent part.** If multiplication
`U × S → G` is an isomorphism with `S` a closed subgroup of multiplicative type, then `U`
contains every unipotent closed subgroup. -/
theorem range_le_of_isUnipotent (u : U ⟶ G) (s : S ⟶ G) (hS : IsMultiplicativeType S)
    [IsIso (subgroupMultiplication u s)]
    {V : GroupScheme (Spec (CommRingCat.of k))} (j : V ⟶ G) (hj : IsClosedSubgroup j)
    (hV : IsUnipotent V) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range u := by
  have : IsAffineHom V.X.hom := isAffineHom_of_isClosedSubgroup j hj
  have : LocallyOfFiniteType V.X.hom := locallyOfFiniteType_of_isClosedSubgroup j hj
  have : IsIso (subgroupMultiplication s u) := by
    rw [subgroupMultiplication_swap]
    infer_instance
  have := isIso_commutingSubgroupMultiplicationHom s u
  exact range_le_of_comp_commutingFactorRetraction s u j
    (hom_eq_zero_of_isUnipotent_of_isMultiplicativeType hV hS _)

end Field

end CommutativeDecomposition

end Langlands.GroupScheme
