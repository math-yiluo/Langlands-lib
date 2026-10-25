import Langlands.Cohomology.DivisibleSystem.Colimit
import Langlands.Cohomology.DivisibleSystem.InvariantTransitivity
import Langlands.Cohomology.ExactColimitQuasiIso
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
# Harris's direct limit `C_m^•` over shrinking subgroups and the comparison (2.6)

Harris 1999, §2, p.306: "Taking the direct limit as H shrinks to the identity, we obtain an
ℓ-divisible system of complexes C_m^• of projective Z/ℓ^mZ[S(ẽ)]-modules and a natural
S(ẽ)-equivariant quasi-isomorphism (2.6)". This module forms that direct limit and the
comparison.

The subgroups are indexed by a filtered preorder `ι : Type uG` with an antitone family `H` of
normal subgroups of finite index. In Harris's setting these are the open subgroups, normal in
`S(ẽ)`, of an open normal pro-`p` subgroup acting trivially on the cohomology, ordered by reverse
inclusion; this specialization is not formalized. The diagram
`quotientInvariantsDiagram` sends `i` to the inflation of Harris's `C_m^{•,H i}`
(`inflatedQuotientInvariantsTotalSystem`) and `i ≤ j` to the transition morphism
`quotientInvariantsTransition`; the functor laws are `quotientInvariantsTransition_refl` and
`quotientInvariantsTransition_comp`. Its colimit `quotientInvariantsLimit`, formed by
`colimitSystem`, is an `ℓ`-divisible system of `ℤ`-graded complexes of representations of `G`,
our `C_m^•`. The comparisons `quotientInvariantsTotalSystemToRepExtend` for the `H i` form a
cocone (`quotientInvariantsTransition_comp_toRepExtend`), and the induced morphism
`quotientInvariantsLimitToRepExtend` to the underlying complexes extended to `ℤ` is our (2.6).
Given `ProPInvariantSubcomplexStatement`, if all `H i` are pro-`p` with `p` a unit in `R`, it is
a quasi-isomorphism at every level `m` at which all `H i` act trivially on the cohomology
(`quasiIso_quotientInvariantsLimitToRepExtend`), because exact colimits preserve
quasi-isomorphisms (`ExactColimit.quasiIso_isColimit_desc`).

The colimits are taken in `Rep R G`, where filtered colimits are exact: the first section provides
these instances for abelian groups, modules and representations (Mathlib provides AB5 for
`ModuleCat.{u} R` only when `R : Type u`).
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w uR uG t w' u v

section ExactColimits

variable (J : Type t) [SmallCategory J] [IsFiltered J] [UnivLE.{t, w'}]

/-- Filtered colimits of shape `J : Type t` in `AddCommGrpCat.{w'}` are exact, for `t ≤ w'`. -/
instance hasExactColimitsOfShape_addCommGrpCat :
    HasExactColimitsOfShape J AddCommGrpCat.{w'} :=
  have : AB5OfSize.{t, t} AddCommGrpCat.{w'} :=
    AB5OfSize_of_univLE.{t, t, w', w'} AddCommGrpCat.{w'}
  AB5OfSize.ofShape J

/-- Filtered colimits of shape `J : Type t` in `ModuleCat.{w'} R` are exact, for `t ≤ w'` and any
ring `R`. -/
instance hasExactColimitsOfShape_moduleCat (R : Type u) [Ring R] :
    HasExactColimitsOfShape J (ModuleCat.{w'} R) :=
  HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat.{w'})

/-- `Rep.{w'} k G` has colimits of shape `J : Type t`, for `t ≤ w'`. -/
instance hasColimitsOfShape_rep (k : Type u) [CommRing k] (G : Type v) [Monoid G] :
    HasColimitsOfShape J (Rep.{w'} k G) :=
  have := hasColimitsOfSizeOfUnivLE.{w', w', t, t} (Rep.{w'} k G)
  inferInstance

/-- Filtered colimits of shape `J : Type t` in `Rep.{w'} k G` are exact, for `t ≤ w'`. -/
instance hasExactColimitsOfShape_rep (k : Type u) [CommRing k] (G : Type v) [Monoid G] :
    HasExactColimitsOfShape J (Rep.{w'} k G) :=
  have : PreservesColimitsOfSize.{t, t} (forget₂ (Rep.{w'} k G) (ModuleCat.{w'} k)) :=
    preservesColimitsOfSize_of_univLE.{w', w', t, t} _
  HasExactColimitsOfShape.domain_of_functor J (forget₂ (Rep.{w'} k G) (ModuleCat.{w'} k))

end ExactColimits

namespace DivisibleSystem

section Limit

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))

/-- The diagram of the inflated systems `C_m^{•,H i}` over a preorder `ι` with an antitone family
of normal subgroups `H i` of finite index, with the transition morphisms. -/
@[simps]
def quotientInvariantsDiagram :
    ι ⥤ DivisibleSystem (CochainComplex (Rep.{max w uR uG} R G) ℤ) ℓ where
  obj i := inflatedQuotientInvariantsTotalSystem.{w, uR, uG} N K (H i) (hK i)
  map {i j} f := quotientInvariantsTransition.{w, uR, uG} K (hH (leOfHom f)) N (hK i) (hK j)
    (hk (leOfHom f))
  map_id i := quotientInvariantsTransition_refl.{w, uR, uG} K N (hK i) (hk (le_refl i))
  map_comp {i j l} f g := (quotientInvariantsTransition_comp.{w, uR, uG} K N (hH (leOfHom f))
    (hH (leOfHom g)) (hK i) (hK j) (hK l) (hk (leOfHom f)) (hk (leOfHom g))).symm

variable [IsFiltered ι]

/-- Our rendering of Harris's `C_m^•`: the colimit over `ι` of the inflated systems
`C_m^{•,H i}`, an `ℓ`-divisible system of `ℤ`-graded complexes of representations of `G`. -/
abbrev quotientInvariantsLimit : DivisibleSystem (CochainComplex (Rep.{max w uR uG} R G) ℤ) ℓ :=
  colimitSystem (quotientInvariantsDiagram.{w, uR, uG} N K H hH hK hk)

/-- The cocone of the comparisons `quotientInvariantsTotalSystemToRepExtend` over the diagram, for
`K` vanishing in degrees `q ≥ N`. -/
@[simps]
def quotientInvariantsDiagramCocone (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    Cocone (quotientInvariantsDiagram.{w, uR, uG} N K H hH hK hk) where
  pt := K.toRepComplexes.extendSystem
  ι :=
    { app i := quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K (H i) (hK i) hN
      naturality {i j} f := (quotientInvariantsTransition_comp_toRepExtend.{w, uR, uG} K
        (hH (leOfHom f)) N (hK i) (hK j) (hk (leOfHom f)) hN).trans (Category.comp_id _).symm }

/-- Our rendering of Harris's comparison (2.6): the morphism from `quotientInvariantsLimit` to the
underlying complexes of representations of `K` extended to `ℤ`, induced by the comparisons for
the `H i`. -/
abbrev quotientInvariantsLimitToRepExtend (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    quotientInvariantsLimit.{w, uR, uG} N K H hH hK hk ⟶ K.toRepComplexes.extendSystem :=
  colimitSystemDesc _ (quotientInvariantsDiagramCocone.{w, uR, uG} N K H hH hK hk hN)

variable [IsTopologicalGroup G]

/-- Given `ProPInvariantSubcomplexStatement`, if every `H i` is a normal pro-`p` subgroup with `p`
invertible in `R` acting trivially on the cohomology at level `m`, then the comparison (2.6) is a
quasi-isomorphism at level `m`. -/
theorem quasiIso_quotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ)
    (htriv : ∀ i q (h : H i), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower.app
      (op m)) := by
  have : IsConnected ι := IsFiltered.isConnected ι
  exact ExactColimit.quasiIso_isColimit_desc (colimit.isColimit _) _ fun i =>
    quasiIso_quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K hS (hP i) hR (hK i) hN m
      (htriv i)

end Limit

end DivisibleSystem

end Langlands.Cohomology
