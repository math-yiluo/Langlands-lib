/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass

/-!
# The class of a frame

Let `z : Z ⟶ V` be a closed immersion. A *frame at `Z`* is an étale `V`-scheme `e : U ⟶ V`
together with functions `f₁, …, f_c ∈ Γ(U, 𝒪_U)` generating the ideal of `Z ∩ U = Z ×_V U`. The
*class of the frame* is the cup product with supports of the Kummer boundaries

`cl(f) = ∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c) ∈ H^{2c}_{Z ∩ U}(U, Λ(c))`

(`AlgebraicGeometry.Etale.kummerBoundaryProduct`), a class supported on `V(f₁, …, f_c)`, which
is `Z ∩ U`. Classes with supports only depend on the support: for closed immersions `i`, `i'`
with the same range, `Ri_! Ri^! L ≅ Ri'_! Ri'^! L` compatibly with the counits
(`AlgebraicGeometry.Etale.supportedTransportIso`), so the class is read in
`H^{2c}_{Z ∩ U}(U, Λ(c))`.

## Main definitions

- `AlgebraicGeometry.Etale.supportedTransportIso`: `Ri_! Ri^! L ≅ Ri'_! Ri'^! L` for closed
  immersions with the same range.
- `AlgebraicGeometry.Etale.PurityFrame`: frames at a closed subscheme.
- `AlgebraicGeometry.Etale.PurityFrame.cl`: the class of a frame.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Transport

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X Z Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) [IsClosedImmersion i]
  [IsClosedImmersion i']

/-- `Ri_! Ri^! L` is supported on the range of `i`, hence on the range of any closed immersion
`i'` with the same range. -/
lemma isZero_leftDerivedUpperStar_openComplement_obj_of_range_eq
    (h : Set.range i.base = Set.range i'.base)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj L))) :=
  isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i
      i'.openComplement.ι
    (by rw [h, i'.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left) _
    subset_rfl _

/-- For closed immersions `i`, `i'` with the same range, the counit `Ri_! Ri^! L ⟶ L` lifts
uniquely through the counit `Ri'_! Ri'^! L ⟶ L`
(`AlgebraicGeometry.Etale.existsUnique_comp_counit_of_isZero`). It is *defined* as
`Classical.choose`; uniqueness makes the choice canonical. -/
noncomputable def supportedTransport (h : Set.range i.base = Set.range i'.base)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) ⟶ (R(i')_![ModuleCat.{u + 1} Λ]).obj
        ((R(i')^![Λ]).obj L) :=
  (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_obj_of_range_eq Λ i i' h L)
    ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)).exists.choose

@[reassoc (attr := simp)]
lemma supportedTransport_comp_counit (h : Set.range i.base = Set.range i'.base)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedTransport Λ i i' h L ≫ (rightDerivedUpperShriekAdjunction Λ i').counit.app L =
      (rightDerivedUpperShriekAdjunction Λ i).counit.app L :=
  (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_obj_of_range_eq Λ i i' h L)
    ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)).exists.choose_spec

/-- **Classes with supports only depend on the support.** For closed immersions `i`, `i'` with
the same range, `Ri_! Ri^! L ≅ Ri'_! Ri'^! L` compatibly with the counits: both lifts are unique,
and their composites lift the counits to themselves. -/
noncomputable def supportedTransportIso (h : Set.range i.base = Set.range i'.base)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) ≅ (R(i')_![ModuleCat.{u + 1} Λ]).obj
        ((R(i')^![Λ]).obj L) where
  hom := supportedTransport Λ i i' h L
  inv := supportedTransport Λ i' i h.symm L
  hom_inv_id :=
    (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι
      (isZero_leftDerivedUpperStar_openComplement_obj_of_range_eq Λ i i rfl L)
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)).unique (by simp)
        (Category.id_comp _)
  inv_hom_id :=
    (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι
      (isZero_leftDerivedUpperStar_openComplement_obj_of_range_eq Λ i' i' rfl L)
      ((rightDerivedUpperShriekAdjunction Λ i').counit.app L)).unique (by simp)
        (Category.id_comp _)

end Transport

section Frame

variable (Λ : Type (u + 1)) [CommRing Λ] [HasKummerClass Λ] [Finite Λ]

/-- Blueprint `proposition-purity-vector-bundles`: Class of a frame

A *frame* at a closed subscheme `z : Z ⟶ V`: an étale `V`-scheme `e : U ⟶ V` together with
functions `f₁, …, f_c ∈ Γ(U, 𝒪_U)` generating the ideal of `Z ∩ U = Z ×_V U` in `U`. In the
purity setting `V ⟶ B` is smooth and `Z ⟶ B` is smooth, `Z` of pure codimension `c` in `V`;
these hypotheses on the ambient family are not needed to define a frame or its class. -/
structure PurityFrame {V Z : Scheme.{u}} (z : Z ⟶ V) [IsClosedImmersion z] (c : ℕ) where
  /-- The étale `V`-scheme of the frame. -/
  U : Scheme.{u}
  /-- The étale structure morphism. -/
  e : U ⟶ V
  [etale : AlgebraicGeometry.Etale e]
  /-- The functions of the frame. -/
  f : Fin c → Γ(U, ⊤)
  /-- The functions generate the ideal of `Z ∩ U = Z ×_V U`. -/
  ker_eq : (pullback.snd z e).ker = IdealSheafData.ofIdealTop (Ideal.span (Set.range f))

namespace PurityFrame

variable {Λ} {V Z : Scheme.{u}} {z : Z ⟶ V} [IsClosedImmersion z] {c : ℕ}

attribute [instance] PurityFrame.etale

/-- The functions of a frame cut out `Z ∩ U`: the zero locus `V(f₁, …, f_c)` has the same
underlying set as `Z ×_V U`. -/
lemma range_zeroLocusSubschemeι (F : PurityFrame z c) :
    Set.range (F.U.zeroLocusSubschemeι (Set.range F.f)).base =
      Set.range (pullback.snd z F.e).base := by
  rw [IdealSheafData.range_subschemeι, ← F.ker_eq, Scheme.Hom.support_ker,
    (pullback.snd z F.e).isClosedEmbedding.isClosed_range.closure_eq]

variable (Λ) in
/-- Blueprint `proposition-purity-vector-bundles`: Class of a frame

The *class of a frame* `(U, f₁, …, f_c)` at `Z`: the cup product with supports of the Kummer
boundaries `α_k = ∂κ(f_k) ∈ H²_{V(f_k)}(U, Λ(1))`,

`cl(f) = α₁ ∪ ⋯ ∪ α_c ∈ H^{2c}_{Z ∩ U}(U, Λ(c)) = Hom(Λ_U, Ri_! Ri^! (Λ_U(c)[2c]))`,

where `i : Z ×_V U ⟶ U` (`AlgebraicGeometry.Etale.kummerBoundaryProduct`, read through
`V(f₁, …, f_c) = Z ∩ U`, `AlgebraicGeometry.Etale.supportedTransportIso`). Each factor has degree
two and twist one, and their supports meet in `Z ∩ U`, giving degree `2c` and twist `c`. -/
noncomputable def cl (F : PurityFrame z c) [HasInvertibleExponent Λ V] :
    haveI : HasInvertibleExponent Λ F.U := .of_hom F.e
    constantComplex Λ F.U ⟶ (R(pullback.snd z F.e)_![ModuleCat.{u + 1} Λ]).obj
      ((R(pullback.snd z F.e)^![Λ]).obj ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  haveI : HasInvertibleExponent Λ F.U := .of_hom F.e
  kummerBoundaryProduct Λ F.f ≫ (supportedTransportIso Λ _ _
    F.range_zeroLocusSubschemeι _).hom

end PurityFrame

end Frame

end Etale

end AlgebraicGeometry
