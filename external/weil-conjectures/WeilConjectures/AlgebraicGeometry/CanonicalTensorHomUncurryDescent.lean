/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension

/-! # Localization of componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Componentwise uncurrying descends to functions on derived morphisms.
The family obeys the localization equation and transport along isomorphisms.
Naturality for noninvertible morphisms is not asserted here.
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent).

Proof: Represent K and L by K-flat complexes P and Lc, and M by Mc.
The fixed resolution I(Mc) is K-injective and Hom(Lc,I(Mc)) is K-injective.
The localization map on morphisms into this Hom complex is bijective, so lift
an input derived morphism to a homotopy class, then to a chain map φ.
Apply the explicitly constructed schemeTensorHomUncurry to φ and localize,
composing with the tensor model comparison and the inverse resolution map.
A homotopy of φ gives a homotopy of its uncurrying: extend the degree-minus-one
uncurried components over the coproducts; the signed Hom differential calculation
of Tag 0A90 shows that its boundary is the difference of the chain maps.
Thus the resulting morphism depends only on the homotopy class. For two K-flat
representatives, a common K-flat resolution compares them. The component formula
commutes with precomposition and with the functorial resolution of the target;
localizing these identities cancels the quasi-isomorphisms and proves independence.
Transport along the chosen representative isomorphisms defines the functions.
Independence of these representatives also proves compatibility with all derived
isomorphisms in the three variables. The family is asserted to exist only as part
of this theorem; no definition selects an undetermined witness of this theorem.
To verify the equation for arbitrary L, resolve L by Lc. Both Hom(-,I(M)) and
P tensor - invert that quasi-isomorphism. The component formula commutes with it;
cancel its localized comparison to recover the displayed equation for L itself.
Zero input and zero complexes give zero, and no boundedness is used. -/
theorem exists_tensorHomUncurry_descent (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom := by
  let := schemeDerivedTensorMonoidal X
  obtain ⟨t, ht⟩ := exists_tensorHomUncurry_descent_representative X
  obtain ⟨s, hs, hi⟩ := exists_tensorHomUncurry_descent_extension X t ht
  refine ⟨s, ?_, hi⟩
  intro P L M hP φ
  exact (hs P L M hP φ).trans (ht P L M hP φ)

end AlgebraicGeometry
