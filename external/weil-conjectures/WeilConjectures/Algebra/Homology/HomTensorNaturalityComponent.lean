/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorLocalizedExt
import WeilConjectures.Algebra.Homology.HomTensorCurryNaturalPure

/-!
# A single component of currying naturality

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- Naturality after one projection of the target Hom complex.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90),
functoriality; its proof refers to More on Algebra, Lemma 15.73.1.
(blueprint: lem-sc-hom-tensor-naturality-component)

Proof: Fix the total source degree `p` and target degree `q = p + n`.
Use extensionality of sheaf morphisms, then of sections of the internal Hom:
a section over `U` is a map on the localized site over `U`. For each such
section of the iterated Hom, compare the resulting maps out of the total
source term on that localized site. The total term is the coproduct of
`K'^i ⊗ L'^j` with `i + j = p`. It suffices to compare on each summand.
By the sheafification adjunction, maps out of that sheaf tensor are determined
on the presheaf tensor; by the tensor universal property they are determined
on pure tensors `x ⊗ y` over every further object of the localized site.

The componentwise functoriality formula in `homComplex_exists` says that
precomposition by `f` sends the outer map to evaluation at `f^i(x)`,
precomposition by `g` sends the inner map to evaluation at `g^j(y)`,
and postcomposition applies `h^q` to the resulting value. Apply the defining
equation `homTensorDegreewiseMap_spec` at `(i,j)` to the left composite:
its value is `h^q(φ_i(f^i(x))_j(g^j(y)))`.
For the right composite the same functoriality formula precomposes with
the degree-`p` total tensor map and postcomposes with `h^q`.
The identity `HomologicalComplex.ι_mapBifunctorMap` restricts that map to
the termwise tensor map on the `(i,j)` summand. Naturality of the
sheafification unit and tensor comparison sends the image of `x ⊗ y` to
the image of `f^i(x) ⊗ g^j(y)`. The same defining currying equation
therefore gives the same value. These formulas commute with all localized
restrictions, since they are presheaf morphisms. Tensor, sheafification,
coproduct, internal-Hom and sheaf-morphism extensionality give the asserted
single-projection equality. No product extensionality for the target Hom term
and no differential calculation enter this component argument. -/
theorem homTensorDegreewiseMap_natural_component
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    letI := SheafOfModules.monoidalCategory R
    (((((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)).f n ≫
        homTensorDegreewiseMap R K' L' M' n) ≫
      homTensorProjection R (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M' n p q hpq =
    (homTensorDegreewiseMap R K L M n ≫
        ((((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
          ((homComplexFunctor (R := R)).obj
            (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h).f n) ≫
      homTensorProjection R (CochainComplex.mapBifunctor K' L'
        (curriedTensor Mod)) M' n p q hpq := by
  let := SheafOfModules.monoidalCategory R
  subst q
  apply homTensorLocalized_ext R K' L' (M'.X (p + n)) _ p
  intro U s W i j hij x y
  subst p
  exact homTensorCurry_natural_pure R K K' L L' M M' f g h n
    (homTensorDegreewiseMap R K L M n) (homTensorDegreewiseMap R K' L' M' n)
    (homTensorDegreewiseMap_spec R K L M n).1
    (homTensorDegreewiseMap_spec R K' L' M' n).1 U s W i j x y

end CategoryTheory
