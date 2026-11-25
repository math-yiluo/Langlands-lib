/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorNaturalityComponent
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Degreewise currying for the Hom-total-tensor comparison

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
/-- The degreewise currying maps commute with simultaneous maps of all three complexes.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90),
functoriality (blueprint: lem-sc-hom-tensor-naturality).

Proof: Apply the product projections of the target Hom term and restrict to
each total-tensor summand, before sheafification. Evaluate on pure tensors
`x ⊗ y` over an arbitrary object of each localized site. The left side
first replaces the outer argument by `f(x)`, the inner one by `g(y)`, and
the value by `h` of that value, then uncurries. The right side first
uncurries and then precomposes with `f ⊗ g` and postcomposes with `h`.
Both therefore evaluate to `h(φ(f(x))(g(y)))`. The action of the Hom
bifunctor on product projections is exactly the pre- and post-composition
formula in `homComplex_exists`; the tensor-total map restricts to the
termwise tensor map. The defining pure-tensor equation for the chosen
currying maps identifies the two evaluations. The tensor, sheafification,
coproduct and product universal properties then imply equality. There
are no differential computations in this assertion, and no claim of
invertibility is included. -/
theorem homTensorDegreewiseMap_natural
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)).f n ≫
        homTensorDegreewiseMap R K' L' M' n =
      homTensorDegreewiseMap R K L M n ≫
        ((((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
          ((homComplexFunctor (R := R)).obj
            (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h).f n := by
  let := SheafOfModules.monoidalCategory R
  have hlim := (Classical.choose_spec
    (homComplex_projections_exists (R := R))).1
      (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M' n
  apply CategoryTheory.Limits.Fan.IsLimit.hom_ext hlim.some
  intro p
  exact homTensorDegreewiseMap_natural_component R K K' L L' M M' f g h
    n p (p + n) rfl

end CategoryTheory
