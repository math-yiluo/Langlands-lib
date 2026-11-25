/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.HomTensorNaturality

/-!
# Hom complexes and the total tensor complex

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90)
(blueprint: lem-sc-derived-hom-tensor-total).
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

-- The `max u v` module universe makes the `HasMapBifunctor` instance term exceed the default
-- `synthInstance.maxSize` of 128 (as for `CochainComplex.IsKFlatTensor`).
set_option synthInstance.maxSize 256 in
/-- The Hom-total-tensor isomorphism, natural contravariantly in `K` and `L` and
covariantly in `M`. Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1
(Tag 0A90) (blueprint: lem-sc-derived-hom-tensor-total).

Proof:
1. Expand the degree-`n` terms using `def-pur-hom-complex`. The left side is
   the product, over `p,q`, of internal Homs from `K^p ⊗ L^q` to `M^(p+q+n)`.
   On the right, maps out of the direct sum in `def-pc-tensor-complex-sheaves`
   give the same product. Use `lem-pc-sheaf-modules-tensor-closed` on every
   localized site to identify these internal Hom sheaves.
2. Curry each component, sending `x ⊗ y` to `f(x)(y)`. Restriction to the
   summands followed by uncurrying is the inverse, by the tensor-Hom adjunction.
3. Check the differential on the `(p,q)` summand. The outer Hom differential
   contributes `-(-1)^n f d_K`, the inner one `-(-1)^(p+n) f d_L`.
   These agree with precomposition with `d_K ⊗ 1 + (-1)^p 1 ⊗ d_L` on the
   total tensor, followed by the degree-`n` Hom differential. Thus the
   degreewise inverse maps are chain maps.
4. Componentwise pre- and post-composition commute with currying by naturality
   of `lem-pc-sheaf-modules-tensor-closed`. This gives the displayed equation
   for simultaneous maps in all three complexes. -/
theorem homComplex_tensorTotal_iso :
    letI := SheafOfModules.monoidalCategory R
    ∃ e : ∀ (K L M : CochainComplex Mod ℤ),
      homComplex (R := R) K (homComplex (R := R) L M) ≅
        homComplex (R := R) (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M,
      ∀ (K K' L L' M M' : CochainComplex Mod ℤ)
        (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M'),
        (((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
            ((homComplexFunctor (R := R)).obj (op K')).map
              ((((homComplexFunctor (R := R)).map g.op).app M) ≫
                ((homComplexFunctor (R := R)).obj (op L')).map h) ≫
            (e K' L' M').hom =
          (e K L M).hom ≫
            (((homComplexFunctor (R := R)).map
              (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
            ((homComplexFunctor (R := R)).obj
              (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h := by
  let := SheafOfModules.monoidalCategory R
  have (K L M : CochainComplex Mod ℤ) (n : ℤ) :
      IsIso (homTensorDegreewiseMap R K L M n) :=
    (homTensorDegreewiseMap_spec R K L M n).2
  let e (K L M : CochainComplex Mod ℤ) :
      homComplex (R := R) K (homComplex (R := R) L M) ≅
        homComplex (R := R) (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ asIso (homTensorDegreewiseMap R K L M n))
      (fun n m _ ↦ homTensorDegreewiseMap_comm R K L M n m)
  refine ⟨e, ?_⟩
  intro K K' L L' M M' f g h
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [e]
  exact homTensorDegreewiseMap_natural R K K' L L' M M' f g h n

end CategoryTheory
