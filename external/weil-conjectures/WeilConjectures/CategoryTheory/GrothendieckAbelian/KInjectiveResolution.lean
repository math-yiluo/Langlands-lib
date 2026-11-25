/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Every Grothendieck abelian category has K-injective resolutions

Let `C` be a Grothendieck abelian category. In this file we show that every cochain complex in
`C` admits, functorially, a monomorphic quasi-isomorphism into a K-injective complex, and in
particular that `CategoryTheory.Abelian.HasKInjectiveResolutions C` holds. This is a theorem of
Alonso Tarrío–Jeremías López–Souto Salorio and of Serpé.

The proof runs the small object argument in `CochainComplex C ℤ` for the Serpé generating set
`CochainComplex.serpeGeneratingSet C`, exactly as
`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean` runs it for the
generating monomorphisms of `C`. Since that set has the same right lifting property as the
class of all monomorphic quasi-isomorphisms, and since the retracts of transfinite compositions
of pushouts of coproducts of monomorphic quasi-isomorphisms are again monomorphic
quasi-isomorphisms, the monomorphic quasi-isomorphisms are the maps with the left lifting
property with respect to their own right lifting property. Hence any morphism factors
functorially as a monomorphic quasi-isomorphism followed by a morphism with the right lifting
property with respect to all monomorphic quasi-isomorphisms. Applying this to `K ⟶ 0`:

```
  K ───0───→ 0
   ╲        ↗
  i ╲      ╱ p
     ↘    ╱
       I K
```

with `i` a monomorphic quasi-isomorphism and `p` in `(monoQuasiIso C _).rlp`, and such an
`I K` is K-injective by `CochainComplex.isKInjective_of_rlp`.

## Main results

- `CochainComplex.llp_rlp_monoQuasiIso`: the monomorphic quasi-isomorphisms of cochain
  complexes in a Grothendieck abelian category are exactly the morphisms with the left lifting
  property with respect to the morphisms with the right lifting property with respect to them.
- `CochainComplex.hasFunctorialFactorization_monoQuasiIso`: every morphism of cochain complexes
  factors functorially as a monomorphic quasi-isomorphism followed by a morphism with the right
  lifting property with respect to all monomorphic quasi-isomorphisms. Together with the
  previous result, this says that these two classes form a weak factorization system.
- `CochainComplex.kInjectiveResolutionFunctor` and `CochainComplex.toKInjectiveResolution`: the
  functorial K-injective replacement `K ↦ I K`, together with the natural monomorphic
  quasi-isomorphism `K ⟶ I K`.
- `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`: every Grothendieck
  abelian category has K-injective resolutions.

## References

* L. Alonso Tarrío, A. Jeremías López, M. J. Souto Salorio, *Localization in categories of
  complexes and unbounded resolutions*
* C. Serpé, *Resolution of unbounded complexes in Grothendieck categories*
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty HomologicalComplex ZeroObject

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- In a Grothendieck abelian category, the monomorphic quasi-isomorphisms of cochain complexes
are exactly the morphisms having the left lifting property with respect to the morphisms having
the right lifting property with respect to all monomorphic quasi-isomorphisms:

```
  A ────f───→ X
  │        ↗  │
  i     ∃ ℓ   p
  ↓  ↗        ↓
  B ────g───→ Y
```

that is, `i` is a monomorphic quasi-isomorphism if and only if every such commutative square
with `p` in `(monoQuasiIso C _).rlp` admits a lift `ℓ`. -/
lemma llp_rlp_monoQuasiIso :
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp.llp = monoQuasiIso C (ComplexShape.up ℤ) := by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← serpeGeneratingSet_rlp.{w} C, llp_rlp_of_hasSmallObjectArgument]
  exact le_trans (retracts_monotone (transfiniteCompositions_monotone
    (pushouts_monotone (coproducts_monotone (serpeGeneratingSet_le C)))))
    (transfiniteCompositions_coproducts_pushouts_le.{w} C)

/-- In a Grothendieck abelian category, every morphism of cochain complexes factors
functorially as

```
  X ────f───→ Y
   ╲        ↗
  i ╲      ╱ p
     ↘    ╱
        Z
```

with `i` a monomorphic quasi-isomorphism and `p` a morphism having the right lifting property
with respect to all monomorphic quasi-isomorphisms. This is the factorization produced by the
small object argument for `CochainComplex.serpeGeneratingSet C`. -/
instance hasFunctorialFactorization_monoQuasiIso :
    HasFunctorialFactorization (monoQuasiIso C (ComplexShape.up ℤ))
      (monoQuasiIso C (ComplexShape.up ℤ)).rlp := by
  -- It suffices to factor as `(serpeGeneratingSet C).rlp.llp` followed by
  -- `(serpeGeneratingSet C).rlp`, which is what the small object argument provides. The first
  -- rewrite handles the right hand class, the second the left hand one, and the third the
  -- occurrence of `.rlp` that the second rewrite has re-created.
  rw [← serpeGeneratingSet_rlp.{w} C, ← llp_rlp_monoQuasiIso.{w} C, ← serpeGeneratingSet_rlp.{w} C]
  infer_instance

/-- The monomorphic quasi-isomorphisms of cochain complexes in a Grothendieck abelian category
and the morphisms with the right lifting property with respect to them form a weak factorization
system: the trivial cofibrations and the fibrations of the model structure of Serpé on
`CochainComplex C ℤ`. -/
instance isWeakFactorizationSystem_monoQuasiIso :
    IsWeakFactorizationSystem (monoQuasiIso C (ComplexShape.up ℤ))
      (monoQuasiIso C (ComplexShape.up ℤ)).rlp where
  rlp := rfl
  llp := llp_rlp_monoQuasiIso.{w} C

/-- `X ↦ Arrow.mk (0 : X ⟶ 0)`, as a functor. -/
@[simps]
noncomputable def toArrowZero : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj X := Arrow.mk (0 : X ⟶ (0 : CochainComplex C ℤ))
  map f := Arrow.homMk f (𝟙 _)

/-- The functorial K-injective replacement `K ↦ I K` in a Grothendieck abelian category: it is
obtained by factoring `K ⟶ 0` functorially as a monomorphic quasi-isomorphism `K ⟶ I K`
followed by a morphism `I K ⟶ 0` with the right lifting property with respect to all
monomorphic quasi-isomorphisms. -/
noncomputable def kInjectiveResolutionFunctor :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  toArrowZero C ⋙ (functorialFactorizationData (monoQuasiIso C (ComplexShape.up ℤ))
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp).Z

/-- The natural monomorphic quasi-isomorphism `K ⟶ I K` from a cochain complex to its
functorial K-injective replacement. -/
noncomputable def toKInjectiveResolution :
    𝟭 (CochainComplex C ℤ) ⟶ kInjectiveResolutionFunctor.{w} C where
  app X := (functorialFactorizationData (monoQuasiIso C (ComplexShape.up ℤ))
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp).i.app ((toArrowZero C).obj X)
  naturality _ _ f := (functorialFactorizationData (monoQuasiIso C (ComplexShape.up ℤ))
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp).i.naturality ((toArrowZero C).map f)

lemma monoQuasiIso_toKInjectiveResolution_app (K : CochainComplex C ℤ) :
    monoQuasiIso C (ComplexShape.up ℤ) ((toKInjectiveResolution.{w} C).app K) :=
  (functorialFactorizationData _ _).hi _

instance isKInjective_kInjectiveResolutionFunctor_obj (K : CochainComplex C ℤ) :
    CochainComplex.IsKInjective ((kInjectiveResolutionFunctor.{w} C).obj K) :=
  isKInjective_of_rlp ((functorialFactorizationData (monoQuasiIso C (ComplexShape.up ℤ))
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp).p.app ((toArrowZero C).obj K))
    (isZero_zero _) ((functorialFactorizationData _ _).hp _)

end CochainComplex

namespace CategoryTheory.Abelian

/-- Every Grothendieck abelian category has K-injective resolutions: any cochain
complex admits a monomorphic quasi-isomorphism into a K-injective complex. This is a
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé. -/
instance hasKInjectiveResolutions_of_isGrothendieckAbelian
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasKInjectiveResolutions C where
  exists_isKInjective K :=
    ⟨(CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K, inferInstance,
      (CochainComplex.toKInjectiveResolution.{w} C).app K,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).1,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).2⟩

end CategoryTheory.Abelian
