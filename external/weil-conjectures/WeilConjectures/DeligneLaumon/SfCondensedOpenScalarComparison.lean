/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # The normalized condensed coefficient comparison for open extension

The open-extension step of `lemma-weight-bounds-partitions` uses module objects over
pulled-back condensed coefficient rings. Its coefficient comparison is the conjugate of the
specified scalar-restriction/pullback square along the derived open and scalar adjunctions.

Source: current blueprint `lem-zl-morphism-open-closed-reduction.proof.md`, Part 2,
and `sec-six-functors-basics/sk-prop-scalar-six/def-sfb-derived-open-immersion-shriek-iso.md`
(blueprint: def-zl-normalized-integral-scalar-comparison).

The distinct name `sfCondensedOpenScalarComparison` denotes this canonical comparison.
The construction works for arbitrary commutative condensed rings and every open immersion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The scalar/open comparison is uniquely determined by the specified right-adjoint square.
Source: latest blueprint, `lem-zl-morphism-open-closed-reduction.proof.md`, Part 2,
open extension; the coefficient compatibility of module extension by zero.
(blueprint: def-zl-normalized-integral-scalar-comparison).

Proof: compose the derived scalar-extension/restriction adjunction with the derived open
adjunction on each side. Conjugation is an equivalence between their natural-isomorphism
types. Apply its inverse to the canonical scalar-restriction/pullback comparison. The two
inverse equations give the normalization and uniqueness. Thus the map is fixed by the
actual adjunctions, rather than chosen as an unspecified isomorphism. No flatness, finite
Tor amplitude, boundedness or constructibility assumption enters this argument; it also
covers the identity immersion, the empty open and zero objects. -/
theorem sfCondensedOpenScalarComparison_existsUnique :
    ∃! c : D(CondensedRing.openImmersionLowerShriek Λ j) ⋙
        L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a U)) ⋙
        D(CondensedRing.openImmersionLowerShriek Λ' j),
      conjugateIsoEquiv
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
          (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))) c =
        CondensedRing.derivedComapUpperStarIso a j := by
  let e := conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
  exact ⟨e.symm (CondensedRing.derivedComapUpperStarIso a j),
    e.apply_symm_apply _, fun c hc ↦ e.injective (hc.trans (e.apply_symm_apply _).symm)⟩

/-- The normalized scalar/open-extension comparison on the current condensed coefficients.
Source: latest blueprint, `lem-zl-morphism-open-closed-reduction.proof.md`, Part 2.
(blueprint: def-zl-normalized-integral-scalar-comparison).

This is the existing canonical conjugate, not a second choice of comparison data. -/
abbrev sfCondensedOpenScalarComparison :
    D(CondensedRing.openImmersionLowerShriek Λ j) ⋙
        L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a U)) ⋙
        D(CondensedRing.openImmersionLowerShriek Λ' j) :=
  CondensedRing.derivedOpenImmersionShriekIso a j

/-- The specified conjugate of the canonical comparison is the pullback square.
Source: latest blueprint, `lem-zl-morphism-open-closed-reduction.proof.md`, Part 2.
(blueprint: def-zl-normalized-integral-scalar-comparison).

Proof: the comparison is defined by inverse conjugation, so this is the right-inverse
identity for the conjugation equivalence. -/
theorem sfCondensedOpenScalarComparison_normalization :
    conjugateIsoEquiv
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
      ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      (sfCondensedOpenScalarComparison a j) = CondensedRing.derivedComapUpperStarIso a j := by
  exact (conjugateIsoEquiv _ _).apply_symm_apply _

end WeilConjectures
