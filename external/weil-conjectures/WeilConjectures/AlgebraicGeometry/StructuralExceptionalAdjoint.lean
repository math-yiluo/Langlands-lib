/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-! # Constructible compact-support exceptional adjoint

Source: Bhatt--Scholze, Lemmas 6.7.7 and 6.7.19, Remark 6.8.15 and Proposition 6.8.14
(blueprint: lem-per-condensed-structural-exceptional-adjoint).

For a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the blueprint lemma asserts
that the bounded constructible compact-support functor `Rf_!` is computed by `i_! ⋙ Rp_*` for
every compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, and that it has a right adjoint `Rf^!` on
bounded constructible complexes. The adjunction is
`ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`
(`Rf_! = boundedConstructibleLowerShriek ⊣ Rf^! = boundedConstructibleUpperShriek`); this file
supplies the compactification-independence clause, comparing `Rf_!` on `Dᵇc` with the derived
lower shriek `Rf_!(c)⟦ℚ̲̄_ℓ⟧` on the ambient derived categories for an arbitrary `c`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The bounded constructible compact-support functor `Rf_!`, the left adjoint in
`boundedConstructibleUpperShriekAdjunction ℓ f : Rf_! ⊣ Rf^!`, is independent of the
compactification: for every compactification `c` of `f`, it is the restriction to `Dᵇc` of the
derived lower shriek `Rf_!(c)⟦ℚ̲̄_ℓ⟧ = i_! ⋙ Rp_*` attached to `c`.

Source: Bhatt--Scholze, Definition 6.7.6, Lemmas 6.7.7 and 6.7.19, Remark 6.8.15 and
Proposition 6.8.14; (blueprint: lem-per-condensed-structural-exceptional-adjoint).

Construction: the independence isomorphism
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` from the chosen
compactification to `c`, followed by the comparison
`boundedConstructibleLowerShriekOfCompactificationCompatibility` of `i_! ⋙ Rp_*` on `Dᵇc`
with the ambient derived lower shriek. -/
noncomputable def boundedConstructibleLowerShriekCompatibilityOfCompactification
    {f : X ⟶ Y} (c : Compactification f.left) :
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
        (compactificationOverField f) c) _ ≪≫
    boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c

end AlgebraicGeometry.ProEtale.CondensedRing
