/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # The image filtration on etale hypercohomology

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-hypercohomology-filtration-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Membership in the image filtration from complexes supported in degrees at least `q`.
A map from such a complex factors through the stupid truncation of `K` at `q`, so this
is the usual image filtration of the termwise hypercohomology spectral sequence.
Source: Stacks Project, Tag 015J.
(blueprint: lem-weil-pbc-etale-hypercohomology-filtration-zero). -/
def InEtaleHypercohomologyFiltration (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (p q : ℤ) (x : (cohomology AddCommGrpCat.{u + 1} X p).obj
      (DerivedCategory.Q.obj K)) : Prop :=
  ∃ (T : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
    (∀ n : ℤ, n < q → IsZero (T.X n)) ∧
    ∃ (f : T ⟶ K) (y : (cohomology AddCommGrpCat.{u + 1} X p).obj
      (DerivedCategory.Q.obj T)),
      (cohomology AddCommGrpCat.{u + 1} X p).map (DerivedCategory.Q.map f) y = x

/-- The image filtration is zero above the total cohomological degree.
Source: Stacks Project, Tag 015J, the first spectral sequence and its vanishing region.

Proof: Choose the witness `T`, map `f`, and class `y`. Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective` replaces `T`
by a quasi-isomorphic complex `J` of injectives with the same lower bound `q`.
A bounded-below complex of injectives is K-injective. Global sections applied termwise
to `J` still vanishes below `q`. The isomorphism `rightDerivedFunctorObjQIso`, together
with the quasi-isomorphism from `T` to `J`, identifies derived global sections of `T`
with this termwise complex. Its homology in degree `p < q` is zero. Consequently
`y = 0`, and additivity of the map induced by `f` gives `x = 0`.
(blueprint: lem-weil-pbc-etale-hypercohomology-filtration-zero). -/
theorem eq_zero_of_inEtaleHypercohomologyFiltration
    (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (p q : ℤ) (hpq : p < q)
    (x : (cohomology AddCommGrpCat.{u + 1} X p).obj (DerivedCategory.Q.obj K))
    (hx : InEtaleHypercohomologyFiltration X K p q x) : x = 0 := by
  obtain ⟨T, hT, f, y, rfl⟩ := hx
  let : T.IsStrictlyGE q := (T.isStrictlyGE_iff q).2 hT
  obtain ⟨J, i, hi, hJ, hJq⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T q
  let : QuasiIso i := hi
  let : ∀ n : ℤ, Injective (J.X n) := hJ
  let : J.IsStrictlyGE q := hJq
  let : J.IsKInjective := CochainComplex.isKInjective_of_injective J q
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let M : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  have hM : M.IsStrictlyGE q := by
    apply (M.isStrictlyGE_iff q).2
    intro n hn
    exact Γ.map_isZero (J.isZero_of_isStrictlyGE q n hn)
  let : M.IsStrictlyGE q := hM
  let e := (Γ.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map i))) ≪≫
    Γ.rightDerivedFunctorObjQIso J
  have hz : IsZero ((cohomology AddCommGrpCat.{u + 1} X p).obj
      (DerivedCategory.Q.obj T)) := by
    exact (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj M) q p hpq).of_iso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).mapIso e)
  have hy : y = 0 := by
    let := AddCommGrpCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _
  rw [hy, map_zero]


end AlgebraicGeometry.Etale
