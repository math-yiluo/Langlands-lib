/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.Reductions
import WeilConjectures.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant
import WeilConjectures.AlgebraicGeometry.Curve.SepClosedComparison
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules

/-!
# Invariance of the cohomology of a proper curve under extension of the base field

Let `k ⊆ k'` be separably closed fields, `C` a proper curve over `k` (a proper `k`-scheme of
dimension at most one), and `F` a torsion étale sheaf on `C`. Then the pullback map
`Hᵠ(C, F) ⟶ Hᵠ(C_{k'}, F|)` is bijective in every degree. This is the input of the proof of
proper base change for the projective line: there the stalk of the exchange morphism at a
geometric point is such a pullback map, between the projective lines over the residue fields
of two strict henselisations.

The case of algebraically closed fields is the real content; it is reached from the curve
calculations by dévissage. The separably closed case is
deduced from it, the extensions `k̄/k` and `k̄'/k'` being purely inseparable, so that the
corresponding base changes are universal homeomorphisms, which do not change étale cohomology.

The base change `C_{k'}` is given by an arbitrary cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

and the coefficient sheaf is a torsion sheaf of `Λ`-modules
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`, torsion of the geometric stalks); its cohomology
is that of the underlying sheaf of abelian groups.

## Main statements

- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`: the algebraically closed
  case.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`: the
  passage from algebraically closed to separably closed fields.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`: the separably closed
  case.

## References

- Stacks Project, Lemma 59.80.4 (invariance of the cohomology of a proper curve),
  <https://stacks.math.columbia.edu/tag/0A5E>
- Stacks Project, Theorem 59.83.1, <https://stacks.math.columbia.edu/tag/03SC>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Invariance of the cohomology of a proper curve under extension of algebraically closed
fields.** Let `k ⊆ k'` be algebraically closed fields, `C` a proper curve over `k` and `F` a
torsion étale sheaf of `Λ`-modules on `C`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian
sheaves is bijective for every `q`. This is the assertion `C₇(C, F)` of the eight curve
calculations; it is proved by reducing to reduced curves and constructible `𝐅_r`-coefficients,
splitting off the zero-dimensional components, localising to a dense open, passing to the
normalisation and to the smooth constant case of the curve calculations.
(blueprint: theorem-cohomology-curves--7)
-/
@[stacks 0A5E]
theorem bijective_cohomologyMap_of_isAlgClosed {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  refine bijective_cohomologyMap_of_forall_isReduced Λ ?_ f k' h F q
  intro X X' g _ _ _ K _ _ ι g' ι' h r _ G _ q
  exact algebraicallyClosedCohomologyInvariant g K h G q

/-- **Passage between separably closed fields.** Let `k ⊆ k'` be separably closed fields, `C`
a proper curve over `k` and `F` a torsion étale sheaf of `Λ`-modules on `C`. If the cohomology
of proper curves is invariant under extensions of algebraically closed fields (the hypothesis
`H`, which is `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`), then for
every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective for every `q`.

Choose compatible algebraic closures `k̄ ⊆ k̄'`. As `k` and `k'` are separably closed, `k̄/k`
and `k̄'/k'` are purely inseparable, so the base changes `C_{k̄} ⟶ C` and `C_{k̄'} ⟶ C'` are
universal homeomorphisms and are bijective on étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap_bijective`). The square of pullback maps between the
four cohomology groups commutes, and its bottom row `Hᵠ(C_{k̄}) ⟶ Hᵠ(C_{k̄'})` is bijective by
`H`.
(blueprint: lemma-extension-separably-closed-ground-field--1)
-/
theorem bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed
    (H : ∀ {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
      {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
      (_ : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsTorsionModuleSheaf F] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  obtain ⟨K, hK, hKa, K', hK', hK'a, D, D', b, b', j, a, p, p',
    hb, hbp, hs, hp, hp', hcomm⟩ := sepClosed_geometric_comparison f h
  let A := (sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj F
  obtain ⟨e⟩ := Etale.pullback_forget_modules_iso Λ p F
  let eH := (Sheaf.functorH D.smallEtaleTopology q).mapIso e
  let eaH := (Sheaf.functorH D'.smallEtaleTopology q).mapIso
    ((Etale.upperStar AddCommGrpCat.{u + 1} a).mapIso e)
  have hbottom : Function.Bijective
      (Etale.cohomologyMap a ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q) := by
    apply (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso eH.hom)).mp
    have heq : Etale.cohomologyMap a
        ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q ∘ eH.hom =
        eaH.hom ∘ Etale.cohomologyMap a
          ((sheafCompose D.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q := by
      funext x
      exact Etale.cohomologyMap_map a q e.hom x
    rw [heq]
    exact (ConcreteCategory.bijective_of_isIso eaH.hom).comp (H b hs G q)
  let e₁ := (Etale.upperStarComp AddCommGrpCat.{u + 1} p' ι').app A
  let e₂ := (Etale.upperStarComp AddCommGrpCat.{u + 1} a p (p' ≫ ι') hcomm).app A
  let e₁H := (Sheaf.functorH D'.smallEtaleTopology q).mapIso e₁
  let e₂H := (Sheaf.functorH D'.smallEtaleTopology q).mapIso e₂
  let g := e₁H.inv ∘ Etale.cohomologyMap p'
    ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj A) q
  have hg : Function.Bijective g :=
    (ConcreteCategory.bijective_of_isIso e₁H.inv).comp
      (Etale.cohomologyMap_bijective p' _ q)
  have hcomp : Function.Bijective (g ∘ Etale.cohomologyMap ι' A q) := by
    have heq : g ∘ Etale.cohomologyMap ι' A q =
        e₂H.inv ∘ Etale.cohomologyMap a
          ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q ∘
            Etale.cohomologyMap p A q := by
      funext x
      have ht : Etale.cohomologyMap p'
          ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj A) q
            (Etale.cohomologyMap ι' A q x) =
          Sheaf.H.map e₁.hom q (Etale.cohomologyMap (p' ≫ ι') A q x) :=
        (Etale.cohomologyPullbackFunctorial p' ι' A q).2.1 x
      have hb : Etale.cohomologyMap a
          ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q
            (Etale.cohomologyMap p A q x) =
          Sheaf.H.map e₂.hom q (Etale.cohomologyMap (p' ≫ ι') A q x) := by
        have hfun (m : D' ⟶ C) (hm : m = a ≫ p) :
            Etale.cohomologyMap a ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q
                (Etale.cohomologyMap p A q x) =
              Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} a p m hm).hom.app A)
                q (Etale.cohomologyMap m A q x) := by
          subst m
          exact (Etale.cohomologyPullbackFunctorial a p A q).2.1 x
        exact hfun _ hcomm
      change Sheaf.H.map e₁.inv q
          (Etale.cohomologyMap p'
            ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj A) q
              (Etale.cohomologyMap ι' A q x)) =
        Sheaf.H.map e₂.inv q
          (Etale.cohomologyMap a ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj A) q
            (Etale.cohomologyMap p A q x))
      rw [ht, hb]
      simp only [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
    rw [heq]
    exact (ConcreteCategory.bijective_of_isIso e₂H.inv).comp
      (hbottom.comp (Etale.cohomologyMap_bijective p A q))
  exact (Function.Bijective.of_comp_iff' hg _).mp hcomp

/-- **Invariance of the cohomology of a proper curve under extension of separably closed
fields.** Let `k ⊆ k'` be separably closed fields, `C` a proper curve over `k` (a proper
`k`-scheme of dimension at most one) and `F` a torsion étale sheaf of `Λ`-modules on `C`. For
every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian
sheaves is bijective for every `q`: the algebraically closed case
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`, transported to separably
closed fields by
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`.
(blueprint: lemma-extension-separably-closed-ground-field--1)
-/
@[stacks 0A5E]
theorem bijective_cohomologyMap_of_isSepClosed {k k' : Type u} [Field k] [IsSepClosed k]
    [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed Λ
    (fun f _ _ _ _ _ h F _ q ↦ bijective_cohomologyMap_of_isAlgClosed Λ f h F q) f h F q

end AlgebraicGeometry.IsCurve
