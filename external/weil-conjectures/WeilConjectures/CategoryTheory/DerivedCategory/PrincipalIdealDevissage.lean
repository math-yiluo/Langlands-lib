/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.PID
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber

/-!
# Dévissage of `Dᵇ_fg(R)` over a principal ideal domain

Let `R` be a principal ideal domain (for instance a discrete valuation ring or a field). A
triangulated subcategory of `D(R)`, closed under isomorphisms, which contains `R` placed in
degree `0` contains every bounded complex with finitely generated cohomology modules
(`DerivedCategory.prop_of_boundedFiniteCohomology`): it contains the free modules of finite
rank (direct sums of copies of `R`), hence every finitely generated module `M`, which is the
cokernel of an injective map of free modules of finite rank (submodules of free modules of
finite rank are free of finite rank), and one concludes by the dévissage of bounded complexes
along their truncations (`DerivedCategory.prop_of_bounded`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace DerivedCategory

variable {R : Type (u + 1)} [CommRing R]
  (P : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R))) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

/-- Modules whose image in degree `0` satisfy `P`. -/
private abbrev singleProp : ObjectProperty (ModuleCat.{u + 1} R) :=
  fun M ↦ P ((singleFunctor (ModuleCat.{u + 1} R) 0).obj M)

omit [P.IsTriangulated] in
private lemma singleProp_of_iso {M N : ModuleCat.{u + 1} R} (e : M ≅ N) (h : singleProp P M) :
    singleProp P N :=
  P.prop_of_iso ((singleFunctor _ 0).mapIso e) h

private lemma singleProp_biprod {M N : ModuleCat.{u + 1} R} (hM : singleProp P M)
    (hN : singleProp P N) : singleProp P (M ⊞ N) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (singleFunctor (ModuleCat.{u + 1} R) 0)
  exact P.prop_of_iso ((singleFunctor _ 0).mapBiprod M N).symm
    (P.ext_of_isTriangulatedClosed₂ _ (binaryBiproductTriangle_distinguished _ _) hM hN)

private lemma singleProp_pi (hR : singleProp P (ModuleCat.of R R)) (n : ℕ) :
    singleProp P (ModuleCat.of R (Fin n → R)) := by
  induction n with
  | zero =>
    refine P.prop_of_isZero (Functor.map_isZero _ ?_)
    rw [ModuleCat.isZero_iff_subsingleton]
    infer_instance
  | succ n ih =>
    refine singleProp_of_iso P ?_ (singleProp_biprod P hR ih)
    exact ModuleCat.biprodIsoProd _ _ ≪≫
      (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R)).toModuleIso

variable [IsDomain R] [IsPrincipalIdealRing R]

private lemma singleProp_of_finite (hR : singleProp P (ModuleCat.of R R)) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] : singleProp P M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : Module.Finite R (LinearMap.ker f) := Module.IsNoetherian.finite R _
  have hK : singleProp P (ModuleCat.of R (LinearMap.ker f)) :=
    singleProp_of_iso P (Module.finBasis R (LinearMap.ker f)).equivFun.toModuleIso.symm
      (singleProp_pi P hR _)
  exact P.ext_of_isTriangulatedClosed₃ _ hS.singleTriangle_distinguished hK
    (singleProp_pi P hR n)

/-- Over a principal ideal domain `R`, a triangulated subcategory of `D(R)`, closed under
isomorphisms, which contains `R` placed in degree `0` contains `Dᵇ_fg(R)`, the bounded complexes
with finitely generated cohomology modules. -/
theorem prop_of_boundedFiniteCohomology
    (hR : P ((singleFunctor (ModuleCat.{u + 1} R) 0).obj (ModuleCat.of R R)))
    {K : DerivedCategory (ModuleCat.{u + 1} R)} (hK : boundedFiniteCohomology R K) : P K := by
  let Q : ObjectProperty (ModuleCat.{u + 1} R) := fun M ↦ Module.Finite R M
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e (h : Module.Finite R _) ↦
    Module.Finite.equiv e.toLinearEquiv⟩
  exact prop_of_bounded P Q (fun M (_ : Module.Finite R M) ↦ singleProp_of_finite P hR M) K
    hK.1 hK.2

section Triangulated

variable {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R]

private lemma moduleFinite_of_exact {M N P : Type (u + 1)} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) [Module.Finite R M] [Module.Finite R P] : Module.Finite R N :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (fun y ↦ by rw [← h y]; simp [Subtype.ext_iff]) g.surjective_rangeRestrict

instance : (boundedFiniteCohomology R).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨TStructure.t.bounded.prop_of_isZero (isZero_zero _),
    fun n ↦ by
      have := (ModuleCat.isZero_iff_subsingleton.1
        ((homologyFunctor (ModuleCat.{u + 1} R) n).map_isZero (isZero_zero _)))
      infer_instance⟩⟩
  isStableUnderShiftBy a := ⟨fun X hX ↦ ⟨TStructure.t.bounded.le_shift a X hX.1, fun n ↦ by
    have := hX.2 (a + n)
    exact Module.Finite.equiv (M := (homologyFunctor (ModuleCat.{u + 1} R) (a + n)).obj X)
      (((homologyFunctor (ModuleCat.{u + 1} R) 0).shiftIso a n (a + n) rfl).app
        X).symm.toLinearEquiv⟩⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    ⟨TStructure.t.bounded.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1, fun n ↦ by
      have := h₁.2 n
      have := h₃.2 n
      exact moduleFinite_of_exact (f := ((homologyFunctor (ModuleCat.{u + 1} R) n).map T.mor₁).hom)
        (g := ((homologyFunctor (ModuleCat.{u + 1} R) n).map T.mor₂).hom)
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
          (HomologySequence.exact₂ T hT n))⟩

end Triangulated

/-- A finitely generated module placed in degree `0` lies in `Dᵇ_fg`. -/
lemma boundedFiniteCohomology_singleFunctor {R : Type (u + 1)} [CommRing R]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    boundedFiniteCohomology R ((singleFunctor (ModuleCat.{u + 1} R) 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact Module.Finite.equiv (M := M)
      ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} R) 0).app M).symm.toLinearEquiv
  · have : Subsingleton ((homologyFunctor (ModuleCat.{u + 1} R) n).obj
        ((singleFunctor (ModuleCat.{u + 1} R) 0).obj M)) := by
      rw [← ModuleCat.isZero_iff_subsingleton]
      rcases lt_or_gt_of_ne hn with h | h
      · exact isZero_of_isGE _ 0 n h
      · exact isZero_of_isLE _ 0 n h
    infer_instance

end DerivedCategory
