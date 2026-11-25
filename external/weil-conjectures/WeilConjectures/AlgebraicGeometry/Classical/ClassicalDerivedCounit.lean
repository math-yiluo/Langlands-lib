/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The counit on bounded-below classical objects

Source: the Weil conjectures blueprint, main-20261015,
`sec-proetale-coefficients/sk-cor-pe-classical-derived/`
(blueprint: lem-pe-classical-derived-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private noncomputable def classicalHomologyIso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _))).inverse ⋙
        (@DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _) q) := by
  let B := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let H := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let Q := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory B _ _ (HasDerivedCategory.standard B))
  let eQ : DerivedCategory.Q ⋙ e.inverse ≅ Q :=
    Functor.associator Q e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft Q e.unitIso.symm ≪≫ Q.rightUnitor
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) B).preimageIso
      (DerivedCategory.homologyFunctorFactors B q ≪≫
        (@DerivedCategory.homologyFunctorFactors B _ _
          (HasDerivedCategory.standard B) q).symm ≪≫
        Functor.isoWhiskerRight eQ.symm H ≪≫ Functor.associator _ _ _)

private theorem classicalModule_of_iso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
  intro I _ _ P
  have hmap := continuityMap_natural P e.hom.hom
  have : IsIso (continuityMap P F.obj) := hF P
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op
      ((sheafToPresheaf _ _).mapIso e)).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [hmap]
  infer_instance

/-- The derived comparison counit is invertible on bounded-below classical objects.
Source: the truncation induction and bounded-below tail argument in
`det-pe-classical-derived-equivalence` (blueprint: lem-pe-classical-derived-counit).
Proof: write F for exact comparison inverse image and R for derived direct
image. Give R the shift structure adjoint to that of F, so the counit is a
transformation of triangulated functors. A classical module G is F(M) for
an etale module M. Exactness identifies each shifted single complex G[-q]
with F(M[-q]); the triangle identity and the invertible unit show that its
counit is invertible. For a bounded classical K with cohomology in [a,b],
start with the zero truncation below a and induct on upper truncations.
Their distinguished triangles have third term H^q(K)[-q]. Counit naturality
and shift compatibility give morphisms of these triangles; the long exact
cohomology sequence and five lemma prove invertibility on the middle term.
This proves the bounded case. For arbitrary bounded-below classical K and
fixed m, let T be its truncation at N >= m. The truncation map T -> K is a
cohomology isomorphism through N and monic in N+1. Right-derived truncation
comparison shows that R(T) -> R(K) is an isomorphism on H^m; exactness of F
preserves this. The naturality square for the counit now has three
invertible sides on H^m, hence its fourth side is invertible. Vary m and
use cohomology detection of isomorphisms. No upper bound on K is required. -/
theorem classicalDerivedCounit (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (hunit : ∀ L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit.app L)) :
    ∀ K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
      ClassicalPlus X Λ K →
        IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.counit.app K) := by
  classical
  let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let B := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let F₀ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let R₀ := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
  let F := F₀.mapDerivedCategoryPlus
  let R := R₀.rightDerivedFunctorPlus
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  let : IsIso adj.unit := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ adj.unit (fun L ↦ hunit L)
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  let P : ObjectProperty B := IsClassicalModuleFor X Λ
  let : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ classicalModule_of_iso X Λ e h⟩
  have hsingle : ∀ G, P G →
      IsIso (adj.counit.app ((DerivedCategory.Plus.singleFunctor B 0).obj G)) := by
    intro G hG
    obtain ⟨E, hE, hEq, _, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 Λ
    let : E.IsEquivalence := hEq
    let M := E.asEquivalence.inverse.obj ⟨G, hG⟩
    let eG : F₀.obj M ≅ G :=
      (eqToIso (congrArg (fun T ↦ T.obj M) hE)).symm ≪≫
        P.ι.mapIso (E.asEquivalence.counitIso.app ⟨G, hG⟩)
    let e : F.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
        (DerivedCategory.Plus.singleFunctor B 0).obj G :=
      (F₀.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
        (DerivedCategory.Plus.singleFunctor B 0).mapIso eG
    exact adj.isIso_counit_app_of_iso e.symm
  intro K hK
  refine DerivedCategory.Plus.isIso_app_of_forall_homology adj.counit P hsingle ?_ ?_ K ?_
  · intro T n hn q hq
    have hz := R₀.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE T n hq
    exact (F₀.map_isZero hz).of_iso
      ((F₀.mapDerivedCategoryPlusHomologyFunctorIso q).symm.app (R.obj T))
  · intro T n hn q hq
    exact DerivedCategory.isZero_of_isGE (DerivedCategory.Plus.ι.obj T) n q hq
  · intro q
    apply classicalModule_of_iso X Λ ((classicalHomologyIso X Λ q).app _).symm
    exact hK q

end AlgebraicGeometry.ProEtale

end
