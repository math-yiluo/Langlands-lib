/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.AlgebraicGeometry.GlobalHomShiftedHypercohomology

/-! # Shifted Hom as cohomology of restricted global derived Hom
Source: Stacks Project, Cohomology on Sites, Tag 08JA; Cohomology, Tag 0B6A.
(blueprint: lem-sc-restricted-global-hom-shifted-equiv).
-/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def restrictionCohomologyEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} B)]
    (r : A →+* B) (k : ℤ) (K : DerivedCategory (ModuleCat.{u} B)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
      ((ModuleCat.restrictScalars.{u} r).mapDerivedCategory.obj K)) ≃+
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) k).obj K) :=
  let i :=
    ((ModuleCat.restrictScalars.{u} r).mapDerivedCategoryHomologyFunctorIso k).symm.app K
  i.toLinearEquiv.toAddEquiv

private theorem restrictionCohomologyEquiv_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} B)]
    (r : A →+* B) (k : ℤ) {K L : DerivedCategory (ModuleCat.{u} B)} (q : K ⟶ L)
    (x : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
      ((ModuleCat.restrictScalars.{u} r).mapDerivedCategory.obj K))) :
    restrictionCohomologyEquiv r k L
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map
        ((ModuleCat.restrictScalars.{u} r).mapDerivedCategory.map q)) x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) k).map q)
        (restrictionCohomologyEquiv r k K x) := by
  have h :=
    ((ModuleCat.restrictScalars.{u} r).mapDerivedCategoryHomologyFunctorIso k).inv.naturality q
  exact congrArg (fun z ↦ z x) h


/-- The shifted-Hom/cohomology identification, including the action of a morphism
in the second entry. Exact scalar restriction changes the ring action, not the
underlying cohomology group.
Source: Stacks Project, Cohomology on Sites, Tag 08JA; Cohomology, Tag 0B6A.
(blueprint: lem-sc-restricted-global-hom-shifted-equiv).

Proof: Choose a K-flat representative of P and a K-injective representative of Q.
Their sheaf Hom complex represents internal RHom; its global sections compute global
RHom. Degree n-m cocycles modulo boundaries are derived morphisms P[m] to Q[n]: the
usual shift comparison carries the Hom-complex differential and its signs to the
chain-map equation. Localization into a K-injective target identifies homotopy
classes with derived morphisms. This is the shifted version of rhom_global_sections.
Evaluation at the unit identifies sheaf Hom global sections with the ordinary Hom
complex. Restriction of scalars is exact and leaves the underlying group unchanged,
so it commutes with cohomology. Transport these identifications through the right-
derived resolution isos, giving e. Postcomposition with q commutes with localization,
shift and each resolution comparison, giving the displayed naturality equation.
All integers are allowed; no boundedness or quasi-coherence hypothesis is needed. -/
theorem restrictedGlobalHom_shiftedHom_equiv
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ e : ∀ (P Q : schemeDerivedCategory X) (m n : ℤ),
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
          ((schemeGlobalScalarRestriction f).obj
            ((schemeGlobalDerivedHom X).obj (op P, Q)))) ≃+ (P⟦m⟧ ⟶ Q⟦n⟧),
      ∀ (P Q Q' : schemeDerivedCategory X) (m n : ℤ) (q : Q ⟶ Q')
        (x : ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
            ((schemeGlobalScalarRestriction f).obj
              ((schemeGlobalDerivedHom X).obj (op P, Q))))),
        e P Q' m n
          (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).map
              ((schemeGlobalScalarRestriction f).map
                ((schemeGlobalDerivedHom X).map ((𝟙 P).op, q)))) x) =
          e P Q m n x ≫ q⟦n⟧' := by
  obtain ⟨c, hc⟩ := schemeGlobalHom_shiftedHypercohomology_equiv.{u, w, wA} X
  obtain ⟨d, hd⟩ := rhom_global_sections.{u, w} (_root_.Opens.grothendieckTopology X)
    X.sheaf
  let a (P Q : schemeDerivedCategory X) (m n : ℤ) :=
    restrictionCohomologyEquiv f.appTop.hom (n - m)
      ((schemeGlobalDerivedHom X).obj (op P, Q))
  refine ⟨fun P Q m n ↦ (a P Q m n).trans
    ((c P Q m n).trans (d (op (P⟦m⟧), Q⟦n⟧))), ?_⟩
  intro P Q Q' m n q x
  have ha := restrictionCohomologyEquiv_naturality f.appTop.hom (n - m)
    ((schemeGlobalDerivedHom X).map
      (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, q)) x
  exact (congrArg (fun z ↦ d (op (P⟦m⟧), Q'⟦n⟧) (c P Q' m n z)) ha).trans
    ((congrArg (d (op (P⟦m⟧), Q'⟦n⟧))
      (hc P Q Q' m n q (a P Q m n x))).trans
        (by
          have h := hd (op (P⟦m⟧), Q⟦n⟧) (op (P⟦m⟧), Q'⟦n⟧)
            ((𝟙 (P⟦m⟧)).op, (shiftFunctor (schemeDerivedCategory X) n).map q)
            (c P Q m n (a P Q m n x))
          dsimp only at h
          simp only [Quiver.Hom.unop_op, Category.id_comp] at h
          simp only [AddEquiv.trans_apply]
          convert h using 1))

end AlgebraicGeometry
