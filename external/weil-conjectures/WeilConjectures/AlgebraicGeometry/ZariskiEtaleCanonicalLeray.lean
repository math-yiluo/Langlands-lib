/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolution
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionMap
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionHomologyDataExists
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Canonical Leray comparison for the Zariski-to-étale morphism

Source: Stacks Project, Cohomology on Sites, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-canonical-leray)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- If zero on every positive object-cohomology presheaf is locally injective,
the canonical pullback followed by the counit is an isomorphism on every open.
There is no strict-henselian hypothesis here.

Source: literature/stacks-project/sites-cohomology.tex, Tags 072W and 0733(1);
etale-cohomology.tex, Tag 09AX, proof, first, second and last sentences.
(blueprint: lem-weil-pbc-zariski-etale-canonical-leray)

Proof: For the usual inclusion the inverse image on abelian sheaves is exact.
For the functor `i` specified here, first restrict to the etale object `i(⊤)`.
Its underlying scheme is `X`, and `hi_inclusion` identifies every `i(U)` with its
open restriction. Direct image along `i` is restriction to that etale object
followed by the usual Zariski direct image; its left adjoint is the usual exact
inverse image followed by exact etale extension by zero. Hence that abelian
left adjoint is exact as well. Local injectivity of zero says any two sections
locally coincide. In
particular every section is locally zero. Transfer this condition along the natural
resolution description of Ext cohomology, using a coefficient universe supporting
sheafification; this transfer is necessary because the Ext universe is arbitrary.
For the morphism of this cohomology presheaf to zero, local surjectivity is automatic
and local injectivity is the hypothesis. Sheafification therefore makes it an
isomorphism to the zero sheaf. By 072W this sheafification is its `q`-th right
derived direct image, so every positive derived direct image of `F` is zero.
Choose an injective resolution of `F`.
The direct image of each injective is injective because its left adjoint is exact.
The pushed-forward resolution has no positive homology by the preceding vanishing,
and degree-zero homology is the direct image of `F` by left exactness.
It is therefore an injective resolution of that direct image. Evaluating it on
an open `V` gives the same complex as evaluating the original resolution on `i(V)`.
The resulting cohomology comparison is an isomorphism. To identify this comparison,
its degree-zero map is the unit followed by the counit, and the triangle identity
makes this the identity. Resolution comparison maps give naturality and compatibility
with connecting homomorphisms. The uniqueness characterization of cohomology pullback
(the three clauses `hfstar`) then identifies it with `fstar` followed by the counit.
This proves invertibility of the specified composite, including degree zero. -/
theorem zariski_etale_canonical_leray
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (fstar : ∀ (p : ℕ) (V : X.Opens)
      (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}),
      Sheaf.H' A p V ⟶
        Sheaf.H' ((sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj A)
          p (i.obj V))
    (hfstar : (∀ (p : ℕ) (V : X.Opens) (A A' : Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u + 1}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p).map φ).app
          (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).map
              ((sheafPullback i AddCommGrpCat.{u + 1}
                (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map φ)).app
                  (op (i.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}))
        (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)).ShortExact)
        (p : ℕ) (V : X.Opens) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : X.Opens) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
        (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (i.obj V))).hom
            (((toSheafify X.smallEtaleTopology
              (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (i.obj V)))) =
          (((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app A).hom.app
              (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify (Opens.grothendieckTopology X.carrier)
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V))))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    ∀ (q : ℕ) (V : X.Opens), IsIso
      (fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))) := by
  let := hi
  obtain ⟨hlex, hquasi⟩ :=
    zariski_etale_pushed_resolution i hi_inclusion hi F hvan
  let := hlex
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let : G.PreservesInjectiveObjects :=
    (sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology).preservesInjectiveObjects_of_preservesFiniteLimits
  let I := InjectiveResolution.of F
  let a := (HomologicalComplex.singleMapHomologicalComplex G
      (ComplexShape.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  let R : InjectiveResolution (G.obj F) :=
    { cocomplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective n := G.injective_obj_of_injective (I.injective n)
      ι := a
      quasiIso := hquasi I }
  have he : R.ι.f 0 ≫ HomologicalComplex.Hom.f (𝟙 R.cocomplex) 0 = G.map (I.ι.f 0) := by
    simp [R, a, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  intro q V
  obtain ⟨e₁, e₂, hcomp⟩ :=
    zariski_etale_resolution_homology_data_exists i hi fstar hfstar F I R (𝟙 R.cocomplex) he q V
  let E := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
  let b := HomologicalComplex.homologyMap
    ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map (𝟙 R.cocomplex)) q
  have hb : IsIso b := inferInstance
  have hbij : Function.Bijective b.hom :=
    (ConcreteCategory.isIso_iff_bijective b).mp hb
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply e₁.injective
    apply hbij.1
    rw [← hcomp x, ← hcomp y, h]
  · intro y
    obtain ⟨z, hz⟩ := hbij.2 (e₂ y)
    obtain ⟨x, rfl⟩ := e₁.surjective z
    refine ⟨x, e₂.injective ?_⟩
    rw [hcomp x]
    exact hz
