/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.AlgebraicGeometry.StrictHenselianCohomologyLocallyZero
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCanonicalLeray

/-!
# Étale and Zariski cohomology over strictly henselian schemes

Source: literature/stacks-project/etale-cohomology.tex, Lemma 09AX
(blueprint: lem-weil-pbc-gabber-strict-henselian-zariski-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- The comparison from Zariski to étale cohomology is an isomorphism when all
local rings of the scheme are strictly henselian.
Source: literature/stacks-project/etale-cohomology.tex, Lemma 09AX
(blueprint: lem-weil-pbc-gabber-strict-henselian-zariski-comparison).
The functor `i` is the inclusion of the small Zariski site into the small étale
site. Its continuous direct image is `ε_* F`; `c` is the pullback followed by
its counit, and is the identity in degree zero.
`hi_inclusion` identifies the underlying open subschemes. The three clauses of `hfstar`
are the defining characterization of cohomology pullback in
`CategoryTheory.siteCohomology_pullback`: naturality, compatibility with the connecting
homomorphisms of short exact sequences, and evaluation of the adjunction unit in degree
zero. Thus `fstar` is the canonical pullback, and `hc` fixes the comparison itself.

Proof:
1. The inclusion defines the Zariski-to-étale morphism of sites. The defining
   characterization of pullback and `hc` identify `c` with its Leray edge map.
2. Higher direct images are the sheafifications of the presheaves
   `U ↦ H^q(U, F)` by the higher-direct-image sheafification theorem.
3. The colimit over Zariski neighborhoods of a point is cohomology over the spectrum
   of its local ring. Strict henselian étale acyclicity makes it zero in positive
   degree, so each positive-degree class restricts to zero on some neighborhood.
4. Hence the morphism from the cohomology presheaf to zero is locally bijective.
   Sheafification makes it an isomorphism, and all positive higher direct images vanish.
5. Degenerate Leray makes the canonical edge map invertible in every degree.
   Substitute the defining equality `hc` to obtain invertibility of `c`. -/
theorem strictHenselian_zariski_etale_comparison
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
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
    (c : ∀ q : ℕ,
      Sheaf.H'
          ((i.sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F)
          q ⊤ ⟶
        Sheaf.H' F q (i.obj ⊤))
    (hc : ∀ q : ℕ, c q =
      fstar q ⊤
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj ⊤))) :
    ∀ q : ℕ, IsIso (c q) := by
  have hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q) := by
    intro q hq
    constructor
    intro U s t _ x hx
    obtain ⟨V, hVU, hxV, hzero⟩ := strictHenselian_cohomology_locally_zero
      hX i hi_inclusion F q hq U.unop (s - t) x hx
    refine ⟨V, homOfLE hVU, ?_, hxV⟩
    change (i.op ⋙ Sheaf.cohomologyPresheaf F q).map (homOfLE hVU).op s =
      (i.op ⋙ Sheaf.cohomologyPresheaf F q).map (homOfLE hVU).op t
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  intro q
  rw [hc q]
  exact zariski_etale_canonical_leray i hi_inclusion hi fstar hfstar F hvan q ⊤
