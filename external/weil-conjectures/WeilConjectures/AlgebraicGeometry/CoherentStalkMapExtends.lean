/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation

/-!
# A map of stalks of coherent modules comes from a map on a neighbourhood

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y4 (label
`lemma-map-stalks-local-map`), using Lemma 01XZ and Modules Lemma 01CP
(blueprint: lem-weil-pbc-coherent-stalk-map-extends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Finite generators and finite generators for their relations give a finite presentation.
This is the forward construction in Stacks Project, Tag 01XZ. -/
private theorem isFinitePresentation_of_coherent (X : Scheme.{u}) (F : X.Modules)
    (h : RingedSpace.IsCoherent X.toRingedSpace F) : F.IsFinitePresentation := by
  classical
  have (V : X.Opens) :
      HasSheafify ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) :
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) (W : CategoryTheory.Over V) :
      HasSheafify (((Opens.grothendieckTopology X).over V).over W)
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) (W : CategoryTheory.Over V) :
      (((Opens.grothendieckTopology X).over V).over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have : F.IsFiniteType := h.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hfp (i : q.I) : (F.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using h.2 (q.X i) n f
    exact Scheme.Modules.isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  have : F.IsFinitePresentation := by
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      F q.I q.X q.coversTop hfp
  infer_instance

/-- A homomorphism between stalks of coherent modules is induced by a morphism on
some open neighbourhood.

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y4
(label `lemma-map-stalks-local-map`), using Lemma 01XZ and Modules, Lemma 01CP
(blueprint: lem-weil-pbc-coherent-stalk-map-extends).

Proof:
1. The coherent source `G` is of finite type by definition (`pqf-def-coherent`).
   Locally choose finitely many generating sections, giving a surjection from a
   finite free module. Its kernel is of finite type by coherence (`pqf-def-coherent`).
   Shrink again and choose finitely many kernel generators. This gives a finite
   presentation of `G` (`def-weil-pbc-module-finite-type-presentation`), as in 01XZ.
2. Apply `lem-weil-pbc-stalk-internal-hom-finite-presentation` (01CP) to `G` and `F`.
   The canonical map from the stalk of internal Hom to Hom of stalks is an
   isomorphism, so `ψ` has a preimage germ. Internal-Hom sections are morphisms
   between the restricted modules (`def-pur-sheaf-hom`). Represent the germ by
   a morphism `φ` on an open neighbourhood `U` of `x` (`def-weil-pbc-module-stalk`).
3. The canonical map sends that representative germ to the induced stalk map `φ_x`
   (`lem-weil-pbc-stalk-internal-hom-finite-presentation`). Its value is `ψ` by
   construction. The restriction stalk isomorphisms identify this induced map
   with the displayed elementwise equality, yielding the required `U` and `φ`. -/
theorem exists_open_hom_of_coherent_stalk_map
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (x : X)
    (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G ⟶
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    ∃ (U : X.Opens) (hx : x ∈ U)
      (φ : (Scheme.Modules.restrictFunctor U.ι).obj G ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj F),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G,
        ψ m =
          ConcreteCategory.hom ((Scheme.Modules.restrictStalkNatIso U.ι
            ((⟨x, hx⟩ : (U : Scheme)))).hom.app F)
            ((RingedSpace.moduleStalkFunctor (U : Scheme).toRingedSpace ⟨x, hx⟩).map φ
              (ConcreteCategory.hom ((Scheme.Modules.restrictStalkNatIso U.ι
                ((⟨x, hx⟩ : (U : Scheme)))).inv.app G) m)) := by
  obtain ⟨_, _⟩ := hF
  have : G.IsFinitePresentation := isFinitePresentation_of_coherent X G hG
  obtain ⟨e, he⟩ := RingedSpace.exists_stalk_internalHom_linearEquiv_of_finitePresentation
    X.toRingedSpace G F x
  obtain ⟨t, ht⟩ := e.surjective ψ.hom
  obtain ⟨U, hx, φ, hφ⟩ := TopCat.Presheaf.exists_germ_eq (G.homObj F).val.presheaf t
  let φover : G.over U ⟶ F.over U := ⟨φ⟩
  let φ' := ((Scheme.Modules.overFunctorEquiv U).inv.app G) ≫
    (Scheme.Modules.overEquiv U).functor.map φover ≫
    ((Scheme.Modules.overFunctorEquiv U).hom.app F)
  refine ⟨U, hx, φ', ?_⟩
  intro m
  let y : (U : Scheme) := ⟨x, hx⟩
  let iso := Scheme.Modules.restrictStalkNatIso (Scheme.Opens.ι U) y
  obtain ⟨V, hyV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).obj G).presheaf
    (ConcreteCategory.hom (iso.inv.app G) m)
  have hv : x ∈ (Scheme.Opens.ι U) ''ᵁ V := by
    exact ⟨y, hyV, rfl⟩
  have hm : TopCat.Presheaf.germ G.presheaf ((Scheme.Opens.ι U) ''ᵁ V) x hv s = m := by
    have hh := ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app (Scheme.Opens.ι U) y G hyV) s
    change ConcreteCategory.hom (iso.hom.app G) _ = _ at hh
    erw [hs] at hh
    exact hh.symm.trans (ConcreteCategory.congr_hom (iso.inv_hom_id_app G) m)
  have hh := he U hx φ ((Scheme.Opens.ι U) ''ᵁ V) (homOfLE (by
    rintro z ⟨w, hw, rfl⟩
    exact w.property)) hv s
  rw [hφ, ht] at hh
  calc
    ψ m = TopCat.Presheaf.germ F.presheaf ((Scheme.Opens.ι U) ''ᵁ V) x hv
        ((φ.app (Opposite.op (Over.mk (homOfLE (by
          rintro z ⟨w, hw, rfl⟩
          exact w.property))))) s) := by
      rw [← hm]
      exact hh
    _ = _ := by
      erw [← hs]
      change _ = ConcreteCategory.hom (iso.hom.app F)
        ((TopCat.Presheaf.stalkFunctor Ab y).map
          ((PresheafOfModules.toPresheaf _).map φ'.val)
          (TopCat.Presheaf.germ
            ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).obj G).presheaf V y hyV s))
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      have hh' := ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app
          (Scheme.Opens.ι U) y F hyV) (φ'.val.app (Opposite.op V) s)
      exact hh'.symm

end AlgebraicGeometry
