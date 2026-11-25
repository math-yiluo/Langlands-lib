/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology

/-!
# The cycle comparison for direct image before deriving

Source: Stacks Project, Cohomology, Tag 01F4 (2), construction on complexes
(blueprint: lem-pc-leray-complex-cocycle-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- A natural map of section functors induces a homology map when the source
forgetful functor preserves cokernels and the target functor preserves kernels. -/
private theorem homologyComparisonOfNatTrans
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    (G : C₀ ⥤ C₁) (D : C₀ ⥤ C₂) (U : C₁ ⥤ C₃) (T : C₂ ⥤ C₃)
    [G.Additive] [D.Additive] [U.Additive] [T.Additive]
    [PreservesFiniteColimits U] [PreservesFiniteLimits T]
    (t : G ⋙ U ⟶ D ⋙ T) (q : ℕ) :
    let A := G.mapHomologicalComplex (ComplexShape.up ℕ)
    let B := D.mapHomologicalComplex (ComplexShape.up ℕ)
    ∃ τ : (A ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙ U) ⟶
        (B ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙ T),
      ∃ c : ∀ C, U.obj ((A.obj C).cycles q) ⟶ T.obj ((B.obj C).cycles q),
        ∀ C, (c C ≫ T.map ((B.obj C).iCycles q) =
          U.map ((A.obj C).iCycles q) ≫ t.app (C.X q)) ∧
          U.map ((A.obj C).homologyπ q) ≫ τ.app C =
            c C ≫ T.map ((B.obj C).homologyπ q) := by
  classical
  let A := G.mapHomologicalComplex (ComplexShape.up ℕ)
  let B := D.mapHomologicalComplex (ComplexShape.up ℕ)
  -- Lift transported global cycles through the evaluated kernel of the differential.
  let k := fun C ↦ U.map ((A.obj C).iCycles q) ≫ t.app (C.X q)
  have hk (C) : k C ≫ T.map ((B.obj C).d q (q + 1)) = 0 := by
    dsimp only [k]
    rw [Category.assoc]
    change U.map ((A.obj C).iCycles q) ≫ t.app (C.X q) ≫
      (D ⋙ T).map (C.d q (q + 1)) = 0
    rw [← t.naturality (C.d q (q + 1)), ← Category.assoc]
    change (U.map ((A.obj C).iCycles q) ≫ U.map ((A.obj C).d q (q + 1))) ≫
      t.app (C.X (q + 1)) = 0
    rw [← U.map_comp, HomologicalComplex.iCycles_d, U.map_zero, zero_comp]
  let ki := fun C ↦ KernelFork.mapIsLimit _
    ((B.obj C).cyclesIsKernel q (q + 1) (by simp)) T
  let c := fun C ↦ (ki C).lift (KernelFork.ofι (k C) (hk C))
  have hc (C) : c C ≫ T.map ((B.obj C).iCycles q) = k C := by
    exact Fork.IsLimit.lift_ι (ki C)
  have c_nat {C C'} (a : C ⟶ C') :
      U.map (HomologicalComplex.cyclesMap (A.map a) q) ≫ c C' =
        c C ≫ T.map (HomologicalComplex.cyclesMap (B.map a) q) := by
    apply Fork.IsLimit.hom_ext (ki C')
    change (U.map (HomologicalComplex.cyclesMap (A.map a) q) ≫ c C') ≫
        T.map ((B.obj C').iCycles q) =
      (c C ≫ T.map (HomologicalComplex.cyclesMap (B.map a) q)) ≫
        T.map ((B.obj C').iCycles q)
    rw [Category.assoc, hc, Category.assoc, ← T.map_comp,
      HomologicalComplex.cyclesMap_i, T.map_comp, ← Category.assoc (c C), hc]
    dsimp only [k]
    rw [← Category.assoc, ← U.map_comp, HomologicalComplex.cyclesMap_i, U.map_comp,
      Category.assoc]
    change U.map ((A.obj C).iCycles q) ≫
        ((G ⋙ U).map (a.f q) ≫ t.app (C'.X q)) =
      (U.map ((A.obj C).iCycles q) ≫ t.app (C.X q)) ≫ (D ⋙ T).map (a.f q)
    rw [t.naturality, Category.assoc]
  -- The same kernel uniqueness identifies the lift of each incoming boundary.
  have c_boundary (C) :
      U.map ((A.obj C).sc q).toCycles ≫ c C =
        t.app (C.X ((ComplexShape.up ℕ).prev q)) ≫ T.map ((B.obj C).sc q).toCycles := by
    apply Fork.IsLimit.hom_ext (ki C)
    change (U.map ((A.obj C).sc q).toCycles ≫ c C) ≫
        T.map ((B.obj C).iCycles q) =
      (t.app (C.X ((ComplexShape.up ℕ).prev q)) ≫ T.map ((B.obj C).sc q).toCycles) ≫
        T.map ((B.obj C).iCycles q)
    rw [Category.assoc, hc]
    dsimp only [k]
    rw [← Category.assoc, ← U.map_comp]
    change U.map (((A.obj C).sc q).toCycles ≫ ((A.obj C).sc q).iCycles) ≫
        t.app (C.X q) =
      (t.app (C.X ((ComplexShape.up ℕ).prev q)) ≫ T.map ((B.obj C).sc q).toCycles) ≫
        T.map ((B.obj C).sc q).iCycles
    rw [ShortComplex.toCycles_i, Category.assoc, ← T.map_comp, ShortComplex.toCycles_i]
    exact t.naturality (C.d _ _)
  let b := fun C ↦ c C ≫ T.map ((B.obj C).homologyπ q)
  have hb (C) : U.map ((A.obj C).sc q).toCycles ≫ b C = 0 := by
    dsimp only [b]
    rw [← Category.assoc, c_boundary, Category.assoc, ← T.map_comp]
    change t.app _ ≫ T.map (((B.obj C).sc q).toCycles ≫
      ((B.obj C).sc q).homologyπ) = 0
    rw [ShortComplex.toCycles_comp_homologyπ, T.map_zero, comp_zero]
  -- Forgetting scalars preserves this cokernel, so the cycle map descends to homology.
  let pi := fun C ↦ CokernelCofork.mapIsColimit _ ((A.obj C).sc q).homologyIsCokernel U
  let δ := fun C ↦ (pi C).desc (CokernelCofork.ofπ (b C) (hb C))
  have hδ (C) : U.map ((A.obj C).homologyπ q) ≫ δ C = b C := by
    exact Cofork.IsColimit.π_desc (pi C)
  -- Naturality can be checked after the cokernel quotient on cycles.
  let τ : (A ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙ U) ⟶
      (B ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙ T) :=
    { app := δ
      naturality := by
        intro C C' a
        change U.map (HomologicalComplex.homologyMap (A.map a) q) ≫ δ C' =
          δ C ≫ T.map (HomologicalComplex.homologyMap (B.map a) q)
        apply Cofork.IsColimit.hom_ext (pi C)
        change U.map ((A.obj C).homologyπ q) ≫
            (U.map (HomologicalComplex.homologyMap (A.map a) q) ≫ δ C') =
          U.map ((A.obj C).homologyπ q) ≫
            (δ C ≫ T.map (HomologicalComplex.homologyMap (B.map a) q))
        calc
          _ = U.map (HomologicalComplex.cyclesMap (A.map a) q) ≫
              (U.map ((A.obj C').homologyπ q) ≫ δ C') := by
            rw [← Category.assoc, ← U.map_comp, HomologicalComplex.homologyπ_naturality,
              U.map_comp, Category.assoc]
          _ = U.map (HomologicalComplex.cyclesMap (A.map a) q) ≫
              (c C' ≫ T.map ((B.obj C').homologyπ q)) := by rw [hδ]
          _ = c C ≫ (T.map (HomologicalComplex.cyclesMap (B.map a) q) ≫
              T.map ((B.obj C').homologyπ q)) := by
            rw [← Category.assoc, c_nat, Category.assoc]
          _ = c C ≫ (T.map ((B.obj C).homologyπ q) ≫
              T.map (HomologicalComplex.homologyMap (B.map a) q)) := by
            rw [← T.map_comp, ← HomologicalComplex.homologyπ_naturality, T.map_comp]
          _ = _ := by
            rw [← Category.assoc (U.map ((A.obj C).homologyπ q)), hδ]
            exact (Category.assoc _ _ _).symm }
  exact ⟨τ, c, fun C ↦ ⟨hc C, hδ C⟩⟩

-- Elaborating the mapped kernel and cokernel lifts unfolds several composed functors.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison from cohomology of global sections to global sections of the
cohomology sheaf is natural in arbitrary nonnegative complexes, before any resolution
or derived-functor identification is chosen.

Source: Stacks Project, Cohomology, Tag 01F4 (2), cycle construction of the edge;
the direct-proof exercise in its proof (expanded by K1)
(blueprint: lem-pc-leray-complex-cocycle-comparison).

Proof: Sections of the direct image on the whole target are sections on the inverse
image of that open, identified with the whole source by `Opens.map_top`. This gives a
natural isomorphism of the underlying abelian-group complexes. Global sections
preserve kernels, so cycles of the sections complex identify with sections of the
cycle sheaf. Apply sections to the cycle-to-homology quotient. The resulting map
annihilates boundaries: the incoming differential factors through the boundary sheaf,
whose composite with the cycle-to-homology quotient is zero. It therefore factors
uniquely through the homology quotient of the sections complex. This factorization
is a group homomorphism. For a cochain map, both composites with this quotient agree
by naturality of the cycle inclusion and quotient; the quotient is epic, so the
factorizations agree. These maps form the displayed natural transformation. The
kernel identification supplies z and its inclusion equation, and the defining
factorization supplies the homology equation. This argument includes degree zero
(where the incoming differential is zero), zero complexes, and the empty scheme. -/
theorem leray_complex_cocycle_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    ∃ τ :
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙
          forget₂ _ AddCommGrpCat) ⟶
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙ HomologicalComplex.homologyFunctor _ _ q ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat),
      ∀ (C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ)
        (s : (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C).cycles q),
        ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj
          ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj C).cycles q),
          (C.X q).val.presheaf.map
            (eqToHom (congrArg op (Opens.map_top f.base).symm))
            ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj C).iCycles q s) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj C).iCycles q) z ∧
          (τ.app C)
            ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj C).homologyπ q s) =
            (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
              ((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj C).homologyπ q) z := by
  classical
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let H := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let U := forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat
  let V := forget₂ (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat
  let T := H ⋙ V
  let : PreservesFiniteLimits H := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  let t : G ⋙ U ⟶ D ⋙ T :=
    { app := fun M ↦ M.val.presheaf.map
        (eqToHom (congrArg op (Opens.map_top f.base).symm))
      naturality := by
        intro M N a
        exact (((PresheafOfModules.toPresheaf _).map a.val).naturality _).symm }
  obtain ⟨τ, c, hc⟩ := homologyComparisonOfNatTrans G D U T t q
  refine ⟨τ, ?_⟩
  intro C s
  refine ⟨c C s, ?_, ?_⟩
  · exact (CategoryTheory.congr_fun (hc C).1 s).symm
  · exact CategoryTheory.congr_fun (hc C).2 s

end AlgebraicGeometry
