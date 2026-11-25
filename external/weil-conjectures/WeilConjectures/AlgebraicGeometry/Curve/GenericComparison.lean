/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity

/-!
# Comparing the cohomology of a curve with that of its generic point

Let `C` be an integral curve over an algebraically closed field, with generic point
`η : Spec k(C) ⟶ C`. For every abelian étale sheaf `F` on `C` the unit `F ⟶ η_* η^* F` induces
isomorphisms `Hᵠ(C, F) ≅ Hᵠ(C, η_* η^* F)` for `q ≥ 2`.

For a nonempty affine open `U` of `C` write `u_U : G ⟶ j_{U*} j_U^* G` for the unit of the open
immersion `j_U : Spec Γ(C, U) ⟶ C`. Say that the sections of `G` *vanish generically* if every
section of `G` vanishes, locally, under some `u_U`. Such a sheaf is the filtered union of the
kernels of the `u_U`, each of which vanishes over `U`, hence is supported on the finitely many
closed points outside `U` and has no cohomology in positive degrees; so `G` itself has no
cohomology in positive degrees (`AlgebraicGeometry.IsCurve.subsingleton_H_of_genericVanishing`,
blueprint `theorem-cohomology-curves`). The kernel and the cokernel of `F ⟶ η_* η^* F` have
generically vanishing sections, by continuity of sections at `Spec k(C) = lim_U Spec Γ(C, U)`
(`AlgebraicGeometry.Etale.unitComparison_app_surjective_of_isLimit`).

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_H_of_genericVanishing`: generically vanishing sheaves
  are acyclic.
- `AlgebraicGeometry.IsCurve.bijective_H_map_unit_fromSpecFunctionField`: the unit
  `F ⟶ η_* η^* F` induces bijections on `Hᵠ` for `q ≥ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

open scoped Etale

section Sections

variable {X : Scheme.{u}}

/-- A monomorphism of sheaves is injective on sections. -/
lemma Etale.injective_app_of_mono {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) [Mono ψ] (W : X.Etale) : Function.Injective (ψ.hom.app (op W)) := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op W)
  have : Mono (E.map ψ) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- A sieve on an étale `X`-scheme `V` which contains all morphisms from étale `X`-schemes with
affine underlying scheme is a covering sieve. -/
lemma Etale.mem_smallEtaleTopology_of_forall_isAffine {V : X.Etale} (R : Sieve V)
    (h : ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), IsAffine W.left → R g) : R ∈ X.smallEtaleTopology V := by
  refine (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
  obtain ⟨A, hA, hxA, -⟩ : ∃ A : V.left.Opens, A ∈ V.left.affineOpens ∧ x ∈ A ∧ A ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 V.left.isBasis_affineOpens)
      (TopologicalSpace.Opens.mem_top x)
  let VA : X.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom)
    (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)
  let g : VA ⟶ V := MorphismProperty.Over.homMk A.ι rfl trivial
  exact ⟨VA, g, h g hA, ⟨x, hxA⟩, rfl⟩

end Sections

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

instance (U : X.NonemptyAffineOpens) : IsOpenImmersion (X.affineOpensDiagramι.app U) :=
  inferInstanceAs (IsOpenImmersion U.2.1.fromSpec)

instance (U : X.NonemptyAffineOpens) : IsAffine (X.affineOpensDiagram.obj U) :=
  inferInstanceAs (IsAffine (Spec Γ(X, U.1)))

instance (U : X.NonemptyAffineOpens) : CompactSpace (X.affineOpensDiagram.obj U) :=
  inferInstanceAs (CompactSpace (Spec Γ(X, U.1)))

instance (U : X.NonemptyAffineOpens) : QuasiSeparatedSpace (X.affineOpensDiagram.obj U) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec Γ(X, U.1)))

instance {U V : X.NonemptyAffineOpens} (f : U ⟶ V) : IsAffineHom (X.affineOpensDiagram.map f) :=
  isAffineHom_of_isAffine _

/-- The unit `G ⟶ j_* j^* G` of the open immersion `j : Spec Γ(X, U) ⟶ X` of a nonempty affine
open `U`. -/
noncomputable abbrev affineOpenUnit (U : X.NonemptyAffineOpens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (X.affineOpensDiagramι.app U)).unit.app
    G

lemma affineOpensDiagramι_map {U V : X.NonemptyAffineOpens} (f : U ⟶ V) :
    X.affineOpensDiagramι.app U = X.affineOpensDiagram.map f ≫ X.affineOpensDiagramι.app V := by
  simpa using (X.affineOpensDiagramι.naturality f).symm

/-- The transition map between the units of two nested nonempty affine opens. -/
noncomputable abbrev affineOpenTransition {U V : X.NonemptyAffineOpens} (f : U ⟶ V)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Etale.unitComparison (X.affineOpensDiagram.map f) (X.affineOpensDiagramι.app V)
    (X.affineOpensDiagramι.app U) (affineOpensDiagramι_map f) G

lemma affineOpenUnit_comp_transition {U V : X.NonemptyAffineOpens} (f : U ⟶ V)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    X.affineOpenUnit V G ≫ X.affineOpenTransition f G = X.affineOpenUnit U G :=
  Etale.unit_app_comp_unitComparison _ _ _ _ G

/-- The sieve of the morphisms `W ⟶ V` along which a section `s` of `G` over `V` is killed by
the unit of some nonempty affine open. -/
@[simps]
noncomputable def genericVanishingSieve (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : X.Etale} (s : G.obj.obj (op V)) : Sieve V where
  arrows W g := ∃ U : X.NonemptyAffineOpens,
    (X.affineOpenUnit U G).hom.app (op W) (G.obj.map g.op s) = 0
  downward_closed := by
    rintro W W' g ⟨U, hU⟩ h
    refine ⟨U, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [NatTrans.naturality_apply (X.affineOpenUnit U G).hom h.op (G.obj.map g.op s)]
    rw [hU, map_zero]

end Scheme

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve f] [IsIntegral C]

include f in
/-- **A sheaf with generically vanishing sections is acyclic.** Let `C` be an integral curve over
an algebraically closed field and `G` an abelian étale sheaf on `C` every section of which
vanishes locally under the unit of some nonempty affine open. Then `Hⁱ(C, G) = 0` for `i ≥ 1`:
`G` is the filtered union of the kernels of the units, which are supported on finitely many
closed points.
(blueprint: `theorem-cohomology-curves`) -/
theorem subsingleton_H_of_genericVanishing
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ (V : C.Etale) (s : G.obj.obj (op V)),
      C.genericVanishingSieve G s ∈ C.smallEtaleTopology V) (i : ℕ) :
    Subsingleton (Sheaf.H G (i + 1)) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  have hdim : topologicalKrullDim C ≤ 1 := IsCurve.krullDim_le_one (f := f)
  -- the diagram of kernels of the units
  let K (U : C.NonemptyAffineOpens) := kernel (C.affineOpenUnit U G)
  let Dg : C.NonemptyAffineOpensᵒᵖ ⥤ Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj U := K U.unop
      map {U V} g := kernel.lift _ (kernel.ι _) (by
        rw [← C.affineOpenUnit_comp_transition g.unop G, kernel.condition_assoc, zero_comp])
      map_id U := by
        rw [← cancel_mono (kernel.ι _)]
        simp only [kernel.lift_ι]
        exact (Category.id_comp _).symm
      map_comp g h := by
        rw [← cancel_mono (kernel.ι _)]
        simp }
  let cG : Cocone Dg :=
    { pt := G
      ι := { app U := kernel.ι _ } }
  -- the cocone of kernels is a colimit
  have : AB5OfSize.{u, u} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : IsConnected C.NonemptyAffineOpensᵒᵖ := IsFiltered.isConnected _
  let φ := colimit.desc Dg cG
  have hmono : Mono φ := by
    let α : Dg ⟶ (Functor.const _).obj G := { app U := kernel.ι _ }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit
      ((Functor.const C.NonemptyAffineOpensᵒᵖ).obj G)).coconePointUniqueUpToIso
      (isColimitConstCocone C.NonemptyAffineOpensᵒᵖ G)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun U ↦ ?_
      simp [φ, e, cG, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      refine C.smallEtaleTopology.superset_covering ?_ (hG V s)
      rintro W g ⟨U, hU⟩
      obtain ⟨t, ht⟩ := Etale.exists_kernel_ι_app_eq _ _ hU
      refine ⟨(colimit.ι Dg (op U)).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom,
        colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit Dg).desc cG) := isIso_of_mono_of_epi φ
  have hcG : IsColimit cG := IsColimit.ofPointIso (colimit.isColimit Dg)
  -- the kernels have no cohomology in positive degrees
  have hK (U : C.NonemptyAffineOpens) : Subsingleton (Sheaf.H (K U) (i + 1)) := by
    let j := C.affineOpensDiagramι.app U
    let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
    have hiso : IsIso ((j)^*[AddCommGrpCat.{u + 1}].map (C.affineOpenUnit U G)) := by
      have : IsIso ((j)^*[AddCommGrpCat.{u + 1}].map (adj.unit.app G) ≫
          adj.counit.app ((j)^*[AddCommGrpCat.{u + 1}].obj G)) := by
        rw [adj.left_triangle_components G]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    have hmono : Mono ((j)^*[AddCommGrpCat.{u + 1}].map (C.affineOpenUnit U G)) :=
      @IsIso.mono_of_iso _ _ _ _ _ hiso
    have hz : IsZero ((j)^*[AddCommGrpCat.{u + 1}].obj (K U)) :=
      (isZero_kernel_of_mono ((j)^*[AddCommGrpCat.{u + 1}].map (C.affineOpenUnit U G))).of_iso
        (PreservesKernel.iso _ _)
    have hz' : IsZero ((U.1.ι)^*[AddCommGrpCat.{u + 1}].obj (K U)) :=
      (Functor.map_isZero ((U.2.1.isoSpec.hom)^*[AddCommGrpCat.{u + 1}]) hz).of_iso
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} U.2.1.isoSpec.hom j U.1.ι
          U.2.1.isoSpec_hom_fromSpec.symm).app _)
    have hne : (U.1 : Set C).Nonempty := U.2.2
    exact Etale.subsingleton_H_of_isZero_upperStar U.1
      (U.1.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim hne)
      (fun x hx ↦ U.1.isOpen.isClosed_singleton_of_mem_compl hdim hne hx)
      (fun x hx ↦ by
        have := Scheme.isAlgClosed_residueField_of_isClosed f x
          (U.1.isOpen.isClosed_singleton_of_mem_compl hdim hne hx)
        infer_instance) _ hz' i
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have := essentiallySmallSelf.{u + 1} C.NonemptyAffineOpensᵒᵖ
  obtain ⟨U, y, rfl⟩ :=
    (Scheme.H_map_isColimit_of_isFiltered_of_large C hcG (i + 1)).1 x
  have := hK U.unop
  rw [Subsingleton.elim y 0, map_zero]

include f in
/-- **Generic replacement.** Let `C` be an integral curve over an algebraically closed field,
with generic point `η : Spec k(C) ⟶ C`. For every abelian étale sheaf `F` on `C` the unit
`F ⟶ η_* η^* F` induces bijections `Hᵠ(C, F) → Hᵠ(C, η_* η^* F)` for `q ≥ 2`: its kernel and
cokernel have generically vanishing sections by continuity of sections at the limit
`Spec k(C) = lim_U Spec Γ(C, U)`, hence are acyclic. -/
theorem bijective_H_map_unit_fromSpecFunctionField
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (Sheaf.H.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      C.fromSpecFunctionField).unit.app F) (n + 2)) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  let ε := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    C.fromSpecFunctionField).unit.app F
  let D := C.affineOpensDiagram
  let ι := C.affineOpensDiagramι
  let c := C.functionFieldCone
  have hc : IsLimit c := C.isLimitFunctionFieldCone
  have hP := C.fromSpecFunctionField_eq_functionFieldCone_comp
  -- the comparison maps to `η_* η^* F`
  let τ (U : C.NonemptyAffineOpens) := Etale.unitComparison (c.π.app U) (ι.app U)
    C.fromSpecFunctionField (hP U) F
  have hτ (U : C.NonemptyAffineOpens) : C.affineOpenUnit U F ≫ τ U = ε :=
    Etale.unit_app_comp_unitComparison _ _ _ _ F
  refine Sheaf.H.bijective_map_of_subsingleton ε (fun i ↦ ?_) (fun i ↦ ?_) n
  · -- the kernel
    refine subsingleton_H_of_genericVanishing f _ (fun V s ↦ ?_) i
    refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_
    let x := (kernel.ι ε).hom.app (op W) ((kernel ε).obj.map g.op s)
    have hx : ε.hom.app (op W) x = 0 := by
      change (kernel.ι ε ≫ ε).hom.app (op W) _ = 0
      rw [kernel.condition]
      rfl
    let U₀ : C.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (τ U₀).hom.app (op W) ((C.affineOpenUnit U₀ F).hom.app (op W) x) = 0 := by
      rw [← hτ U₀] at hx
      exact hx
    obtain ⟨U, f', hU⟩ := Etale.exists_unitComparison_app_eq_zero_of_isLimit D ι c
      C.fromSpecFunctionField hP hc F W U₀ _ h₀
    refine ⟨U, ?_⟩
    have hxU : (C.affineOpenUnit U F).hom.app (op W) x = 0 := by
      rw [← C.affineOpenUnit_comp_transition f' F]
      exact hU
    let A := (ι.app U)^*[AddCommGrpCat.{u + 1}] ⋙ (ι.app U)_*[AddCommGrpCat.{u + 1}]
    have : Mono (A.map (kernel.ι ε)) := inferInstance
    refine Etale.injective_app_of_mono (A.map (kernel.ι ε)) W ?_
    rw [map_zero]
    have := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι.app U)).unit.naturality
      (kernel.ι ε)
    change ((C.affineOpenUnit U (kernel ε) ≫ A.map (kernel.ι ε)).hom.app (op W)) _ = 0
    rw [← this]
    exact hxU
  · -- the cokernel
    refine subsingleton_H_of_genericVanishing f _ (fun V t ↦ ?_) i
    let π := cokernel.π ε
    have : Sheaf.IsLocallySurjective π :=
      (Sheaf.isLocallySurjective_iff_epi' (φ := π)).2 inferInstance
    refine C.smallEtaleTopology.transitive (Presheaf.imageSieve_mem _ π.hom t) _
      fun W g ⟨ta, hta⟩ ↦ ?_
    refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W' h hW' ↦ ?_
    let E := (C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((C.fromSpecFunctionField)^*[AddCommGrpCat.{u + 1}].obj F)
    obtain ⟨U, s, hs⟩ := Etale.unitComparison_app_surjective_of_isLimit D ι c
      C.fromSpecFunctionField hP hc F W' (E.obj.map h.op ta)
    refine ⟨U, ?_⟩
    let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ι.app U)
    let A := (ι.app U)^*[AddCommGrpCat.{u + 1}] ⋙ (ι.app U)_*[AddCommGrpCat.{u + 1}]
    -- the morphism identity `τ ≫ π ≫ u = 0`
    have key : τ U ≫ π ≫ adj.unit.app (cokernel ε) = 0 := by
      have h₁ : π ≫ adj.unit.app (cokernel ε) = adj.unit.app E ≫ A.map π :=
        adj.unit.naturality π
      have h₂ : τ U ≫ adj.unit.app E = adj.unit.app (A.obj F) ≫ A.map (τ U) :=
        adj.unit.naturality (τ U)
      have h₃ : adj.unit.app (A.obj F) = A.map (adj.unit.app F) :=
        (CategoryTheory.Adjunction.map_map_unit_app_eq adj F).symm
      have h₄ : adj.unit.app F ≫ τ U ≫ π = 0 := by
        rw [← Category.assoc]
        exact (congrArg (· ≫ π) (hτ U)).trans (cokernel.condition ε)
      rw [h₁, ← Category.assoc, h₂, h₃, Category.assoc, ← A.map_comp, ← A.map_comp, h₄,
        A.map_zero]
    change (C.affineOpenUnit U (cokernel ε)).hom.app (op W')
      ((cokernel ε).obj.map (h ≫ g).op t) = 0
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hta]
    erw [← NatTrans.naturality_apply π.hom h.op ta]
    erw [← hs]
    change ((τ U ≫ π ≫ adj.unit.app (cokernel ε)).hom.app (op W')) s = 0
    rw [key]
    rfl

end IsCurve

end AlgebraicGeometry
