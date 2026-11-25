/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjAffineGeneratorLinear
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Normalized degree-one sections of the glued symmetric Proj twist

Source: Stacks Project, Constructions, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-glued-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

private theorem affine_linear_maps_glue {S : Scheme.{u}} (E F : S.Modules)
    (t : ∀ U : S.affineOpens, E.val.obj (op U.1) →ₗ[Γ(S, U.1)] F.val.obj (op U.1))
    (ht : ∀ (U V : S.affineOpens) (h : U ≤ V) (m : E.val.obj (op V.1)),
      F.presheaf.map (homOfLE (X := S.Opens) h).op (t V m) =
        t U (E.presheaf.map (homOfLE (X := S.Opens) h).op m)) :
    ∃ σ : E ⟶ F, ∀ (U : S.affineOpens) (m : E.val.obj (op U.1)),
      σ.app U.1 m = t U m := by
  let B : S.affineOpens → S.Opens := Subtype.val
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    simpa only [B, Subtype.range_coe] using S.isBasis_affineOpens
  let β : (inducedFunctor B).op ⋙ E.presheaf ⟶
      (inducedFunctor B).op ⋙ F.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom (t U.unop).toAddMonoidHom
      naturality := by
        intro U V f
        ext m
        exact (ht V.unop U.unop f.unop.hom.le m).symm }
  let α : E.presheaf ⟶ F.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom E.presheaf
      ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) hB β
  have hα (U : S.affineOpens) (m : E.val.obj (op U.1)) :
      α.app (op U.1) m = t U m := by
    exact congrArg (fun f : E.presheaf.obj (op U.1) ⟶ F.presheaf.obj (op U.1) ↦ f m)
      (TopCat.Sheaf.extend_hom_app E.presheaf
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) hB β U)
  have lin (W : S.Opens) (r : Γ(S, W)) (m : E.val.obj (op W)) :
      α.app (op W) (r • m) = r • α.app (op W) m := by
    let I := {U : S.affineOpens // U.1 ≤ W}
    have hc : W ≤ ⨆ U : I, U.1.1 := by
      intro x hx
      obtain ⟨V, hV, hxV, hVW⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
      exact (show V ≤ ⨆ U : I, U.1.1 from
        le_iSup_of_le (⟨⟨V, hV⟩, hVW⟩ : I) le_rfl) hxV
    let F' : TopCat.Sheaf (Type u) S :=
      (sheafCompose _ (forget AddCommGrpCat.{u})).obj
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F)
    apply F'.eq_of_locally_eq' (fun U : I ↦ U.1.1) W
      (fun U ↦ homOfLE U.2) hc
    intro U
    change F.presheaf.map (homOfLE U.2).op (α.app (op W) (r • m)) =
      F.presheaf.map (homOfLE U.2).op (r • α.app (op W) m)
    have hn (x : E.val.obj (op W)) :
        α.app (op U.1.1) (E.presheaf.map (homOfLE U.2).op x) =
          F.presheaf.map (homOfLE U.2).op (α.app (op W) x) :=
      CategoryTheory.congr_fun (α.naturality (homOfLE U.2).op) x
    rw [← hn, E.map_smul, F.map_smul, ← hn, hα, hα]
    exact (t U.1).map_smul _ _
  let σ : E ⟶ F := ⟨PresheafOfModules.homMk α (fun W ↦ lin W.unop)⟩
  exact ⟨σ, hα⟩

private theorem twist_chart_read_bijective {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1)
    (U : S.affineOpens) : Function.Bijective (A.twistChartRead L chart U) := by
  let j := A.relProjι U
  let adj := Scheme.Modules.tensorPullbackSectionAdjunction j
  have hu : Function.Bijective ((adj.unit.app L).app (A.relProjHom ⁻¹ᵁ U.1)) := by
    have he := (Scheme.Modules.pullbackPushforwardAdjunction j).unit_leftAdjointUniq_hom_app
      adj L
    have hb := Scheme.Modules.bijective_pullbackUnit_app_of_isOpenImmersion j L
      (le_of_eq (A.relProjHom_preimage U))
    rw [← he, Scheme.Modules.Hom.comp_app]
    exact (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pushforward j).map
        (((Scheme.Modules.pullbackPushforwardAdjunction j).leftAdjointUniq adj).hom.app L)).app
          (A.relProjHom ⁻¹ᵁ U.1))).comp hb
  exact (ConcreteCategory.bijective_of_isIso
    ((chart U).hom.app (A.twistChartOpen U))).comp hu

/-- The degree-one affine twists glue, together with the sheaf map sending a module
section to its homogeneous fraction. No invertibility or surjectivity is asserted here.
Source: Stacks, Tag 01NR (lemma-glue-relative-proj-twists), specialized to degree one
of the symmetric algebra as in Tag 01OB (definition-projective-bundle).
(blueprint: lem-trf-symmetric-proj-glued-sections).

Proof: on every affine base open U take the existing module Proj.twist A(U) 1.
Quasi-coherent affine restriction is coefficientwise scalar extension. On the standard
open D_+(e), the scalar-extension isomorphism sends a/e^k to res(a)/res(e)^k.
These maps and their inverses commute with further standard-open restriction and
compose by the fraction formula. Refine intersections of affine base opens by affine
opens; agreement after refinement supplies the descent cocycle on the relative-Proj
chart cover. Glue these actual module sheaves and the chart isomorphisms. The sections
m ↦ iota(m)/1 are additive, linear over the base structure map, and compatible with
restriction by that same fraction formula. They therefore glue to a module morphism
σ from E to the direct image of the glued module. Its displayed normalization is the
local formula for this morphism, transported through the actual tensor-pullback unit.
No local freeness, finite generation, or nonemptiness is needed. -/
theorem exists_symmetric_twist_sections
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] :
    ∃ (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
      (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1)
      (σ : E ⟶ (Scheme.Modules.pushforward
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj L),
    ∀ (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1),
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) L
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (σ.app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))) := by
  classical
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  obtain ⟨L, chart, hc⟩ := A.exists_twist_chart_descent
  have hι (U : S.affineOpens) (m : E.val.obj (op U.1)) :
      SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈ A.grading U 1 := by
    change _ ∈ _ ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ m
  choose g hg using exists_affine_generator_linear S E
  let read (U : S.affineOpens) := A.twistChartRead L chart U
  let e (U : S.affineOpens) := LinearEquiv.ofBijective (read U).hom
    (twist_chart_read_bijective A L chart U)
  let t (U : S.affineOpens) := (e U).symm.toLinearMap.comp (g U)
  have ht (U : S.affineOpens) (m : E.val.obj (op U.1)) :
      read U (t U m) = A.twistChartFraction U
        ⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m, hι U m⟩ := by
    exact ((e U).apply_symm_apply (g U m)).trans (hg U m (hι U m))
  have nat (U V : S.affineOpens) (h : U ≤ V) (m : E.val.obj (op V.1)) :
      ((Scheme.Modules.pushforward A.relProjHom).obj L).presheaf.map
          (homOfLE (X := S.Opens) h).op (t V m) =
        t U (E.presheaf.map (homOfLE (X := S.Opens) h).op m) := by
    apply (twist_chart_read_bijective A L chart U).injective
    obtain ⟨r, hr, hf⟩ := hc U V h
    calc
      _ = r (read V (t V m)) := (hr (t V m)).symm
      _ = r (A.twistChartFraction V ⟨_, hι V m⟩) := congrArg r (ht V m)
      _ = A.twistChartFraction U ⟨_, _⟩ := hf ⟨_, hι V m⟩
      _ = read U (t U (E.presheaf.map (homOfLE (X := S.Opens) h).op m)) := by
        rw [ht]
        congr 1
        apply Subtype.ext
        exact SymmetricAlgebraSheaf.restriction_ι E (homOfLE (X := S.Opens) h).op m
  obtain ⟨σ, hσ⟩ := affine_linear_maps_glue E
    ((Scheme.Modules.pushforward A.relProjHom).obj L) t nat
  refine ⟨L, chart, σ, ?_⟩
  intro U m hm
  have he := ht U m
  rw [← hσ U m] at he
  have hu := (Classical.choose_spec
    (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction (A.relProjι U))).1 L
      (A.relProjHom ⁻¹ᵁ U.1) (σ.app U.1 m)
  change (chart U).hom.app (A.twistChartOpen U)
    (((Scheme.Modules.tensorPullbackSectionAdjunction (A.relProjι U)).unit.app L).app
      (A.relProjHom ⁻¹ᵁ U.1) (σ.app U.1 m)) = _ at he
  exact (congrArg ((chart U).hom.app (A.twistChartOpen U)) hu.symm).trans he

end AlgebraicGeometry.SymmetricProjTautologicalCharts
