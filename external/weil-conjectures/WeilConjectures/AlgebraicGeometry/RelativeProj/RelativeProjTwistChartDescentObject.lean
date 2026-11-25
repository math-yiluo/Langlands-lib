/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentCompatibility
import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistCompositionLaw
import WeilConjectures.AlgebraicGeometry.TraceFormula.DirectedTensorMatchingSections

/-! # Object part of relative Proj twist descent

## References

* Stacks Project, Constructions, Tag 01NR
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSectionComp

private theorem baseChange_data
    {R T B C : Type u} [CommRing R] [CommRing T] [CommRing B] [CommRing C]
    [Algebra R T] [Algebra R B] [Algebra T C] [Algebra R C] [IsScalarTower R T C]
    {ℬ : ℕ → Submodule R B} {𝒞 : ℕ → Submodule T C}
    [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
    (ψ : ℬ →+*ᵍ 𝒞) (hb : ψ.IsGradedBaseChange) :
    ∃ β : TensorProduct R T B ≃ₐ[T] C,
      (∀ b : B, β (TensorProduct.tmul R 1 b) = ψ b) ∧
      (∀ n : ℕ, 𝒞 n = Submodule.span T (ψ '' (ℬ n : Set B))) := by
  let : Algebra B C := ψ.toRingHom.toAlgebra
  have : IsScalarTower R B C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (hb.map_algebraMap r).symm
  have : Algebra.IsPushout R T B C := ⟨hb.isBaseChange_linearMap⟩
  refine ⟨Algebra.IsPushout.equiv R T B C, ?_, ?_⟩
  · intro b
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  · intro n
    apply le_antisymm
    · exact fun a ha ↦ hb.mem_span n ha
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact ψ.map_mem ha

private theorem restriction_comparison {U V : S.affineOpens} (h : U ≤ V) :
    ∃ θ : ∀ j : ℤ,
      (tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
          (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j,
      Proj.IsScalarExtensionTwistComparison (A.res h)
        (A.relProjFunctor.map (homOfLE h)) θ := by
  let f := (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom
  let : Algebra Γ(S, V.1) Γ(S, U.1) := f.toAlgebra
  let : Algebra Γ(S, V.1) (A.obj U) :=
    ((algebraMap Γ(S, U.1) (A.obj U)).comp f).toAlgebra
  have : IsScalarTower Γ(S, V.1) Γ(S, U.1) (A.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hb : (A.res h).IsGradedBaseChange := A.isGradedBaseChangeAlong h
  obtain ⟨β, hβ, hgraded⟩ := baseChange_data (A.res h) hb
  obtain ⟨θ, hθ, _⟩ := Proj.scalarExtension_twist_comparison
    (A.grading V) (A.grading U) (algebraMap _ _) (algebraMap _ _)
    (fun _ ↦ rfl) (fun _ ↦ rfl) β (A.res h) hβ hgraded
    (A.relProjFunctor.map (homOfLE h))
    (fun _ a _ _ ↦ Proj.map_preimage_basicOpen (A.res h) _ a)
    (fun _ a ha hn ↦ Proj.awayι_comp_map (A.res h) _ hn a ha)
  exact ⟨θ, hθ⟩

private theorem restriction_comparison_comp {U V W : S.affineOpens}
    (h : U ≤ V) (k : V ≤ W)
    (θ : ∀ j : ℤ,
      (tensorPullback (A.relProjFunctor.map (homOfLE k))).obj
        (Proj.twist (A.grading W) j) ≅ Proj.twist (A.grading V) j)
    (η : ∀ j : ℤ,
      (tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j)
    (ζ : ∀ j : ℤ,
      (tensorPullback (A.relProjFunctor.map (homOfLE (h.trans k)))).obj
        (Proj.twist (A.grading W) j) ≅ Proj.twist (A.grading U) j)
    (hθ : Proj.IsScalarExtensionTwistComparison (A.res k)
      (A.relProjFunctor.map (homOfLE k)) θ)
    (hη : Proj.IsScalarExtensionTwistComparison (A.res h)
      (A.relProjFunctor.map (homOfLE h)) η)
    (hζ : Proj.IsScalarExtensionTwistComparison (A.res (h.trans k))
      (A.relProjFunctor.map (homOfLE (h.trans k))) ζ) (j : ℤ) :
    ζ j = eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (Proj.twist (A.grading W) j))
        (A.relProjFunctor.map_comp (homOfLE h) (homOfLE k))) ≪≫
      (tensorPullbackSectionComp (A.relProjFunctor.map (homOfLE h))
        (A.relProjFunctor.map (homOfLE k))).app (Proj.twist (A.grading W) j) ≪≫
      (tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso (θ j) ≪≫ η j := by
  let f := (S.presheaf.map (homOfLE (X := S.Opens) k).op).hom
  let g := (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom
  let : Algebra Γ(S, W.1) Γ(S, V.1) := f.toAlgebra
  let : Algebra Γ(S, V.1) Γ(S, U.1) := g.toAlgebra
  let : Algebra Γ(S, W.1) Γ(S, U.1) := (g.comp f).toAlgebra
  have : IsScalarTower Γ(S, W.1) Γ(S, V.1) Γ(S, U.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Γ(S, W.1) (A.obj V) :=
    ((algebraMap Γ(S, V.1) (A.obj V)).comp f).toAlgebra
  have : IsScalarTower Γ(S, W.1) Γ(S, V.1) (A.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Γ(S, V.1) (A.obj U) :=
    ((algebraMap Γ(S, U.1) (A.obj U)).comp g).toAlgebra
  have : IsScalarTower Γ(S, V.1) Γ(S, U.1) (A.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hb : (A.res k).IsGradedBaseChange := A.isGradedBaseChangeAlong k
  have hc : (A.res h).IsGradedBaseChange := A.isGradedBaseChangeAlong h
  obtain ⟨β, hβ, hgraded⟩ := baseChange_data (A.res k) hb
  obtain ⟨γ, hγ, hgraded'⟩ := baseChange_data (A.res h) hc
  refine Proj.scalarExtension_twist_composition_law
    (A.grading W) (A.grading V) (algebraMap _ _) (algebraMap _ _)
    (fun _ ↦ rfl) (fun _ ↦ rfl) β (A.res k) hβ hgraded
    (A.relProjFunctor.map (homOfLE k))
    (fun _ a _ _ ↦ Proj.map_preimage_basicOpen (A.res k) _ a)
    (fun _ a ha hn ↦ Proj.awayι_comp_map (A.res k) _ hn a ha) θ hθ
    (A.grading U) γ (A.res h) hγ hgraded'
    (A.relProjFunctor.map (homOfLE h))
    (A.relProjFunctor.map (homOfLE (h.trans k)))
    (fun _ a ha hn ↦ Proj.awayι_comp_map (A.res h) _ hn a ha)
    ?_ η ζ hη ?_ (A.relProjFunctor.map_comp (homOfLE h) (homOfLE k)) j
  · intro n a ha hn
    have hirr : HomogeneousIdeal.irrelevant (A.grading U) ≤
        (HomogeneousIdeal.irrelevant (A.grading W)).map ((A.res h).comp (A.res k)) := by
      rw [A.res_comp h k]
      exact A.irrelevant_le_map_res (h.trans k)
    have hp : Proj.map ((A.res h).comp (A.res k)) hirr =
        A.relProjFunctor.map (homOfLE (h.trans k)) :=
      (Proj.map_congr (A.res_comp h k) hirr
        (A.irrelevant_le_map_res (h.trans k))).trans
          (A.relProjFunctor_map_homOfLE (h.trans k)).symm
    simpa only [GradedRingHom.comp_apply, hp] using
      Proj.awayι_comp_map ((A.res h).comp (A.res k)) hirr hn a ha
  · simpa only [A.res_comp h k] using hζ

/-- The affine degree-one twists admit a descended module and local chart isomorphisms. -/
theorem exists_twist_chart_descent_object :
    ∃ (L : A.relProj.Modules),
      ∃ (chart : ∀ U : S.affineOpens,
        (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
          Proj.twist (A.grading U) 1),
      TwistChartCompatibility A L chart := by
  classical
  choose θ hθ using fun (U V : S.affineOpens) (h : U ≤ V) ↦
    restriction_comparison A h
  let 𝒰 := A.relProjGluingData.cover
  have : Quiver.IsThin 𝒰.I₀ := inferInstanceAs (Quiver.IsThin S.affineOpens)
  let M : ∀ U : 𝒰.I₀, (𝒰.X U).Modules := fun U ↦ Proj.twist (A.grading U) 1
  let t : ∀ {U V : S.affineOpens} (f : U ⟶ V),
      (tensorPullback (𝒰.trans f)).obj (M V) ≅ M U :=
    fun {U V} f ↦ θ U V (leOfHom f) 1
  have ht : ∀ {U V W : S.affineOpens} (f : U ⟶ V) (g : V ⟶ W),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M W)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M W) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f := by
    intro U V W f g
    exact restriction_comparison_comp A (leOfHom f) (leOfHom g)
      (θ V W (leOfHom g)) (θ U V (leOfHom f)) (θ U W (leOfHom (f ≫ g)))
      (hθ V W (leOfHom g)) (hθ U V (leOfHom f)) (hθ U W (leOfHom (f ≫ g))) 1
  refine ⟨tensorMatchingModule 𝒰 M t, tensorMatchingChartIso 𝒰 M t ht, ?_⟩
  intro U V h
  exact ⟨θ U V h, hθ U V h,
    tensorMatchingChartIso_condition 𝒰 M t ht (homOfLE (X := S.affineOpens) h)⟩

end AlgebraicGeometry.Scheme.GradedAlgebraData
