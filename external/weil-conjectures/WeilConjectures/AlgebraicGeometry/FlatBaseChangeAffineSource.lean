/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.AffineCohomologySectionEquiv
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source affine dictionary, with its specified pure-tensor normalization.
Source: Stacks Project, Tags 02KH (first paragraph), 01XJ, 01E4 and 03FD.
(blueprint: new-flat-base-change-affine-source)

Proof: Put A = Gamma(V), B = Gamma(W), U = f inverse V, and N = F restricted to U.
Identify pullback along U's open immersion with restriction by the unique
adjunction comparison, preserving the restriction unit. Compute module cohomology
and Ext-based abelian-sheaf cohomology on the same section complex of a module
injective resolution: forgotten injectives are section-acyclic (03FD). This gives
a canonical additive eH. Naturality for multiplication by sections shows that eH
commutes with the A-action through h. The augmentation and components equations
of D.source identify its section complex with the restriction of I, so changing
this resolution does not change eH or the class represented by a cocycle.

By ordinaryHigherImage_isQuasicoherent, all R^q f_* F are quasi-coherent. Their
positive cohomology over the affine V vanishes. The cocycle-normalized Leray edge
is therefore an A-linear isomorphism from cohomology on U to Gamma(P,V).
The presheaf description of higher images (01E4) identifies this edge, on the
section complex recorded in D, with D.sourceClass. Compose it with eH inverse.
Apply exists_tensorPullback_affine_sections to g, V, W and P, swap the two tensor
factors, and extend the preceding A-linear isomorphism by B. This gives a
bijective B-linear map. The affine section theorem sends s tensor z to s times
the restricted adjunction unit of z; substituting z = D.sourceClass(eH inverse xi)
is exactly the displayed formula. For empty opens or zero F these are zero
modules; in degree zero the same edges are the augmentation comparisons. -/
theorem Scheme.Modules.exists_flatBaseChange_affine_source
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let P := ((Scheme.Modules.pushforward f).rightDerived p).obj F
    ∃ (eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) →ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W)),
      Function.Bijective a ∧
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (eH.symm xi)))) := by
  classical
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
  intro h N P
  choose E hE using
    Scheme.Modules.exists_moduleCohomology_source_comparison (f ⁻¹ᵁ V).toScheme p
  let eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
        Scheme.Modules.HOver h N p :=
    (E ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).trans
      (Scheme.Modules.H.mapLinearEquiv
        ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F) p).toAddEquiv
  choose e he using
    Scheme.Modules.exists_affine_cohomology_section_equiv f F I p V hV D.source E hE
  have hP : P.IsQuasicoherent := ordinaryHigherImage_isQuasicoherent f F inferInstance p
  let : ∀ G : S.Modules, Module Γ(S, V)
      Γ((Scheme.Modules.tensorPullback g).obj G, W) :=
    fun G ↦ Module.compHom _ (g.appLE V W eVW).hom
  choose c hc hs ht _ using
    Scheme.Modules.exists_tensorPullback_affine_sections g ⟨V, hV⟩ ⟨W, hW⟩ eVW
  let k : (Γ(S', W) ⊗[Γ(S, V)] Γ(P, V)) →ₗ[Γ(S', W)]
      Γ((Scheme.Modules.tensorPullback g).obj P, W) :=
    { toFun := fun t ↦ c P hP ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm t)
      map_add' := by intro t t'; simp
      map_smul' := by
        intro b t
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          hs P hP b ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm t) }
  let t : (Γ(S', W) ⊗[Γ(S, V)] Scheme.Modules.HOver h N p) ≃ₗ[Γ(S', W)]
      (Γ(S', W) ⊗[Γ(S, V)] Γ(P, V)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(S', W) Γ(S', W)) e
  refine ⟨eH, k.comp t.toLinearMap, ?_, ?_⟩
  · exact (hc P hP).comp
      ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm.bijective.comp t.bijective)
  · intro s xi
    change c P hP (e xi ⊗ₜ[Γ(S, V)] s) = _
    have he' : e xi = D.sourceClass p (eH.symm xi) := by
      simpa only [Scheme.Modules.FlatBaseChangeOpenChoices.sourceClass, eH] using he xi
    exact (ht P hP (e xi) s).trans (congrArg (fun z ↦ s •
      ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
        (Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
          V z)) he')
end AlgebraicGeometry
