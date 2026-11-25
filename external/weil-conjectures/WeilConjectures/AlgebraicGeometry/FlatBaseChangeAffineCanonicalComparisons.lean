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
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.AffineCohomologySectionEquiv
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison

/-! # Canonical affine section comparisons before flat base change

Source: Stacks Project, Tags 02KH (affine dictionary paragraph), 01XJ, 01XK,
01E4 and 03FD. (blueprint: new-flat-base-change-affine-canonical-comparisons)
-/

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
/-- Canonical source and target affine comparisons, compatible with the cohomological
pullback. This asserts no invertibility of the cohomological base-change map and needs
no flatness of either projection. The additive comparison is existential here; it is
not an arbitrary additive change of coordinates.

Source: Stacks Project, Tag 02KH, first paragraph of the proof; Tags 01XJ, 01XK,
01E4 and 03FD. (blueprint: new-flat-base-change-affine-canonical-comparisons)

Proof: Identify open-immersion pullback with restriction via their adjunctions. Forget
an injective module resolution to abelian sheaves; forgotten injectives are acyclic
for sections, so the common section complex compares derived module sections with
Ext cohomology. Precomposition by the canonical constant-integer/free-Yoneda comparison
fixes e0. Naturality for multiplication by sections makes this comparison A-linear.
The augmentation and components equations in D.source identify its section complex
with that of the original resolution I, independently of the comparison choices.

The higher direct images of F are quasi-coherent because f is qcqs (01XJ). On affine
V their positive cohomology vanishes. The cocycle-normalized Leray edge (01XK) therefore
identifies H(U,N) with sections of P over V; on the section complex recorded in D this
edge sends e0(x) to D.sourceClass(x), by 01E4. Tensor this A-linear identification with
B and apply the affine tensor-pullback sections formula to P. Its unit formula gives
a0(s tensor xi) = s times the restriction of the unit at D.sourceClass(e0 inverse xi).
This constructs a0 as a B-linear equivalence without any flatness assumption.

The affine chart square identifies U_B with the inverse image of W in the original
cartesian square. The pullback composition isomorphisms identify N_B with the restriction
of g'^*F there. Since f' is qcqs and g'^*F is quasi-coherent, its higher images are again
quasi-coherent. On affine W the same vanishing and Leray edge, composed with the chart
and module/abelian comparisons, construct b0 as a B-linear equivalence.

To verify the last equality, compute the two maps on the common section complexes.
An augmented comparison of injective resolutions represents the map defining
moduleCohomologyFMap(D.psi); applying exact inverse image to an abelian injective
resolution and its acyclic comparison represents the Ext pullback defining
H.baseChangeLinear. Both represent the coefficient map induced by the pullback unit:
D.unit_square and the pullback composition unit equations identify these maps.
Resolution comparisons preserving augmentations are homotopic, hence induce the same
map on cohomology. The components equations of D identify restrictions to W termwise.
Apply the cocycle formulas for the two Leray edges, which take a cocycle to its class
in the higher image. They give precisely the displayed last equality. All scalar
representations commute with these maps, so b0 is B-linear. This construction includes
empty opens, zero coefficients, and degree zero, where the edges are augmentations. -/
theorem Scheme.Modules.exists_flatBaseChange_affine_canonical_comparisons
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
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
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∃ (e0 : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a0 : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) ≃ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W))
      (b0 : Scheme.Modules.HOver (Scheme.Modules.baseChangeSnd (S := Γ(S', W)) h)
          (Scheme.Modules.baseChangedModule (S := Γ(S', W)) h N) p ≃ₗ[Γ(S', W)]
          Γ(Q, W)),
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a0 (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (e0.symm xi)))) ∧
      (∀ xi : Scheme.Modules.HOver h N p,
        b0 (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
          Q.presheaf.map (homOfLE eVW).op
            (D.targetClass p
              (Scheme.Modules.moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (e0.symm xi)))) := by
  classical
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
  intro h N P Q
  let : ∀ G : S.Modules, Module Γ(S, V)
      Γ((Scheme.Modules.tensorPullback g).obj G, W) :=
    fun G ↦ Module.compHom _ (g.appLE V W eVW).hom
  refine (Scheme.Modules.exists_tensorPullback_affine_sections
    g ⟨V, hV⟩ ⟨W, hW⟩ eVW).elim fun c sections ↦ ?_
  have hc := sections.1
  have hs := sections.2.1
  have ht := sections.2.2.1
  have target :=
    Scheme.Modules.exists_flatBaseChange_target_leray_comparison
      f g F I J p V W hV hW eVW D
  obtain ⟨E, hE, htarget⟩ := target
  obtain ⟨eH, heH, b0, hb0⟩ := htarget
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have edge :=
    Scheme.Modules.exists_affine_cohomology_section_equiv f F I p V hV D.source E hE
  obtain ⟨e, he⟩ := edge
  have hP := ordinaryHigherImage_isQuasicoherent f F inferInstance p
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
  have hk : Function.Bijective (k.comp t.toLinearMap) :=
    (hc P hP).comp
      ((TensorProduct.comm Γ(S, V) Γ(P, V) Γ(S', W)).symm.bijective.comp t.bijective)
  refine ⟨eH, LinearEquiv.ofBijective (k.comp t.toLinearMap) hk, b0, ?_, ?_⟩
  · intro s xi
    change c P hP (e xi ⊗ₜ[Γ(S, V)] s) = _
    have he' : e xi = D.sourceClass p (eH.symm xi) := by
      rw [heH]
      dsimp only [Scheme.Modules.FlatBaseChangeOpenChoices.sourceClass]
      exact he xi
    exact (ht P hP (e xi) s).trans (congrArg (fun z ↦ s •
      ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
        (Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
          V z)) he')
  · exact hb0
end AlgebraicGeometry
