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
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeAffineSource
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeAffineTarget

/-! # Normalized affine cohomology section dictionaries

Source: Stacks Project, Tags 02KH and 02N7; Tags 01E4 and 03FD for the
higher-direct-image and module/abelian cohomology identifications.
(blueprint: lem-weil-pbc-flat-base-change-affine-dictionary)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- Normalized affine section identifications, before choosing a resolution lift.
Source: Stacks Project, Tags 02KH (affine-local reduction), 01XJ, 01E4 and 03FD.
(blueprint: lem-weil-pbc-flat-base-change-affine-dictionary)

Proof: Set U = f inverse V and N = F restricted to U. The given D identifies
its resolutions with the restrictions of I and J to U and g' inverse U,
preserving the augmentations and the restriction-unit square. Compute module cohomology and
underlying abelian-sheaf cohomology on the same section complexes to obtain e.
Use the affine chart W = Spec B and V = Spec A and the cartesian square to
identify the coefficient on U_B with the restriction of g'^*F. The Leray edge
maps, together with quasi-coherence of higher direct images for qcqs maps and
affine vanishing, identify the sections of both higher direct images with
cohomology of their inverse-image opens. The affine tensor-pullback section
formula and e give a, with the stated pure-tensor normalization. The target
identification gives b. Compute the pullback on the common section complexes:
the restricted coefficient map is D.psi, so the module/abelian comparison
intertwines its cohomology map with H.baseChangeLinear. Restriction from g^-1 V
to W gives the last formula. Both identifications are linear: scalars act by
multiplication on the same complexes and all comparison maps commute with it.
The repaired target interface transports the canonical target comparison along
the normalized source lift, using flat cohomology base-change invertibility.
No resolution lift t or resolution-defined beta is used. Empty opens, zero
coefficients, and degree zero are covered by the same complexes and comparison maps. -/
theorem Scheme.Modules.exists_flatBaseChange_affine_dictionary
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
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∃ (eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) →ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W))
      (b : Scheme.Modules.HOver (Scheme.Modules.baseChangeSnd (S := Γ(S', W)) h)
        (Scheme.Modules.baseChangedModule (S := Γ(S', W)) h N) p →ₗ[Γ(S', W)] Γ(Q, W)),
      Function.Bijective a ∧ Function.Bijective b ∧
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (eH.symm xi)))) ∧
      (∀ xi : Scheme.Modules.HOver h N p,
        b (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
          Q.presheaf.map (homOfLE eVW).op
            (D.targetClass p
              (Scheme.Modules.moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (eH.symm xi)))) := by
  choose eH a ha ha_formula using
    Scheme.Modules.exists_flatBaseChange_affine_source f g F I J p V W hV hW eVW D
  choose b hb hb_formula using
    Scheme.Modules.exists_flatBaseChange_affine_target
      f g F I J p V W hV hW eVW D eH a ha ha_formula
  exact ⟨eH, a, b, ha, hb, ha_formula, hb_formula⟩

end AlgebraicGeometry
