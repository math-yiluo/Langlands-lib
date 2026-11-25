/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.CoefficientSourceAffineTensorPresentation
import WeilConjectures.AlgebraicGeometry.CoefficientTargetAffineTensorPresentation
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Affine bijectivity of normalized coefficient comparisons

Source: Stacks Project, Tags 02KE, 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A coefficient comparison morphism with the unit formula is bijective on affine opens.
This is a single-open statement: no tuples, face maps, or gluing are involved.
Source: Stacks Project, Tag 02KG (Lemma 30.5.1); Tags 01I9 and 01IA.
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-bijective).

Proof: Write A = Gamma(U,O), D = Gamma(Z,O), N = Gamma(Z,F), and
R = Gamma(B,O). The affine intersection base-change theorem shows that
W -> T' is affine. Hence W intersect f' inverse image B is affine, and it
is Z times_U B by the cartesian square and the stated equality for W.
The affine pullback section formula identifies the sections of M there
with (R tensor_A D) tensor_D N = R tensor_A N. The source is the pullback
to B of the associated A-module N, so the same formula identifies its
sections with R tensor_A N. Both identifications send 1 tensor s to the
restriction of the displayed generator section. Naturality of q under
B -> top and its linearity over Gamma(B,O) therefore identify q on every
r tensor s with the identity under these presentations. Such pure tensors
generate the tensor product, so q is conjugate to an additive equivalence
and is bijective. The argument includes empty Z and empty B, with zero
modules. It uses neither flatness nor any covering assumption. -/
theorem coefficientComparison_affine_bijective {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    ∀ q : H.obj (G.obj (op Z)) ⟶
        (pushforward (W.ι ≫ f')).obj (M.restrict W.ι),
      (∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
        (coefficientSupportIso f' M W ⊤).hom
          (q.app ⊤ (coefficientGenerator g _ s)) =
        M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ ⊤ ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) →
      ∀ B : T'.Opens, IsAffineOpen B → Function.Bijective (q.app B) := by
  classical
  dsimp only
  intro q hq B hB
  let N := (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
        ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
  let P := (pullback g).obj ((pullback U.toScheme.toSpecΓ).obj (tilde N))
  let M := (pullback g').obj F
  let Q := (pushforward (W.ι ≫ f')).obj (M.restrict W.ι)
  change P ⟶ Q at q
  change ∀ s : N, (coefficientSupportIso f' M W ⊤).hom
    (q.app ⊤ (coefficientGenerator g N s)) =
    M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ ⊤ ≤ W)).op
      (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s) at hq
  let : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
    (g.appLE ⊤ B (by simp)).hom.toAlgebra
  obtain ⟨a, ha⟩ := exists_coefficientSource_affine_tensor_presentation g N B hB
  obtain ⟨b, hb⟩ := exists_coefficientTarget_affine_tensor_presentation
    f F U hU Z hZ g g' f' sq W hW B hB
  have hgen (s : N) :
      q.app B (a.symm (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s)) =
        b.symm (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s) := by
    have hs : a.symm (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s) =
        P.presheaf.map (homOfLE le_top).op (coefficientGenerator g N s) := by
      exact a.injective ((a.apply_symm_apply _).trans (ha s).symm)
    refine (congrArg (q.app B) hs).trans ?_
    apply (ConcreteCategory.bijective_of_isIso (coefficientSupportIso f' M W B).hom).1
    have hn := congrArg (fun k ↦ k (coefficientGenerator g N s))
      (q.mapPresheaf.naturality (homOfLE (le_top : B ≤ ⊤)).op)
    simp only [ConcreteCategory.comp_apply] at hn
    change q.app B (P.presheaf.map (homOfLE le_top).op
        (coefficientGenerator g N s)) =
      Q.presheaf.map (homOfLE le_top).op
        (q.app ⊤ (coefficientGenerator g N s)) at hn
    refine (congrArg (coefficientSupportIso f' M W B).hom hn).trans ?_
    refine (coefficientSupportIso_naturality f' M W (homOfLE le_top) _).trans ?_
    refine (congrArg (M.presheaf.map (homOfLE (inf_le_inf le_rfl
      ((TopologicalSpace.Opens.map f'.base).map
        (homOfLE (le_top : B ≤ ⊤))).le)).op) (hq s)).trans ?_
    refine Eq.trans ?_ (hb s).symm
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  let qlin : Γ(P, B) →ₗ[Γ(T', B)] Γ(Q, B) := (q.val.app (op B)).hom
  change Γ(P, B) ≃ₗ[Γ(T', B)] (TensorProduct Γ(U.toScheme, ⊤) Γ(T', B) N) at a
  change Γ(Q, B) ≃ₗ[Γ(T', B)] (TensorProduct Γ(U.toScheme, ⊤) Γ(T', B) N) at b
  change ∀ s : N, qlin (a.symm (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s)) =
    b.symm (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s) at hgen
  have hcompare (t : TensorProduct Γ(U.toScheme, ⊤) Γ(T', B) N) :
      qlin (a.symm t) = b.symm t := by
    induction t using TensorProduct.inductionOn with
    | tmul r s =>
      have ht : TensorProduct.tmul Γ(U.toScheme, ⊤) r s =
          r • (TensorProduct.tmul Γ(U.toScheme, ⊤) (1 : Γ(T', B)) s) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, a.symm.map_smul, qlin.map_smul, hgen, b.symm.map_smul]
    | add t t' ht ht' =>
      rw [a.symm.map_add, qlin.map_add, ht, ht', b.symm.map_add]
  have heq : (fun x ↦ q.app B x) = fun x ↦ b.symm (a x) := by
    funext x
    change qlin x = b.symm (a x)
    simpa only [a.symm_apply_apply] using hcompare (a x)
  change Function.Bijective (fun x ↦ q.app B x)
  rw [heq]
  exact b.symm.bijective.comp a.bijective

end
end AlgebraicGeometry.Scheme.Modules
