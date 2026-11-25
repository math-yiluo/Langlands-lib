/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineComparisonMap
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineSectionComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.RingSheafificationRestrictedStalks

/-! # Stalk comparison on an affine chart for the symmetric algebra

Source: Stacks Project, Modules, Lemma 01CH and Schemes, Lemma 01I8.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-comparison-stalks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The tilde comparison is bijective on every stalk of the affine chart.
Source: Stacks Project, Modules, Lemmas 01CG and 01CH; Schemes, Lemma 01I8;
Algebra, Lemma 0C6F. This is step 6 of the affine symmetric algebra comparison.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-comparison-stalks).

Proof: write R = O_X(W), M = F(W), A = Sym_R(M), and S for the restriction of the
ring sheafification to Spec R. For each smaller affine V, quasi-coherent affine section
base change gives F(V) = O(V) tensor_R M. Symmetric algebra base change then gives a
bijection lambda_V : O(V) tensor_R A -> Sym_{O(V)}(F(V)). Tilde section base change
gives a second bijection beta_V : O(V) tensor_R A -> tilde(A)(V). Both send r tensor a
to r times the restriction of a. The comparison alpha satisfies
alpha_V beta_V = theta_V lambda_V: its equality on 1 tensor a follows from the adjunction
and naturality, and linearity gives equality on all tensors. These identifications commute
with restriction, since their formulas agree on pure tensors.
The ring sheafification unit theta is bijective on stalks (forgetting to abelian groups
commutes with sheafification). Affine neighbourhoods inside W are cofinal. For surjectivity
at x, lift a target germ through theta_x, represent the lift on an affine V, write its
representative as lambda_V(c), and use alpha_V(beta_V(c)) as its lift through alpha_x.
For injectivity, represent a source germ on an affine V as beta_V(c). If its image under
alpha_x is zero, injectivity of theta_x makes the germ of lambda_V(c) zero. Restrict to
an affine neighbourhood V' where lambda_V(c) vanishes. Restriction compatibility and
injectivity of lambda_V' force the restricted tensor c' to be zero. Thus beta_V'(c')
is zero, so the original source germ was zero. For two germs with equal images, apply
this zero-kernel argument to their difference. No finiteness or separatedness is used. -/
theorem affineComparison_stalk_bijective {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (x : Spec Γ(X, W)) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf (Spec Γ(X, W))).map (affineComparison F hW))) := by
  let P := hW.fromSpec.opensFunctor.op ⋙ presheaf F ⋙
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u})
  let T := (Scheme.Modules.toPresheaf (Spec Γ(X, W))).obj
    (tilde (R := Γ(X, W)) (ModuleCat.of Γ(X, W) (sections F (op W))))
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let B : (Spec Γ(X, W)).affineOpens → (Spec Γ(X, W)).Opens := Subtype.val
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    simpa only [B, Subtype.range_coe] using (Spec Γ(X, W)).isBasis_affineOpens
  obtain ⟨δ, hδ, hδcomp⟩ := exists_affineSectionComparison F hW
  let TS : TopCat.Sheaf AddCommGrpCat.{u} (Spec Γ(X, W)) :=
    ⟨T, (tilde (R := Γ(X, W))
      (ModuleCat.of Γ(X, W) (sections F (op W)))).isSheaf⟩
  let γ : P ⟶ T := TopCat.Sheaf.restrictHomEquivHom P TS hB δ
  have hγapp (V : (Spec Γ(X, W)).affineOpens) :
      γ.app (op V.1) = δ.app (op V) :=
    TopCat.Sheaf.extend_hom_app P TS hB δ V
  have hγ (V : (Spec Γ(X, W)).Opens) (hV : IsAffineOpen V) :
      Function.Bijective (γ.app (op V)) := by
    change Function.Bijective (γ.app (op (B ⟨V, hV⟩)))
    rw [hγapp ⟨V, hV⟩]
    exact hδ ⟨V, hV⟩
  have hcomp : γ ≫
      (Scheme.Modules.toPresheaf (Spec Γ(X, W))).map (affineComparison F hW) =
      CategoryTheory.Functor.whiskerLeft hW.fromSpec.opensFunctor.op
        (CategoryTheory.Functor.whiskerRight
          (toSheafify (Opens.grothendieckTopology X) (presheaf F))
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u})) := by
    apply TopCat.Sheaf.hom_ext P
      ⟨_, (Scheme.Modules.restrict (algebra F).toModule hW.fromSpec).isSheaf⟩ hB
    intro V
    change γ.app (op V.1) ≫ _ = _
    rw [hγapp]
    exact hδcomp V
  have hγx : Function.Bijective (K.map γ) := by
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
      (Spec Γ(X, W)).isBasis_affineOpens (fun V hV ↦ (hγ V hV).1) x, ?_⟩
    intro t
    obtain ⟨V, hxV, hV, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
        (Spec Γ(X, W)).isBasis_affineOpens T x t
    obtain ⟨a, ha⟩ := (hγ V hV).2 s
    refine ⟨TopCat.Presheaf.germ P V x hxV a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha]
  have hθ := ringSheafification_restricted_stalk_bijective hW.fromSpec (presheaf F) x
  have hwhole : Function.Bijective
      (K.map (γ ≫ (Scheme.Modules.toPresheaf (Spec Γ(X, W))).map
        (affineComparison F hW))) := by
    rw [hcomp]
    exact hθ
  rw [Functor.map_comp] at hwhole
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := hγx.2 a
    obtain ⟨b', rfl⟩ := hγx.2 b
    exact congrArg (K.map γ) (hwhole.1 hab)
  · intro t
    obtain ⟨a, ha⟩ := hwhole.2 t
    exact ⟨K.map γ a, ha⟩

end AlgebraicGeometry.SymmetricAlgebraSheaf
