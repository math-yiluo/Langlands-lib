/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.AffineQuotientRestrictedIso

/-!
# Sheafifying an affine quotient resolution

Source: Stacks Project, Tag 068C, affine-local resolution argument
(blueprint: lem-sc-affine-quotient-resolution-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An algebraic resolution of an affine quotient sheafifies to a resolution of the
restricted pushforward of the closed subscheme's structure sheaf.
Source: Stacks Project, Tag 068C, affine-local reduction and Koszul resolution
(blueprint: lem-sc-affine-quotient-resolution-sheafification).

Proof: The equation for the quotient presentation identifies the inverse image of
`U` with `Spec (A/I)` over `Spec A`, where `A = Γ(Y,U)`. On a basic open `D(g)`, the
restricted pushforward of the structure sheaf has sections `(A/I)_g`, including
its `A_g`-module action. These identifications commute with restriction maps and
therefore give an isomorphism with `tilde(A/I)` transported along `hU.isoSpec`.
The tilde functor is exact: its stalk at a prime is localization of modules, and
localization is exact. Restriction along the affine chart is an equivalence, hence
exact. Apply these functors to the given augmentation; homology commutes with an
exact functor, so the resulting map remains a quasi-isomorphism. Identify the
image of the single complex with the single complex of the image module, then
compose with the single complex of the preceding module isomorphism. This gives
the asserted chain map and quasi-isomorphism. No bound or freeness is needed. -/
theorem exists_affine_quotient_sheafified_resolution {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.Opens) (hU : IsAffineOpen U) (I : Ideal (Γ(Y, U)))
    (e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
      Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)))
    (he : i ∣_ U ≫ U.toSpecΓ =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ)
    (ε : K ⟶ (ChainComplex.single₀ (ModuleCat (Γ(Y, U) : Type u))).obj
      (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)))
    [QuasiIso ε] :
    ∃ q : ((tilde.functor Γ(Y, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K ⟶
        (ChainComplex.single₀ U.toScheme.Modules).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
      QuasiIso q := by
  obtain ⟨eiso⟩ := affine_quotient_restricted_iso i U hU I e he
  let F := tilde.functor Γ(Y, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom
  let a := ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ε)
  let s := HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0
  let q₁ := a ≫ (s.hom.app (ModuleCat.of (Γ(Y, U) : Type u)
    ((Γ(Y, U) : Type u) ⧸ I)))
  let q₂ := q₁ ≫ (ChainComplex.single₀ _).map eiso.hom
  let tilde_preservesKernel : ∀ (R : CommRingCat.{u})
      {M N : ModuleCat.{u} R} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (tilde.functor R) := by
    intro R M N f
    let T := tilde.functor R
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := R)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    let : T.IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := R) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := R) N).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := R) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) k
    let e : T.obj ((moduleSpecΓFunctor (R := R)).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := R) k)
    let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
    let c := Limits.KernelFork.ofι t ht
    have hc : Limits.IsLimit (c.map T) := by
      apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
      exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
    have hc' : Limits.IsLimit c :=
      Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact Limits.preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  let T := tilde.functor Γ(Y, U)
  let : ∀ {M N : ModuleCat.{u} (Γ(Y, U) : Type u)} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) T :=
    fun {_ _} f ↦ tilde_preservesKernel (Γ(Y, U)) f
  let : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor hU.isoSpec.hom) := by
    infer_instance
  let : PreservesFiniteColimits (Scheme.Modules.restrictFunctor hU.isoSpec.hom) := by
    infer_instance
  let : F.Additive := by
    change (tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).Additive
    infer_instance
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom)
    exact comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom)
    exact comp_preservesFiniteColimits _ _
  have : QuasiIso a := by infer_instance
  refine ⟨q₂, ?_⟩
  dsimp [q₂, q₁, a, s]
  infer_instance

end AlgebraicGeometry
