/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Topology.Sheaves.CechFlasque

/-!
# Higher direct images along affine morphisms vanish

For an affine morphism `f : X ⟶ T` and a quasi-coherent `𝒪_X`-module `ℱ`, the higher direct
images `R^q f_* ℱ` vanish for `q > 0`
(`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isAffineHom`) and `f_* ℱ` is
quasi-coherent (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

section AffineMorphism

/-- The underlying abelian sheaf of an injective `𝒪_X`-module is Čech-acyclic on affine opens,
since it is flasque. -/
lemma cechAcyclicOnAffines_toAb_of_injective (I : X.Modules) [Injective I] :
    cechAcyclicOnAffines X ((toAb X).obj I) :=
  have := isFlasque_of_injective I
  fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₂`
Čech-acyclic on affine opens, `M₃` is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_toAb_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((toAb X).obj S.X₁))
    (h₂ : cechAcyclicOnAffines X ((toAb X).obj S.X₂)) :
    cechAcyclicOnAffines X ((toAb X).obj S.X₃) :=
  cechAcyclicOnAffines_X₃ (S := S.map (toAb X)) (hS.map_of_exact (toAb X)) h₁ h₂

/-- Let `f : X ⟶ T` be affine. The pushforward along `f` of a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules, with `M₁` Čech-acyclic on affine opens, is right
exact: `M₂ ⟶ M₃` is surjective on the sections over the affine opens `f ⁻¹ᵁ V`, `V` affine. -/
lemma epi_pushforward_map_g_of_cechAcyclicOnAffines (f : X ⟶ T) [IsAffineHom f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((toAb X).obj S.X₁)) : Epi ((pushforward f).map S.g) := by
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  obtain ⟨z, hz⟩ := surjective_app_of_cechAcyclicOnAffines (hS.map_of_exact (toAb X)) h₁
    (IsAffineOpen.preimage hV f) (S.X₃.presheaf.map (homOfLE (f.preimage_mono hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

/-- **The higher direct images along an affine morphism vanish.** Let `f : X ⟶ T` be affine
and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ = 0` for `q > 0`.

The underlying abelian sheaves of quasi-coherent modules and of injective `𝒪_X`-modules, which
are flasque, are Čech-acyclic on the affine opens of `X`, and this class is stable under
cokernels of monomorphisms. A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` in this
class is surjective on the sections over the affine opens `f ⁻¹ᵁ V`, `V` affine in `T`, so `f_*`
keeps it short exact; hence `ℱ` is `f_*`-acyclic by dimension shifting
(`CategoryTheory.Functor.rightAcyclic_of_epi_map_g`). This is the vanishing of
`H^q(f⁻¹ V, ℱ)` for the affine schemes `f⁻¹ V` of the blueprint proof, in Čech form.

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isZero_higherDirectImage_of_isAffineHom (f : X ⟶ T) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {q : ℕ} (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj ℱ) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have h : (pushforward f).rightAcyclic ℱ := Functor.rightAcyclic_of_epi_map_g (pushforward f)
    (fun M ↦ cechAcyclicOnAffines X ((toAb X).obj M))
    (fun I _ ↦ cechAcyclicOnAffines_toAb_of_injective I)
    (fun _ hS h₁ h₂ ↦ cechAcyclicOnAffines_toAb_X₃ hS h₁ h₂)
    (fun S hS h₁ ↦ epi_pushforward_map_g_of_cechAcyclicOnAffines f hS h₁)
    (cechAcyclicOnAffines_of_isQuasicoherent ℱ)
  exact h q

/-- **The pushforward along an affine morphism is quasi-coherent.** For `f : X ⟶ T` affine and
`ℱ` quasi-coherent, `f_* ℱ` is quasi-coherent: for an affine open `V` of `T` and `g ∈ Γ(T, V)`,
the preimage `f ⁻¹ᵁ V` is affine with `f ⁻¹ᵁ D(g) = D(f^♯ g)`, so `Γ(D(g), f_* ℱ)` is the
localization of `Γ(V, f_* ℱ) = Γ(f ⁻¹ᵁ V, ℱ)` at `g`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen`).

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isQuasicoherent_pushforward_of_isAffineHom (f : X ⟶ T) [IsAffineHom f] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((pushforward f).obj ℱ).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW g s ↦ ?_) (fun W hW g t ht ↦ ?_)
  · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq ℱ (hW.preimage f) (f.app W g)
      (f.preimage_basicOpen g).symm (f.preimage_mono (T.basicOpen_le g)) s
    refine ⟨n, t, ht.trans ?_⟩
    have h : f.app (T.basicOpen g) (T.presheaf.map (homOfLE (T.basicOpen_le g)).op g) =
        X.presheaf.map (homOfLE (f.preimage_mono (T.basicOpen_le g))).op (f.app W g) := by
      rw [← ConcreteCategory.comp_apply, f.naturality]
      rfl
    rw [← h, ← map_pow]
    rfl
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq ℱ (hW.preimage f) (f.app W g)
      (f.preimage_basicOpen g).symm (f.preimage_mono (T.basicOpen_le g)) t ht
    rw [← map_pow] at hn
    exact ⟨n, hn⟩

end AffineMorphism

end AlgebraicGeometry.Scheme.Modules
