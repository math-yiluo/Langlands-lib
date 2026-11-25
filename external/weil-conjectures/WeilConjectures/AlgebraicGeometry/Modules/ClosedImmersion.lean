/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Modules under a closed immersion

Let `i : X ⟶ Y` be a closed immersion. The pushforward `i_*` is faithful, since every open
subset of `X` is the preimage of an open subset of `Y`; so global generation of an `𝒪_X`-module
`ℳ` can be checked on `i_* ℳ`. The pushforward of a quasi-coherent module is quasi-coherent,
and, if `Y` is locally noetherian, the pushforward of a coherent module is coherent.

As in the rest of the project, "coherent" is spelled as `SheafOfModules.IsQuasicoherent`
together with `SheafOfModules.IsFinitePresentation`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.faithful_pushforward_of_isClosedImmersion`: `i_*` is
  faithful.
- `AlgebraicGeometry.Scheme.Modules.GeneratingSections.ofPushforward`: if `i_* ℳ` is generated
  by global sections, so is `ℳ`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion` and
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isClosedImmersion`:
  `i_*` preserves quasi-coherent and coherent modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- For an affine open `U`, the global sections of the restriction of `M` along
`hU.fromSpec : Spec Γ(X, U) ⟶ X` are the sections of `M` over `U`, as `Γ(X, U)`-modules. -/
noncomputable def sectionsTopRestrictFromSpecEquiv {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) where
  toFun x := M.presheaf.map (homOfLE (by rw [Hom.image_top_eq_opensRange,
    hU.opensRange_fromSpec])).op ((M.restrictAppIso hU.fromSpec ⊤).hom x)
  invFun y := (M.restrictAppIso hU.fromSpec ⊤).inv
    (M.presheaf.map (homOfLE (hU.fromSpec_image_le ⊤)).op y)
  map_add' x y := by simp
  map_smul' r x := by
    dsimp only
    rw [restrictAppIso_fromSpec_smul, map_smul, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, RingHom.id_apply]
  left_inv x := by
    dsimp only
    rw [← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op (hU.fromSpec ''ᵁ ⊤) ⟶ _) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, Iso.hom_inv_id_apply]
  right_inv y := by
    dsimp only
    rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- Let `i : X ⟶ Y` be a morphism of schemes and `V` an open of `Y` such that
`i.app V : Γ(Y, V) ⟶ Γ(X, i ⁻¹ᵁ V)` is surjective. If `Γ(F, i ⁻¹ᵁ V)` is a finite
`Γ(X, i ⁻¹ᵁ V)`-module, then `Γ(i_* F, V)`, which is the same group with `Γ(Y, V)` acting through
`i.app V`, is a finite `Γ(Y, V)`-module. -/
theorem finite_sections_pushforward_of_surjective {X Y : Scheme.{u}} (i : X ⟶ Y) (F : X.Modules)
    (V : Y.Opens) (hi : Function.Surjective (i.app V))
    [Module.Finite Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V)] :
    Module.Finite Γ(Y, V) Γ((pushforward i).obj F, V) := by
  let := (i.app V).hom.toAlgebra
  let : Module Γ(Y, V) Γ(F, i ⁻¹ᵁ V) := Module.compHom _ (i.app V).hom
  have : IsScalarTower Γ(Y, V) Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  have : Module.Finite Γ(Y, V) Γ(X, i ⁻¹ᵁ V) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hi
  have := Module.Finite.trans Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) (R := Γ(Y, V))
  exact Module.Finite.equiv
    { AddEquiv.refl _ with map_smul' _ _ := rfl :
      Γ(F, i ⁻¹ᵁ V) ≃ₗ[Γ(Y, V)] Γ((pushforward i).obj F, V) }

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- **Pushforward along a topological embedding is faithful.** Every open subset of `X` is
the preimage `i ⁻¹ᵁ V` of an open subset `V` of `Y`, and the sections of `i_* ℳ` over `V` are the
sections of `ℳ` over `i ⁻¹ᵁ V`; so a morphism `φ` is determined by `i_* φ`. -/
lemma faithful_pushforward_of_isInducing {i : X ⟶ Y} (hi : Topology.IsInducing i) :
    (pushforward i).Faithful where
  map_injective {M N} φ ψ h := by
    refine hom_ext _ _ fun U ↦ ?_
    obtain ⟨V, hV, hUV⟩ := hi.isOpen_iff.1 U.2
    obtain rfl : i ⁻¹ᵁ ⟨V, hV⟩ = U := TopologicalSpace.Opens.ext hUV
    rw [← pushforward_map_app, ← pushforward_map_app, h]

/-- **Pushforward along a closed immersion is faithful.** -/
instance faithful_pushforward_of_isClosedImmersion : (pushforward i).Faithful :=
  faithful_pushforward_of_isInducing i.isClosedEmbedding.isInducing

/-- **Generating sections descend along a closed immersion.** If `i_* ℳ` is generated by global
sections, so is `ℳ`: the global sections of `i_* ℳ` are those of `ℳ`, and the adjoint
`free I ≅ i^* (free I) ⟶ ℳ` of an epimorphism `free I ⟶ i_* ℳ` is an epimorphism, since
`i_*` is faithful and so reflects epimorphisms. -/
noncomputable def GeneratingSections.ofPushforward {M : X.Modules}
    (σ : SheafOfModules.GeneratingSections ((pushforward i).obj M)) :
    SheafOfModules.GeneratingSections M :=
  have : Epi ((Scheme.Modules.pullback i).map σ.π ≫
      (pullbackPushforwardAdjunction i).counit.app M) := by
    refine (pushforward i).epi_of_epi_map ?_
    have : @Epi Y.Modules _ _ _ σ.π := σ.epi
    have h : σ.π = (pullbackPushforwardAdjunction i).unit.app _ ≫ (pushforward i).map
        ((Scheme.Modules.pullback i).map σ.π ≫
          (pullbackPushforwardAdjunction i).counit.app M) := by
      simp
    rw [h] at this
    exact epi_of_epi ((pullbackPushforwardAdjunction i).unit.app _) _
  have := (pullbackPushforwardAdjunction i).leftAdjoint_preservesColimits
  .ofEpiFree ((SheafOfModules.mapFreeIso (Scheme.Modules.pullback i) σ.I
    (pullbackObjUnitIso i).symm).hom ≫
    (Scheme.Modules.pullback i).map σ.π ≫ (pullbackPushforwardAdjunction i).counit.app M)

/-- **The pushforward along a closed immersion of a quasi-coherent module is
quasi-coherent.** Over an affine open `Spec R` of `Y`, with preimage `Spec (R / I)`, the
pushforward of the module associated with an `R / I`-module `M` is the module associated with
`M` regarded as an `R`-module. Here it is the case of an affine morphism,
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom`. -/
theorem isQuasicoherent_pushforward_of_isClosedImmersion (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] :
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) ((pushforward i).obj F) :=
  isQuasicoherent_pushforward_of_isAffineHom i F

/-- **The pushforward along a closed immersion of a coherent module is coherent**, for a
locally noetherian target `Y`. Over an affine open `Spec R` of `Y`, with preimage
`Spec (R / I)`, the module of sections of `ℱ` is finite over `R / I`, hence finite over the
noetherian ring `R`, hence finitely presented. -/
theorem isFinitePresentation_pushforward_of_isClosedImmersion [IsLocallyNoetherian Y]
    (F : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) ((pushforward i).obj F) := by
  have : ((pushforward i).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isClosedImmersion i F
  let ι := {V : Y.Opens // IsAffineOpen V}
  have (j : ι) : Module.Finite Γ(X, i ⁻¹ᵁ j.1) Γ(F, i ⁻¹ᵁ j.1) :=
    finite_sections_of_isFinitePresentation F (j.2.preimage i)
  have (j : ι) : IsNoetherianRing Γ(Y, j.1) :=
    IsLocallyNoetherian.component_noetherian ⟨j.1, j.2⟩
  have (j : ι) : Module.Finite Γ(Y, j.1)
      Γ(((pushforward i).obj F).restrict j.2.fromSpec, ⊤) := by
    have := finite_sections_pushforward_of_surjective i F j.1 (i.app_surjective j.1 j.2)
    exact Module.Finite.equiv (sectionsTopRestrictFromSpecEquiv _ j.2).symm
  choose P hP using fun j : ι ↦
    exists_presentation_isFinite (((pushforward i).obj F).restrict j.2.fromSpec)
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ (fun j : ι ↦ j.2.fromSpec) ?_ P
  refine eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (Set.mem_univ y)
  exact ⟨⟨V, hV⟩, by rwa [IsAffineOpen.opensRange_fromSpec]⟩

end AlgebraicGeometry.Scheme.Modules
