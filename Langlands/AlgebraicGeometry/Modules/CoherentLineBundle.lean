import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.RestrictTensorProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Local finiteness of affine sections and tensoring by line bundles -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace HasFiniteAffineSections

variable {X Y : Scheme.{u}} {M : X.Modules}

/-- Restriction along an open immersion preserves finite affine sections. -/
lemma restrict (hM : HasFiniteAffineSections M) (f : Y ⟶ X) [IsOpenImmersion f] :
    HasFiniteAffineSections (M.restrict f) := by
  intro U
  have := hM ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  let g : Γ(M, f ''ᵁ U.1) →ₛₗ[(f.appIso U.1).hom.hom] Γ(M.restrict f, U.1) :=
    { toFun := (M.restrictAppIso f U.1).inv
      map_add' := map_add _
      map_smul' := by
        intro r s
        exact Scheme.Modules.smul_restrictAppIso_inv_apply f M U.1 r s }
  exact Module.Finite.of_surjective g
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f U.1).inv).surjective

/-- Finite sections of a restriction give finite sections on contained affine opens. -/
lemma finite_of_restrict (O : X.Opens) (hM : HasFiniteAffineSections (M.restrict O.ι))
    (U : X.affineOpens) (hUO : U.1 ≤ O) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  let V := O.ι ⁻¹ᵁ U.1
  have e : O.ι ''ᵁ V = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUO
  have hV : IsAffineOpen V :=
    O.ι.isAffineOpen_iff_of_isOpenImmersion.1 (e.symm ▸ U.2)
  have := hM ⟨V, hV⟩
  suffices Module.Finite Γ(X, O.ι ''ᵁ V) Γ(M, O.ι ''ᵁ V) by rwa [e] at this
  let g : Γ(M.restrict O.ι, V) →ₛₗ[(O.ι.appIso V).inv.hom] Γ(M, O.ι ''ᵁ V) :=
    { toFun := (M.restrictAppIso O.ι V).hom
      map_add' := map_add _
      map_smul' := Scheme.Modules.smul_restrictAppIso_hom_apply O.ι M V }
  exact Module.Finite.of_surjective g
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso O.ι V).hom).surjective

end HasFiniteAffineSections

/-- Each point has an affine neighborhood with finite module sections. -/
def HasLocallyFiniteSections {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
    Module.Finite Γ(X, U) Γ(M, U)

namespace AffineSections

open Langlands.Cohomology AffineVanishing

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

section Basic

variable (f : Γ(X, U))

local instance : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
  (rres (X.basicOpen_le f)).toAlgebra

local instance : Module Γ(X, U) Γ(M, X.basicOpen f) :=
  Module.compHom Γ(M, X.basicOpen f) (rres (X.basicOpen_le f))

local instance : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Restriction to a basic open, linear over the original ring of sections. -/
def basicRestriction : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := Cech.res (X.basicOpen_le f)
  map_add' := map_add _
  map_smul' := res_smul M (X.basicOpen_le f)

lemma isLocalizedModule_basicRestriction (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] :
    IsLocalizedModule.Away f (basicRestriction M f) := by
  have := hU.isLocalization_basicOpen f
  have hM := QuasicoherentLocal.isLocalizingAt_of_isQuasicoherent hU M
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · rw [← (Algebra.lsmul Γ(X, U) (A := Γ(X, X.basicOpen f))
      Γ(X, U) Γ(M, X.basicOpen f)).commutes]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen f)) f).map _
  · intro s
    obtain ⟨n, t, ht⟩ := hM.exists_res_eq f s
    refine ⟨n, t, ?_⟩
    change rres (X.basicOpen_le f) (f ^ n) • s = _
    rw [map_pow]
    exact ht.symm
  · exact hM.exists_pow_smul_eq_zero f

/-- Finite sections on an affine open remain finite on each basic open. -/
lemma finite_basicOpen (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent]
    [Module.Finite Γ(X, U) Γ(M, U)] :
    Module.Finite Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) := by
  have := hU.isLocalization_basicOpen f
  have := isLocalizedModule_basicRestriction M f hU
  exact Module.Finite.of_isLocalizedModule (Submonoid.powers f) (basicRestriction M f)

/-- Finiteness descends from a basic-open cover of an affine open. -/
lemma finite_of_basicCover (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent]
    (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤)
    (hfinite : ∀ g : s, Module.Finite Γ(X, X.basicOpen g.val) Γ(M, X.basicOpen g.val)) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have (g : s) := hU.isLocalization_basicOpen g.val
  have (g : s) := isLocalizedModule_basicRestriction M g.val hU
  exact Module.Finite.of_localizationSpan' s hs
    (fun g => basicRestriction M g.val) hfinite

end Basic

end AffineSections

namespace HasLocallyFiniteSections

variable {X : Scheme.{u}} {M : X.Modules}

/-- Finiteness on open neighborhoods can be refined to affine neighborhoods. -/
lemma of_locally_finiteAffineSections
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ HasFiniteAffineSections (M.restrict O.ι)) :
    HasLocallyFiniteSections M := by
  intro x
  obtain ⟨O, hxO, hfinite⟩ := h x
  obtain ⟨U, hU, hxU, hUO⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxO
  exact ⟨U, hU, hxU, hfinite.finite_of_restrict O ⟨U, hU⟩ hUO⟩

/-- Finite sections on every affine open give pointwise affine neighborhoods. -/
lemma of_finiteAffineSections (hM : HasFiniteAffineSections M) :
    HasLocallyFiniteSections M := by
  intro x
  obtain ⟨U, hU, hx, -⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hU, hx, hM ⟨U, hU⟩⟩

/-- For a quasi-coherent module, finite affine sections are a local property. -/
lemma finiteAffineSections (hM : HasLocallyFiniteSections M) [M.IsQuasicoherent] :
    HasFiniteAffineSections M := by
  intro U
  let s : Set Γ(X, U.1) :=
    {f | Module.Finite Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)}
  have hs : U.1 ≤ ⨆ f : s, X.basicOpen f.val := by
    intro x hx
    obtain ⟨V, hV, hxV, hfinite⟩ := hM x
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 hV x ⟨hx, hxV⟩
    have := hfinite
    have hf : f ∈ s := by
      dsimp [s]
      rw [hfg]
      exact AffineSections.finite_basicOpen M g hV
    exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  exact AffineSections.finite_of_basicCover M U.2 s
    (U.2.self_le_iSup_basicOpen_iff.1 hs) (fun g => g.property)

end HasLocallyFiniteSections

open Langlands.Scheme.Modules

/-- A local trivialization of the second factor identifies the tensor with the first. -/
def tensorRestrictionTrivialization {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (tensorObj M N).restrict U.ι ≅ M.restrict U.ι := by
  have := isIso_restrictTensorHom U M N
  exact (asIso (restrictTensorHom U M N)).symm ≪≫
    (tensorFunctor U.toScheme).mapIso ((Iso.refl (M.restrict U.ι)).prod e) ≪≫
      tensorRightUnitor (M.restrict U.ι)

namespace QuasicoherentLocal

/-- Tensoring a quasi-coherent module with a locally free rank-one module
preserves quasi-coherence. -/
lemma isQuasicoherent_tensor_lineBundle {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] (hN : Picard.IsLocallyFreeRankOne N) :
    (tensorObj M N).IsQuasicoherent := by
  classical
  choose U hx e using hN
  have hcover : (_root_.Opens.grothendieckTopology X).CoversTop U := by
    apply (_root_.Opens.coversTop_iff X U).2
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.2 ⟨x, hx x⟩
  have (x : X) : ((tensorObj M N).restrict (U x).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U x).toScheme.ringCatSheaf).prop_of_iso
      (tensorRestrictionTrivialization M N (U x) (e x).some).symm inferInstance
  have (x : X) : ((tensorObj M N).over (U x)).IsQuasicoherent :=
    isQuasicoherent_over_of_restrict _ _
  exact SheafOfModules.IsQuasicoherent.of_coversTop (tensorObj M N) U hcover

end QuasicoherentLocal

namespace HasFiniteAffineSections

/-- Tensoring with a locally free rank-one module preserves finite affine sections. -/
lemma tensor_lineBundle {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteAffineSections M) [M.IsQuasicoherent]
    (hN : Picard.IsLocallyFreeRankOne N) :
    HasFiniteAffineSections (tensorObj M N) := by
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M N hN
  apply HasLocallyFiniteSections.finiteAffineSections
  apply HasLocallyFiniteSections.of_locally_finiteAffineSections
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hN x
  exact ⟨U, hxU, (hM.restrict U.ι).of_iso (tensorRestrictionTrivialization M N U e).symm⟩

end HasFiniteAffineSections

end Langlands.AlgebraicGeometry.Modules
