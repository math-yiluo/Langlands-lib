import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof

/-!
# Vanishing of higher direct images from cohomology over preimages of basic opens

For an open `U` of a scheme `X`, `openCohomology U n` is the cohomology `Hⁿ(U, M|_U)` of the
restriction of an `𝒪_X`-module to `U`. If `f : X ⟶ Y` is a morphism of schemes, `V` is an open
of `Y`, `B` is a basis of the topology of `Y`, and `Hⁿ(f⁻¹ U, M) = 0` for every `U ∈ B` contained
in `V`, then `Rⁿ f_* M` restricts to zero on `V`. In particular, if `Hⁿ(f⁻¹ U, M) = 0` for every
affine open `U` of `Y`, then `Rⁿ f_* M = 0`.

The proof is a dimension shift along `0 ⟶ M ⟶ I ⟶ I / M ⟶ 0` with `I` injective. Injective
modules are flasque, flasque modules stay flasque after restriction to an open, and flasque
modules have vanishing higher cohomology. In degree `0` and `1` the sheaf property and local
surjectivity are used directly.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}}

/-- The cohomology `Hⁿ(U, M|_U)` of the restriction of an `𝒪_X`-module `M` to an open `U`, as a
`Γ(U, ⊤)`-module. -/
noncomputable def openCohomology (U : X.Opens) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(U, ⊤) :=
  Scheme.Modules.restrictFunctor U.ι ⋙ cohomology U n

namespace OpenCohomologyVanishing

open Langlands.Cohomology.DerivedPlus PushforwardInjectiveAcyclic

/-- Pushforward of sheaves of modules along a continuous functor between small sites is left
exact, since it is computed on underlying presheaves, where it is a right adjoint. -/
lemma preservesFiniteLimits_pushforward {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  have h1 : (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top (F := F) (R := R.obj) φ.hom)
  have h2 : PreservesFiniteLimits (PresheafOfModules.pushforward.{u} φ.hom) := inferInstance
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.forget _) :=
    inferInstanceAs
      (PreservesFiniteLimits (SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward φ.hom))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget _)

instance (U : X.Opens) : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
  preservesFiniteLimits_pushforward _

/-- The restriction of a flasque module to an open is flasque. -/
lemma isFlasque_restrict (U : X.Opens) (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf where
  epi i := by
    rw [show i = i.unop.op from rfl, Scheme.Modules.restrict_map M U.ι i.unop]
    exact TopCat.Presheaf.IsFlasque.epi _

/-- A module whose sections are all trivial is zero. -/
lemma isZero_of_subsingleton (N : X.Modules) (h : ∀ U : X.Opens, Subsingleton Γ(N, U)) :
    IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

/-- A section which vanishes locally vanishes. -/
lemma eq_zero_of_locally_eq_zero (N : Y.Modules) {O : Y.Opens} (s : Γ(N, O))
    (h : ∀ y ∈ O, ∃ (O' : Y.Opens) (i : O' ⟶ O), y ∈ O' ∧ N.presheaf.map i.op s = 0) :
    s = 0 := by
  choose O' i hy hs using h
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨N.presheaf, N.isSheaf⟩
  refine F.eq_of_locally_eq' (U := fun y : O => O' y.1 y.2) O (fun y => i y.1 y.2) ?_ s 0 ?_
  · intro y hy'
    exact Opens.mem_iSup.2 ⟨⟨y, hy'⟩, hy y hy'⟩
  · intro y
    change N.presheaf.map _ s = N.presheaf.map _ 0
    rw [hs, map_zero]

/-- If `N₁` has no nonzero sections over opens contained in `V` and `φ : N₁ ⟶ N₂` is an
epimorphism, then neither has `N₂`. -/
lemma eq_zero_of_epi {N₁ N₂ : Y.Modules} (φ : N₁ ⟶ N₂) [Epi φ] {V : Y.Opens}
    (h : ∀ O ≤ V, ∀ s : Γ(N₁, O), s = 0) (O : Y.Opens) (hO : O ≤ V) (t : Γ(N₂, O)) :
    t = 0 := by
  have hφ := (TopCat.Presheaf.isLocallySurjective_iff _).1
    (ClosedImmersionHigherDirectImageVanishing.isLocallySurjective_of_epi φ)
  refine eq_zero_of_locally_eq_zero N₂ t fun y hy => ?_
  obtain ⟨O', hO', ⟨s, hs⟩, hy'⟩ := hφ O t y hy
  refine ⟨O', homOfLE hO', hy', ?_⟩
  rw [h O' (hO'.trans hO) s, map_zero] at hs
  exact hs.symm

/-- Let `φ ≫ ψ = 0` with `ψ` an epimorphism, and suppose that over opens contained in `V`,
sections of `N₂` are locally in the image of `φ`. Then `N₃` has no nonzero sections over opens
contained in `V`. -/
lemma eq_zero_of_comp_eq_zero {N₁ N₂ N₃ : Y.Modules} {φ : N₁ ⟶ N₂} {ψ : N₂ ⟶ N₃}
    (hφψ : φ ≫ ψ = 0) [Epi ψ] {V : Y.Opens}
    (hφ : ∀ O ≤ V, ∀ t : Γ(N₂, O), ∀ y ∈ O,
      ∃ (O' : Y.Opens) (i : O' ⟶ O), y ∈ O' ∧ ∃ s, φ.app O' s = N₂.presheaf.map i.op t)
    (O : Y.Opens) (hO : O ≤ V) (t : Γ(N₃, O)) : t = 0 := by
  have hψ := (TopCat.Presheaf.isLocallySurjective_iff _).1
    (ClosedImmersionHigherDirectImageVanishing.isLocallySurjective_of_epi ψ)
  refine eq_zero_of_locally_eq_zero N₃ t fun y hy => ?_
  obtain ⟨O₁, hO₁, ⟨c, hc⟩, hy₁⟩ := hψ O t y hy
  obtain ⟨O₂, i, hy₂, s, hs⟩ := hφ O₁ (hO₁.trans hO) c y hy₁
  refine ⟨O₂, i ≫ homOfLE hO₁, hy₂, ?_⟩
  have hc' : ψ.app O₁ c = N₃.presheaf.map (homOfLE hO₁).op t := hc
  have hnat : ψ.app O₂ (N₂.presheaf.map i.op c) = N₃.presheaf.map i.op (ψ.app O₁ c) :=
    NatTrans.naturality_apply ψ.mapPresheaf i.op c
  have hzero : ψ.app O₂ (φ.app O₂ s) = 0 := by
    change (φ ≫ ψ).app O₂ s = 0
    rw [hφψ]
    rfl
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hc', ← hnat, ← hs, hzero]

/-- Sections over `W` of the middle term surject onto those of the third term of a short exact
sequence when `H¹(W, -)` of the first term vanishes. -/
lemma surjective_app_of_isZero {S : ShortComplex X.Modules} (hS : S.ShortExact) (W : X.Opens)
    (h : IsZero ((openCohomology W 1).obj S.X₁)) : Function.Surjective (S.g.app W) := by
  let := HasDerivedCategory.standard W.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(W, ⊤))
  let ρ := Scheme.Modules.restrictFunctor W.ι
  let G := globalSections W.toScheme
  have hS' : (S.map ρ).ShortExact := hS.map_of_exact ρ
  have h0 : Epi ((G.rightDerived 0).map (S.map ρ).g) :=
    epi_rightDerived_zero_map_of_isZero G hS' h
  have e : G.map (S.map ρ).g = G.rightDerivedZeroIsoSelf.inv.app _ ≫
      (G.rightDerived 0).map (S.map ρ).g ≫ G.rightDerivedZeroIsoSelf.hom.app _ := by
    rw [G.rightDerivedZeroIsoSelf.hom.naturality, Iso.inv_hom_id_app_assoc]
  have h1 : Epi (G.map (S.map ρ).g) := by
    rw [e]
    infer_instance
  have h2 : Function.Surjective (S.g.app (W.ι ''ᵁ ⊤)) :=
    (ModuleCat.epi_iff_surjective (G.map (S.map ρ).g)).1 h1
  have key : ∀ O : X.Opens, O = W → Function.Surjective (S.g.app O) →
      Function.Surjective (S.g.app W) := by
    rintro O rfl hO
    exact hO
  exact key _ W.ι_image_top h2

/-- Sections over `W` vanish when `H⁰(W, -)` vanishes. -/
lemma subsingleton_of_isZero (M : X.Modules) (W : X.Opens)
    (h : IsZero ((openCohomology W 0).obj M)) : Subsingleton Γ(M, W) := by
  have h' : IsZero ((globalSections W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj M)) :=
    h.of_iso ((cohomologyZeroIso W.toScheme).app _).symm
  have h2 := ModuleCat.subsingleton_of_isZero h'
  have key : ∀ O : X.Opens, O = W → Subsingleton Γ(M, O) → Subsingleton Γ(M, W) := by
    rintro O rfl hO
    exact hO
  exact key _ W.ι_image_top h2

/-- Dimension shifting: in a short exact sequence with flasque middle term, vanishing of
`Hⁿ⁺²(W, -)` of the first term gives vanishing of `Hⁿ⁺¹(W, -)` of the third. -/
lemma isZero_openCohomology_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₂.presheaf] (W : X.Opens) (n : ℕ)
    (h : IsZero ((openCohomology W (n + 2)).obj S.X₁)) :
    IsZero ((openCohomology W (n + 1)).obj S.X₃) := by
  let := HasDerivedCategory.standard W.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(W, ⊤))
  let ρ := Scheme.Modules.restrictFunctor W.ι
  let G := globalSections W.toScheme
  have hS' : (S.map ρ).ShortExact := hS.map_of_exact ρ
  have : TopCat.Presheaf.IsFlasque (ρ.obj S.X₂).presheaf := isFlasque_restrict W S.X₂
  have hI : IsZero ((G.rightDerived (n + 1)).obj (ρ.obj S.X₂)) :=
    isZero_cohomology_succ_of_isFlasque n (ρ.obj S.X₂)
  have hδ := mono_rightDerivedδ_of_isZero G hS' (n + 1) (n + 2) rfl hI
  rw [IsZero.iff_id_eq_zero]
  exact hδ.right_cancellation _ _ (h.eq_of_tgt _ _)

/-- The sections of `Rⁿ f_* M` over opens contained in `V` vanish if `Hⁿ(f⁻¹ U, M) = 0` for
all `U` in a basis `B` with `U ≤ V`. -/
theorem eq_zero_of_isBasis (f : X ⟶ Y) (V : Y.Opens) {B : Set Y.Opens} (hB : Opens.IsBasis B)
    (n : ℕ) (M : X.Modules)
    (h : ∀ U ∈ B, U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M))
    (O : Y.Opens) (hO : O ≤ V) (t : Γ((higherDirectImage f n).obj M, O)) : t = 0 := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  let F := Scheme.Modules.pushforward f
  suffices key : ∀ (n : ℕ) (M : X.Modules),
      (∀ U ∈ B, U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) →
      ∀ O ≤ V, ∀ t : Γ((F.rightDerived n).obj M, O), t = 0 from
    key n M h O hO t
  intro n
  induction n with
  | zero =>
    intro M h O hO t
    have h0 : ∀ O ≤ V, ∀ t : Γ(F.obj M, O), t = 0 := by
      intro O hO t
      refine eq_zero_of_locally_eq_zero _ t fun y hy => ?_
      obtain ⟨U, hUB, hyU, hUO⟩ := Opens.isBasis_iff_nbhd.1 hB hy
      refine ⟨U, homOfLE hUO, hyU, ?_⟩
      have := subsingleton_of_isZero M (f ⁻¹ᵁ U) (h U hUB (hUO.trans hO))
      exact Subsingleton.elim (α := Γ(M, f ⁻¹ᵁ U)) _ _
    exact eq_zero_of_epi (F.rightDerivedZeroIsoSelf.inv.app M) h0 O hO t
  | succ n ih =>
    intro M h O hO t
    have hS := injectiveSc_shortExact M
    have := epi_rightDerivedδ_of_isZero F hS n (n + 1) rfl
      (F.isZero_rightDerived_obj_injective_succ n (Injective.under M))
    cases n with
    | zero =>
      let e := F.rightDerivedZeroIsoSelf
      let δ := rightDerivedδ F hS 0 1 rfl
      have hzero : F.map (injectiveSc M).g ≫ (e.inv.app _ ≫ δ) = 0 := by
        rw [← cancel_epi (e.hom.app (injectiveSc M).X₂), comp_zero,
          ← e.hom.naturality_assoc, Iso.hom_inv_id_app_assoc, rightDerived_map_comp_δ]
      refine eq_zero_of_comp_eq_zero hzero (fun O' hO' c y hy => ?_) O hO t
      obtain ⟨U, hUB, hyU, hUO⟩ := Opens.isBasis_iff_nbhd.1 hB hy
      refine ⟨U, homOfLE hUO, hyU, ?_⟩
      exact surjective_app_of_isZero hS (f ⁻¹ᵁ U) (h U hUB (hUO.trans hO')) _
    | succ m =>
      have : TopCat.Presheaf.IsFlasque (Injective.under M).presheaf :=
        isFlasque_of_injective (Injective.under M)
      refine eq_zero_of_epi (rightDerivedδ F hS (m + 1) (m + 2) rfl)
        (fun O' hO' s => ih (cokernel (Injective.ι M)) (fun U hUB hUV => ?_) O' hO' s) O hO t
      exact isZero_openCohomology_X₃ hS (f ⁻¹ᵁ U) m (h U hUB hUV)

end OpenCohomologyVanishing

open OpenCohomologyVanishing

/-- **Local zero detection.** If `Hⁿ(f⁻¹ U, M) = 0` for every `U` in a basis `B` of `Y` with
`U ≤ V`, then the restriction of `Rⁿ f_* M` to `V` is zero. -/
theorem isZero_restrict_higherDirectImage_of_isBasis (f : X ⟶ Y) (V : Y.Opens)
    {B : Set Y.Opens} (hB : Opens.IsBasis B) (n : ℕ) (M : X.Modules)
    (h : ∀ U ∈ B, U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj ((higherDirectImage f n).obj M)) :=
  isZero_of_subsingleton _ fun W =>
    ⟨fun a b => (eq_zero_of_isBasis f V hB n M h _ (V.ι_image_le W) a).trans
      (eq_zero_of_isBasis f V hB n M h _ (V.ι_image_le W) b).symm⟩

/-- The same vanishing for the pullback along `V.ι`, which is isomorphic to the restriction. -/
theorem isZero_pullback_higherDirectImage_of_isBasis (f : X ⟶ Y) (V : Y.Opens)
    {B : Set Y.Opens} (hB : Opens.IsBasis B) (n : ℕ) (M : X.Modules)
    (h : ∀ U ∈ B, U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((Scheme.Modules.pullback V.ι).obj ((higherDirectImage f n).obj M)) :=
  (isZero_restrict_higherDirectImage_of_isBasis f V hB n M h).of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm

/-- If `Hⁿ(f⁻¹ U, M) = 0` for every affine open `U ≤ V` of `Y`, then the restriction of
`Rⁿ f_* M` to `V` is zero. -/
theorem isZero_pullback_higherDirectImage_of_affineOpens (f : X ⟶ Y) (V : Y.Opens) (n : ℕ)
    (M : X.Modules)
    (h : ∀ U : Y.Opens, IsAffineOpen U → U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((Scheme.Modules.pullback V.ι).obj ((higherDirectImage f n).obj M)) :=
  isZero_pullback_higherDirectImage_of_isBasis f V Y.isBasis_affineOpens n M h

/-- **Zero detection.** If `Hⁿ(f⁻¹ U, M) = 0` for every `U` in a basis `B` of `Y`, then
`Rⁿ f_* M = 0`. -/
theorem isZero_higherDirectImage_of_isBasis (f : X ⟶ Y) {B : Set Y.Opens}
    (hB : Opens.IsBasis B) (n : ℕ) (M : X.Modules)
    (h : ∀ U ∈ B, IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((higherDirectImage f n).obj M) :=
  isZero_of_subsingleton _ fun O =>
    ⟨fun a b => (eq_zero_of_isBasis f ⊤ hB n M (fun U hU _ => h U hU) O le_top a).trans
      (eq_zero_of_isBasis f ⊤ hB n M (fun U hU _ => h U hU) O le_top b).symm⟩

/-- If `Hⁿ(f⁻¹ U, M) = 0` for every affine open `U` of `Y`, then `Rⁿ f_* M = 0`. -/
theorem isZero_higherDirectImage_of_affineOpens (f : X ⟶ Y) (n : ℕ) (M : X.Modules)
    (h : ∀ U : Y.Opens, IsAffineOpen U → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((higherDirectImage f n).obj M) :=
  isZero_higherDirectImage_of_isBasis f Y.isBasis_affineOpens n M h

end Langlands.AlgebraicGeometry.Modules.DerivedSections
