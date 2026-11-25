/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.Topology.StratificationDense

/-!
# Dévissage of a constructible sheaf

A constructible sheaf `F` of `Λ`-modules on a Noetherian scheme `X` has a finite filtration
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = F` whose subquotients are extensions by zero of lisse sheaves along
locally closed immersions (`AlgebraicGeometry.Etale.exists_filtration_isFiniteLocallyConstant`,
blueprint `lemma-flat-models-generators--3`). A locally closed immersion is written as a closed
immersion `i : Y ⟶ W` into an open subscheme `W ⊆ X`, and the extension by zero along it is
`(W.ι)_! ∘ i_*`.

The filtration is `F_r = (U_r)_! (U_r)^* F ⊆ F` for a chain of opens
`∅ = U_0 ⊆ U_1 ⊆ ⋯ ⊆ U_m = X` such that each difference `U_r \ U_{r-1}` lies in a stratum of a
stratification trivializing `F`; such a chain exists by Noetherian induction
(`Topology.Stratification.exists_chain_opens`). The subquotients are computed by applying the
exact functor `(U_r)_!` to the open–closed exact sequence on `U_r`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace CategoryTheory

/-- If two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` have isomorphic right adjoints, their counits at
an object are isomorphic as arrows into that object. -/
lemma Adjunction.exists_iso_counit_app {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) (F : D) :
    ∃ α : L₁.obj (R₁.obj F) ≅ L₂.obj (R₂.obj F),
      adj₁.counit.app F = α.hom ≫ adj₂.counit.app F := by
  let adj' := adj₂.ofNatIsoRight e.symm
  refine ⟨(adj₁.leftAdjointUniq adj').app (R₁.obj F) ≪≫ L₂.mapIso (e.app F), ?_⟩
  rw [← Adjunction.leftAdjointUniq_hom_app_counit adj₁ adj']
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  congr 1

/-- If `f₁ = α ≫ φ ≫ f₂` for monomorphisms `f₁`, `f₂` and an isomorphism `α`, the cokernel of
the inclusion of subobjects `mk f₁ ≤ mk f₂` is the cokernel of `φ`. -/
def Subobject.cokernelOfLEMkIso {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {B A₁ A₁' A₂ : C} (f₁ : A₁ ⟶ B) (f₂ : A₂ ⟶ B) [Mono f₁] [Mono f₂] (α : A₁ ≅ A₁')
    (φ : A₁' ⟶ A₂) (hφ : f₁ = α.hom ≫ φ ≫ f₂) (h : mk f₁ ≤ mk f₂) :
    cokernel (ofLE _ _ h) ≅ cokernel φ :=
  cokernelIsoOfEq (f := ofLE _ _ h)
      (g := ((underlyingIso f₁).hom ≫ α.hom) ≫ φ ≫ (underlyingIso f₂).inv) (by
        rw [← cancel_mono (mk f₂).arrow, ofLE_arrow, ← underlyingIso_hom_comp_eq_mk]
        simp [← hφ]) ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _

end CategoryTheory

namespace Topology.Stratification

variable {X : Type*} [TopologicalSpace X] (S : Stratification X)

/-- For a proper open subset `U` of a space with a finite stratification, there is a strictly
larger open `U'` such that `U' \ U` lies in a single stratum: some stratum has nonempty interior
in the complement of `U`, the strata being finitely many locally closed subsets covering it. -/
lemma exists_lt_diff_subset_stratum (U : TopologicalSpace.Opens X) (hU : U ≠ ⊤) :
    ∃ U' : TopologicalSpace.Opens X, U < U' ∧ ∃ k, (U' : Set X) \ U ⊆ S.stratum k := by
  set C := (U : Set X)ᶜ
  have hC : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne, Set.compl_empty_iff]
    exact fun h ↦ hU (TopologicalSpace.Opens.coe_eq_univ.mp h)
  have : Nonempty C := hC.to_subtype
  let s : Fin S.n → Set C := fun k ↦ Subtype.val ⁻¹' S.stratum k
  obtain ⟨k, hk⟩ : ∃ k, (interior (s k)).Nonempty := by
    by_contra! h
    have hN : IsNowhereDense (⋃ k, s k) := isNowhereDense_iUnion fun k ↦
      ((S.isLocallyClosed_stratum k).preimage
        continuous_subtype_val).isNowhereDense_of_interior_eq_empty (h k)
    have hs : (⋃ k, s k) = Set.univ := by
      simp [s, ← Set.preimage_iUnion, S.iUnion_stratum_eq_univ]
    rw [hs, IsNowhereDense, closure_univ, interior_univ] at hN
    exact Set.univ_nonempty.ne_empty hN
  obtain ⟨N, hN, hNs⟩ := isOpen_induced_iff.mp (isOpen_interior (s := s k))
  refine ⟨U ⊔ ⟨N, hN⟩, ?_, k, ?_⟩
  · obtain ⟨c, hc⟩ := hk
    refine lt_of_le_of_ne le_sup_left fun h ↦ c.2 ?_
    have : c.1 ∈ (U ⊔ ⟨N, hN⟩ : TopologicalSpace.Opens X) := by
      rw [← hNs] at hc
      exact Or.inr hc
    rwa [← h] at this
  · rintro x ⟨hx, hxU⟩
    rcases hx with hx | hx
    · exact absurd hx hxU
    · have : (⟨x, hxU⟩ : C) ∈ interior (s k) := by
        rw [← hNs]
        exact hx
      exact interior_subset (s := s k) this

/-- On a Noetherian space with a finite stratification, every open `U` is the start of a finite
chain of opens `U = V₀ ≤ V₁ ≤ ⋯ ≤ V_m = X` each of whose differences `V_{r+1} \ V_r` lies in a
single stratum. -/
lemma exists_chain_opens [TopologicalSpace.NoetherianSpace X] (U : TopologicalSpace.Opens X) :
    ∃ (m : ℕ) (V : Fin (m + 1) → TopologicalSpace.Opens X), V 0 = U ∧ V (Fin.last m) = ⊤ ∧
      ∀ r : Fin m, V r.castSucc ≤ V r.succ ∧
        ∃ k, (V r.succ : Set X) \ V r.castSucc ⊆ S.stratum k := by
  induction U using WellFoundedGT.induction with
  | _ U ih =>
  by_cases hU : U = ⊤
  · exact ⟨0, fun _ ↦ U, rfl, hU, fun r ↦ r.elim0⟩
  obtain ⟨U', hUU', k, hk⟩ := S.exists_lt_diff_subset_stratum U hU
  obtain ⟨m, V, hV0, hVm, hstep⟩ := ih U' hUU'
  refine ⟨m + 1, Fin.cons U V, rfl, ?_, fun r ↦ ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hVm]
  · induction r using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hV0]
      exact ⟨hUU'.le, k, hk⟩
    | succ j =>
      rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hstep j

end Topology.Stratification

namespace AlgebraicGeometry

open Scheme

/-- The complement of the range of an open immersion is the range of a closed immersion (for
instance the reduced induced closed subscheme). -/
lemma exists_isClosedImmersion_range_eq_compl {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ := by
  let I := IdealSheafData.vanishingIdeal (⟨(Set.range j.base)ᶜ,
    j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : TopologicalSpace.Closeds X)
  exact ⟨I.subscheme, I.subschemeι, inferInstance, by simp [I, IdealSheafData.range_subschemeι]⟩

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The counit `j_! j^* F ⟶ F` of the extension by zero along an open immersion is a
monomorphism, being the first map of the open–closed short exact sequence. -/
instance Etale.mono_openImmersionLowerShriekUpperStarAdjunction_counit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((Etale.openImmersionLowerShriekUpperStarAdjunction _ j).counit.app F) := by
  obtain ⟨Z, i, _, hi⟩ := exists_isClosedImmersion_range_eq_compl j
  exact (Etale.shortExact_openClosedShortComplex _ j i F hi).mono_f

/-- Blueprint `lemma-flat-models-generators--3`: Dévissage of a constructible sheaf.

Let `X` be Noetherian (in the blueprint: of finite type over a field) and `F` a constructible
sheaf of `Λ`-modules on `X_ét`. There is a finite filtration by subsheaves
`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = F` and, for each `1 ≤ r ≤ m`, a locally closed subscheme of `X`, given
as a closed immersion `i_r : Y_r ⟶ W_r` into an open `W_r ⊆ X`, with a finite locally constant
sheaf `L_r` on `Y_r`, such that `F_r / F_{r-1} ≅ (W_r ⟶ X)_! (i_r)_* L_r`. The filtration need
not split. -/
theorem Etale.exists_filtration_isFiniteLocallyConstant [Finite Λ] {X : Scheme.{u}}
    [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (m : ℕ) (Fil : Fin (m + 1) → Subobject F), Monotone Fil ∧
      IsZero (Subobject.underlying.obj (Fil 0)) ∧
      Fil (Fin.last m) = ⊤ ∧ ∀ (r : Fin m) (h : Fil r.castSucc ≤ Fil r.succ),
        ∃ (W : X.Opens) (Y : Scheme.{u}) (i : Y ⟶ W) (_ : IsClosedImmersion i)
          (L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          IsFiniteLocallyConstantSheaf L ∧
            Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
              (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((i)_*[ModuleCat.{u + 1} Λ].obj L)) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨m, V, hV0, hVm, hstep⟩ := S.exists_chain_opens (⊥ : X.Opens)
  let ε (W : X.Opens) :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) W.ι).counit.app F
  -- the counit along `U ≤ U'` factors through the counit along `U'`
  have hfac (W₀ W : X.Opens) (h : W₀ ≤ W) : ∃ α : (W₀.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((W₀.ι)^*[ModuleCat.{u + 1} Λ].obj F) ≅ (W.ι)_!open[ModuleCat.{u + 1} Λ].obj
        ((X.homOfLE h)_!open[ModuleCat.{u + 1} Λ].obj ((X.homOfLE h)^*[ModuleCat.{u + 1} Λ].obj
          ((W.ι)^*[ModuleCat.{u + 1} Λ].obj F))),
      ε W₀ = α.hom ≫ (W.ι)_!open[ModuleCat.{u + 1} Λ].map
        ((Etale.openImmersionLowerShriekUpperStarAdjunction _ (X.homOfLE h)).counit.app
          ((W.ι)^*[ModuleCat.{u + 1} Λ].obj F)) ≫ ε W := by
    obtain ⟨α, hα⟩ := Adjunction.exists_iso_counit_app
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) W₀.ι)
      ((Etale.openImmersionLowerShriekUpperStarAdjunction _ (X.homOfLE h)).comp
        (Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι))
      (Etale.upperStarComp _ (X.homOfLE h) W.ι W₀.ι (X.homOfLE_ι h).symm) F
    exact ⟨α, hα.trans (by rw [Adjunction.comp_counit_app])⟩
  have hle (W₀ W : X.Opens) (h : W₀ ≤ W) : Subobject.mk (ε W₀) ≤ Subobject.mk (ε W) := by
    obtain ⟨α, hα⟩ := hfac W₀ W h
    exact Subobject.mk_le_mk_of_comm (α.hom ≫ _) (by rw [hα, Category.assoc])
  have hmono : Monotone V := Fin.monotone_iff_le_succ.mpr fun r ↦ (hstep r).1
  refine ⟨m, fun r ↦ Subobject.mk (ε (V r)), fun a b hab ↦ hle _ _ (hmono hab), ?_, ?_, ?_⟩
  · have h0 : IsZero ((Scheme.Opens.ι (V 0))_!open[ModuleCat.{u + 1} Λ].obj
        ((Scheme.Opens.ι (V 0))^*[ModuleCat.{u + 1} Λ].obj F)) := by
      rw [hV0]
      have : IsEmpty (⊥ : X.Opens).toScheme := 
        ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
      exact Functor.map_isZero _ (Scheme.Etale.isZero_sheaf_of_isEmpty _)
    exact h0.of_iso (Subobject.underlyingIso _)
  · obtain ⟨Z, i, _, hi⟩ := exists_isClosedImmersion_range_eq_compl (⊤ : X.Opens).ι
    have hSES := Etale.shortExact_openClosedShortComplex _ (⊤ : X.Opens).ι i F hi
    have : IsEmpty Z := ⟨fun z ↦ by
      have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
      simp [hi, Scheme.Opens.range_ι] at this⟩
    have hg : (Etale.openClosedShortComplex _ (⊤ : X.Opens).ι i
        (disjoint_range_of_range_eq_compl _ _ hi) F).g = 0 :=
      (Functor.map_isZero (i)_*[ModuleCat.{u + 1} Λ]
        (Scheme.Etale.isZero_sheaf_of_isEmpty _)).eq_of_tgt _ _
    have : Epi (ε ⊤) := hSES.exact.epi_f hg
    have : IsIso (ε (V (Fin.last m))) := by
      rw [hVm]
      exact isIso_of_mono_of_epi (ε ⊤)
    exact Subobject.mk_eq_top_of_isIso _
  · intro r h
    obtain ⟨hWW, k, hk⟩ := hstep r
    obtain ⟨Y, i, hi, hrange⟩ := exists_isClosedImmersion_range_eq_compl (X.homOfLE hWW)
    have hSES := (Etale.shortExact_openClosedShortComplex _ (X.homOfLE hWW) i
      ((Scheme.Opens.ι (V r.succ))^*[ModuleCat.{u + 1} Λ].obj F) hrange).map_of_exact
        (Scheme.Opens.ι (V r.succ))_!open[ModuleCat.{u + 1} Λ]
    obtain ⟨α, hα⟩ := hfac _ _ hWW
    refine ⟨V r.succ, Y, i, hi, (i)^*[ModuleCat.{u + 1} Λ].obj
      ((Scheme.Opens.ι (V r.succ))^*[ModuleCat.{u + 1} Λ].obj F), ?_,
      ⟨Subobject.cokernelOfLEMkIso _ _ α _ hα h ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso hSES.gIsCokernel⟩⟩
    have := hS k
    have : IsFiniteLocallyConstantSheaf
        ((i ≫ Scheme.Opens.ι (V r.succ))^*[ModuleCat.{u + 1} Λ].obj F) := by
      refine IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ (S.immersion k) ?_ F
      rintro _ ⟨y, rfl⟩
      rw [S.range_immersion]
      apply hk
      refine ⟨by simp, fun hy ↦ ?_⟩
      have : i.base y ∈ Set.range (X.homOfLE hWW).base :=
        ⟨⟨_, hy⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩
      have hy' : i.base y ∈ Set.range i.base := ⟨y, rfl⟩
      rw [hrange] at hy'
      exact hy' this
    exact IsFiniteLocallyConstantSheaf.of_iso ((Etale.upperStarComp _ i
      (Scheme.Opens.ι (V r.succ))).app F)

end AlgebraicGeometry

end
