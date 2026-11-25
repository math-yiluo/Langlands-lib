/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.AlgebraicGeometry.CoherentHomIdealPowerExtension
import WeilConjectures.AlgebraicGeometry.CoherentHomIdealPowerEventuallyZero
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.SectionsOverQuasiCompactOpen

/-! # Coherent homomorphisms over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB (blueprint:
lem-weil-pbc-coherent-homs-over-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Maps on the complement of `V(𝓘)` extend to maps from `𝓘ⁿ𝓖`. Let `X` be a Noetherian
scheme (locally Noetherian and quasi-compact), `𝓕` quasi-coherent, `𝓖` coherent and `𝓘` a
quasi-coherent sheaf of ideals. The open `U = X ∖ V(𝓘)` is given by its points: `x ∈ U` iff
the stalk inclusion `𝓘ₓ ⟶ 𝒪_{X,x}` is surjective, i.e. `𝓘ₓ = 𝒪_{X,x}` (so `V(𝓘)` is closed).
`𝓘ⁿ𝓖 ⊆ 𝓖` is `idealModuleProduct (idealSheafPower I.toModulesι n).2 G` with its inclusion
`idealModuleProductι`; at `n = 0` this is the image of the isomorphism `𝒪_X ⊗ 𝓖 ⟶ 𝓖`,
i.e. `𝓖` itself. Then `𝓘|_U = 𝒪_U` and `(𝓘ⁿ𝓖)|_U = 𝓖|_U` (the restriction to `U` of the
inclusion is an isomorphism); `r n m h` is the inclusion `𝓘ᵐ𝓖 ⊆ 𝓘ⁿ𝓖`; the diagram `D` is
`n ↦ Hom(𝓘ⁿ𝓖, 𝓕)` (identified by `e`) with restriction along `r`; the cocone `c` sends `χ`
to `χ|_U` read on `𝓖|_U` through `(𝓘ⁿ𝓖)|_U = 𝓖|_U`; and the canonical map
`colim_n Hom(𝓘ⁿ𝓖, 𝓕) ⟶ Hom_{𝒪_U}(𝓖|_U, 𝓕|_U)` is bijective. In particular every `ψ` on `U`
is `χ|_U` for some `n` and `χ : 𝓘ⁿ𝓖 ⟶ 𝓕`.
Restriction to `U` is `SheafOfModules.overFunctor X.ringCatSheaf U`.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB
(blueprint: lem-weil-pbc-coherent-homs-over-open).

Proof:
1. `V(𝓘)` is closed and meets an affine `W` in `V(𝓘(W))`
   (lem-weil-pbc-quasi-coherent-ideal-zero-set-affine); on affines inside `U` the ideal
   contains `1`, which glues, so `𝓘|_U = 𝒪_U`, and by induction `(𝓘ⁿ𝓖)|_U = 𝓖|_U`; the
   powers decrease, so the maps `ρ_n : χ ↦ χ|_U` are compatible.
2. `X` is quasi-separated and every open is quasi-compact; `𝓘ⁿ`, `𝓘ⁿ𝓖` and
   `𝓘ⁿ ⊗ 𝓖` are coherent, coherent modules are of finite presentation.
3. For `𝓖 = 𝒪_X` the map is `χ ↦ χ_U(1)` into `Γ(U, 𝓕)`, injective by
   lem-weil-pbc-sections-over-quasi-compact-open (1).
4. Surjectivity reduces to coherent `𝓕` by extending the finite type image of `1 ↦ s`
   (lem-weil-pbc-module-finite-type-submodule-extension).
5. For coherent `𝓕` the `𝓘ᴺ`-torsion subsheaves stabilize at some `𝓗 = 𝓕_n`, and
   `𝓘ⁿ𝓗 = 0` (ACC, lem-weil-pbc-noetherian-acc-quasi-coherent).
6. Artin-Rees gives `𝓕' = 𝓘ᵐ𝓕` without `𝓘`-torsion and with `𝓕'|_U = 𝓕|_U`.
7. lem-weil-pbc-sections-over-quasi-compact-open (2) for `𝓕'` gives surjectivity, hence
   the case `𝓖 = 𝒪_X`.
8. `𝓔 = 𝓗om(𝓖, 𝓕)` is quasi-coherent with `𝓔(U) = Hom(𝓖|_U, 𝓕|_U)`; apply step 7 to it.
9. `ψ` gives `φ : 𝓘ⁿ ⟶ 𝓔`, i.e. `φ̃ : 𝓣 = 𝓘ⁿ ⊗ 𝓖 ⟶ 𝓕`; `π : 𝓣 ⟶ 𝓖` has image `𝓘ⁿ𝓖`
   and kernel `𝓚`.
10. `𝓘ⁿ𝓚 = 0`, computed on affines.
11. Artin-Rees for `𝓚 ⊆ 𝓣` gives `𝓘ᵐ𝓣 ≅ 𝓘ⁿ⁺ᵐ𝓖` via `π`.
12. `φ̃ ∘ π'⁻¹ : 𝓘ⁿ⁺ᵐ𝓖 ⟶ 𝓕` restricts to `ψ` on `U` (surjectivity).
13. If `χ|_U = 0`, its image is coherent supported in `V(𝓘)`, killed by some `𝓘ᵗ`
    (lem-weil-pbc-coherent-support-power-ideal-kills), so `χ` vanishes on `𝓘ⁿ⁺ᵗ𝓖`
    (injectivity). 
(blueprint: def-weil-pbc-coherent-homs-over-open-data-structure)
-/
structure CoherentHomsOverOpenData {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) where
  U : X.Opens
  r : ∀ (n m : ℕ), n ≤ m →
    (idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
      idealModuleProduct (idealSheafPower I.toModulesι n).2 G)
  hU : ∀ x : X, x ∈ U ↔ Function.Surjective
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom
  hW : ∀ (W : X.Opens), W ≤ U → Function.Bijective (I.toModulesι.app W)
  hIso : ∀ n : ℕ, IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
    (idealModuleProductι (idealSheafPower I.toModulesι n).2 G))
  hcomp : ∀ (n m : ℕ) (h : n ≤ m),
    r n m h ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
      idealModuleProductι (idealSheafPower I.toModulesι m).2 G
  hcolim : ∃ (D : ℕ ⥤ AddCommGrpCat.{u})
    (e : ∀ n : ℕ, D.obj n ≅
      AddCommGrpCat.of (idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F))
    (c : D ⟶ (Functor.const ℕ).obj
      (AddCommGrpCat.of ((SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf U).obj F))),
    (∀ (n m : ℕ) (h : n ≤ m)
      (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
      (e m).hom (D.map (homOfLE h) ((e n).inv χ)) = r n m h ≫ χ) ∧
    (∀ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
      (SheafOfModules.overFunctor X.ringCatSheaf U).map
          (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫
        c.app n ((e n).inv χ) =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map χ) ∧
    Function.Bijective (colimit.desc D ⟨_, c⟩)

private theorem product_mono {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (G : X.Modules) :
    Mono (idealModuleProductι ι G) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  dsimp [idealModuleProductι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem product_over_iso {X : Scheme.{u}} (I : X.IdealSheafData)
    (G : X.Modules) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom)
    (n : ℕ) : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
      (idealModuleProductι (idealSheafPower I.toModulesι n).2 G)) := by
  let j := idealModuleProductι (idealSheafPower I.toModulesι n).2 G
  have hbij (W : X.Opens) (hW : W ≤ U) : Function.Bijective (j.app W) := by
    let fs := (SheafOfModules.toSheaf X.ringCatSheaf).map j
    apply TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective fs W
    intro x hx
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    have := product_mono (idealSheafPower I.toModulesι n).2 G
    have hinj : Function.Injective (S.map j).hom := by
      change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map j.mapPresheaf)
      apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      intro V
      have : Mono j.val := (SheafOfModules.forget _).map_mono j
      exact (ModuleCat.mono_iff_injective (j.val.app (.op V))).mp inferInstance
    refine ⟨hinj, ?_⟩
    obtain ⟨e, he, _, _, hrange, _, hpowers⟩ := ideal_module_product_stalk I.toModulesι G x
    let J : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    have hJ : J = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      exact (ModuleCat.epi_iff_surjective e.hom).mp inferInstance |>.comp
        ((hU x).mp (hW hx))
    have hr : LinearMap.range (S.map j).hom = ⊤ := by
      cases n with
      | zero =>
        obtain ⟨e₀, _, _, _, h₀, _⟩ :=
          ideal_module_product_stalk (𝟙 (SheafOfModules.unit X.ringCatSheaf)) G x
        have htop : (LinearMap.range
            (S.map (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫ e₀.hom).hom :
              Ideal (X.presheaf.stalk x)) = ⊤ := by
          rw [S.map_id, Category.id_comp]
          exact LinearMap.range_eq_top.mpr
            ((ModuleCat.epi_iff_surjective e₀.hom).mp inferInstance)
        change LinearMap.range (S.map j).hom =
          (LinearMap.range (S.map (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫ e₀.hom).hom :
            Ideal (X.presheaf.stalk x)) • ⊤ at h₀
        rw [htop, Submodule.top_smul] at h₀
        exact h₀
      | succ n =>
        have hh := (hpowers (n + 1) (Nat.succ_pos n)).2.1
        change LinearMap.range (S.map j).hom = J ^ (n + 1) • ⊤ at hh
        simpa only [hJ, Ideal.top_pow, Submodule.top_smul] using hh
    exact LinearMap.range_eq_top.mp hr
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _), NatTrans.isIso_iff_isIso_app]
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hbij W.unop.left (leOfHom W.unop.hom)

/-- The structural data exists (the geometric part of Lemma 01YB).
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
The proof follows Steps 1--11 and 13 of the displayed proof above: construct the
complement and transition maps, establish the coherence and finiteness facts,
apply the sections-over-a-quasi-compact-open result to obtain the cocone and its
bijective colimit map, and use the support-power-ideal argument for injectivity.
These constructions are packaged in `CoherentHomsOverOpenData`; no arbitrary
witness is chosen. (blueprint: lem-weil-pbc-coherent-homs-over-open-data) -/
theorem coherent_homs_over_open_data {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    Nonempty (CoherentHomsOverOpenData I F G) := by
  classical
  have : I.toModules.IsQuasicoherent := by
    simpa only [idealSheafPower] using
      (Modules.ideal_times_quasiCoherent_affine_sections I F).2.2.1 1 (by decide)
  have : I.toModules.IsFiniteType :=
    I.isFiniteType_toModules (I.ofFiniteType_of_isLocallyNoetherian)
  obtain ⟨U, one, rp, hU, hm, hpow, _⟩ :=
    sections_over_quasiCompact_open I.toModulesι F
  have hfactor (n m : ℕ) (h : n ≤ m) :
      ∃ r : idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
          idealModuleProduct (idealSheafPower I.toModulesι n).2 G,
        r ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
          idealModuleProductι (idealSheafPower I.toModulesι m).2 G := by
    obtain ⟨r, hr⟩ := formalModuleQuotient_factor I (𝟙 G) h
    exact ⟨r, by simpa using hr.symm⟩
  let r := fun n m h ↦ (hfactor n m h).choose
  have hr := fun n m h ↦ (hfactor n m h).choose_spec
  refine ⟨⟨U, r, hU, ?_, product_over_iso I G U hU, hr, ?_⟩⟩
  · intro W hW
    simpa only [idealSheafPower] using hpow 1 W hW
  · let P := fun n ↦ idealModuleProduct (idealSheafPower I.toModulesι n).2 G
    let j := fun n ↦ idealModuleProductι (idealSheafPower I.toModulesι n).2 G
    have hj (n : ℕ) : Mono (j n) := product_mono _ _
    have rid (n : ℕ) : r n n le_rfl = 𝟙 _ := by
      let := hj n
      apply (cancel_mono (j n)).mp
      simpa using hr n n le_rfl
    have rcomp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
        r m k h' ≫ r n m h = r n k (h.trans h') := by
      let := hj n
      apply (cancel_mono (j n)).mp
      rw [Category.assoc, hr n m h, hr m k h', hr n k (h.trans h')]
    let D : ℕ ⥤ AddCommGrpCat.{u} :=
      { obj n := AddCommGrpCat.of (P n ⟶ F)
        map {n m} f := AddCommGrpCat.ofHom
          { toFun := fun χ ↦ r n m (leOfHom f) ≫ χ
            map_zero' := by simp
            map_add' := by intros; simp only [Preadditive.comp_add] }
        map_id n := by
          apply AddCommGrpCat.ext
          intro χ
          change r n n le_rfl ≫ χ = χ
          rw [rid, Category.id_comp]
        map_comp {n m k} f g := by
          apply AddCommGrpCat.ext
          intro χ
          change r n k (leOfHom (f ≫ g)) ≫ χ =
            r m k (leOfHom g) ≫ r n m (leOfHom f) ≫ χ
          rw [← rcomp n m k (leOfHom f) (leOfHom g)]
          exact Category.assoc _ _ _ }
    let H := SheafOfModules.overFunctor X.ringCatSheaf U
    have hi (n : ℕ) : IsIso (H.map (j n)) := product_over_iso I G U hU n
    let c : D ⟶ (Functor.const ℕ).obj
        (AddCommGrpCat.of (H.obj G ⟶ H.obj F)) :=
      { app n := AddCommGrpCat.ofHom
          { toFun := fun χ ↦ inv (H.map (j n)) ≫ H.map χ
            map_zero' := by simp
            map_add' := by intros; simp only [Functor.map_add, Preadditive.comp_add] }
        naturality {n m} f := by
          apply AddCommGrpCat.ext
          intro χ
          change inv (H.map (j m)) ≫ H.map (r n m (leOfHom f) ≫ χ) =
            (inv (H.map (j n)) ≫ H.map χ) ≫ 𝟙 _
          rw [Category.comp_id]
          apply (cancel_epi (H.map (j m))).mp
          have hjm : H.map (j m) =
              H.map (r n m (leOfHom f)) ≫ H.map (j n) := by
            rw [← H.map_comp]
            exact congrArg H.map (hr n m (leOfHom f)).symm
          rw [IsIso.hom_inv_id_assoc, hjm]
          simp only [H.map_comp, Category.assoc, IsIso.hom_inv_id_assoc] }
    refine ⟨D, fun n ↦ Iso.refl _, c, ?_, ?_, ?_⟩
    · intro n m h χ
      rfl
    · intro n χ
      change H.map (j n) ≫ inv (H.map (j n)) ≫ H.map χ = H.map χ
      simp
    · let : PreservesFilteredColimitsOfSize.{0, 0}
          (CategoryTheory.forget AddCommGrpCat.{u}) :=
        preservesFilteredColimitsOfSize_shrink _
      constructor
      · apply (injective_iff_map_eq_zero (colimit.desc D ⟨_, c⟩).hom).mpr
        intro z hz
        obtain ⟨n, χ, rfl⟩ := Concrete.colimit_exists_rep D z
        have hc : c.app n χ = 0 := by
          exact (ConcreteCategory.congr_hom (colimit.ι_desc (F := D) ⟨_, c⟩ n) χ).symm.trans hz
        have hχ : H.map χ = 0 := by
          have he := congrArg (fun f ↦ H.map (j n) ≫ f) hc
          simpa [c] using he
        obtain ⟨m, h, hm⟩ :=
          coherent_hom_ideal_power_eventually_zero I F G hG U hU n χ hχ
        have hz' : D.map (homOfLE h) χ = 0 := hm (r n m h) (hr n m h)
        calc
          colimit.ι D n χ = colimit.ι D m (D.map (homOfLE h) χ) :=
            (ConcreteCategory.congr_hom (colimit.w D (homOfLE h)) χ).symm
          _ = 0 := by rw [hz']; exact map_zero _
      · intro ψ
        obtain ⟨n, χ, hχ⟩ := coherent_hom_ideal_power_extension I F G hG U hU ψ
        refine ⟨colimit.ι D n χ, ?_⟩
        have hc : c.app n χ = ψ := by
          change inv (H.map (j n)) ≫ H.map χ = ψ
          rw [← hχ, IsIso.inv_hom_id_assoc]
        exact (ConcreteCategory.congr_hom (colimit.ι_desc (F := D) ⟨_, c⟩ n) χ).trans hc

/-- The extension clause follows from the structural data in Lemma 01YB.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
Given `d.hcolim`, use surjectivity of its colimit map to represent any morphism
on `d.U` by a colimit class. The filtered colimit of the groups `D.obj n` is
represented by an element at some finite stage; the cocone compatibility in
`d.hcolim` identifies that representative with the restriction of a map from
`idealModuleProduct (idealSheafPower I n) G`, giving the required `n` and `χ`.
This step uses no additional geometric assertion.
(blueprint: lem-weil-pbc-coherent-homs-over-open-extension) -/
theorem coherent_homs_over_open_extension {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (d : CoherentHomsOverOpenData I F G) :
    ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf d.U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf d.U).obj F,
      ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
        (SheafOfModules.overFunctor X.ringCatSheaf d.U).map
            (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
          (SheafOfModules.overFunctor X.ringCatSheaf d.U).map χ := by
  have _ := hG
  intro ψ
  obtain ⟨D, e, c, hcomp, hcoc, hbij⟩ := d.hcolim
  obtain ⟨z, hz⟩ := hbij.2 ψ
  let : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{u}) :=
    preservesFilteredColimitsOfSize_shrink _
  obtain ⟨n, z, rfl⟩ := Concrete.colimit_exists_rep D z
  refine ⟨n, (e n).hom z, ?_⟩
  have he : (e n).inv ((e n).hom z) = z := by
    exact ConcreteCategory.congr_hom (e n).hom_inv_id z
  have hz' : c.app n z = ψ := by
    simpa [← ConcreteCategory.comp_apply, colimit.ι_desc] using hz
  simpa only [he, hz'] using hcoc n ((e n).hom z)

/-- (blueprint: lem-weil-pbc-coherent-homs-over-open) -/
theorem coherent_homs_over_open {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules)
    [F.IsQuasicoherent] (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∃ (U : X.Opens)
      (r : ∀ (n m : ℕ), n ≤ m →
        (idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
          idealModuleProduct (idealSheafPower I.toModulesι n).2 G)),
      (∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom) ∧
      (∀ (W : X.Opens), W ≤ U → Function.Bijective (I.toModulesι.app W)) ∧
      (∀ n : ℕ, IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
        (idealModuleProductι (idealSheafPower I.toModulesι n).2 G))) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
          idealModuleProductι (idealSheafPower I.toModulesι m).2 G) ∧
      (∃ (D : ℕ ⥤ AddCommGrpCat.{u})
        (e : ∀ n : ℕ, D.obj n ≅
          AddCommGrpCat.of (idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F))
        (c : D ⟶ (Functor.const ℕ).obj
          (AddCommGrpCat.of ((SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
            (SheafOfModules.overFunctor X.ringCatSheaf U).obj F))),
        (∀ (n m : ℕ) (h : n ≤ m)
          (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (e m).hom (D.map (homOfLE h) ((e n).inv χ)) = r n m h ≫ χ) ∧
        (∀ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (SheafOfModules.overFunctor X.ringCatSheaf U).map
              (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫
            c.app n ((e n).inv χ) =
          (SheafOfModules.overFunctor X.ringCatSheaf U).map χ) ∧
        Function.Bijective (colimit.desc D ⟨_, c⟩)) ∧
      ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
          (SheafOfModules.overFunctor X.ringCatSheaf U).obj F,
        ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (SheafOfModules.overFunctor X.ringCatSheaf U).map
              (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
            (SheafOfModules.overFunctor X.ringCatSheaf U).map χ := by
  obtain ⟨d⟩ := coherent_homs_over_open_data I F G hG
  refine ⟨d.U, d.r, d.hU, d.hW, d.hIso, d.hcomp, d.hcolim, ?_⟩
  exact coherent_homs_over_open_extension I F G hG d

end AlgebraicGeometry.Scheme
