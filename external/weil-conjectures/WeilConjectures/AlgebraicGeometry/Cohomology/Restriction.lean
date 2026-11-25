/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-!
# Restricting resolutions to open subschemes

Restriction along an open immersion `f : X ⟶ Y` is exact and sends injective `𝒪_Y`-modules to
flasque, hence acyclic, `𝒪_X`-modules. So the restriction of an injective resolution of `ℱ` is an
acyclic resolution of `ℱ|_X`, which computes its cohomology
(`AlgebraicGeometry.Scheme.Modules.H.cyclesZeroSuccAddEquiv`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exactAt_restrict`: restriction keeps a complex exact.
- `AlgebraicGeometry.Scheme.Modules.restrictCyclesIso`: the cycles of the restricted complex are
  the restriction of the cycles.
- `AlgebraicGeometry.Scheme.Modules.H.restrictSucc`: restriction of cohomology classes to an open
  subscheme, with `H.restrictSucc_apply` and `H.restrictSucc_eq_zero_iff` on representatives.
- `AlgebraicGeometry.Scheme.Modules.exists_app_toCycles_eq_of_isAffineOpen`: for quasi-coherent
  `ℱ`, the degree-one cocycles of an injective resolution lift over affine opens.
- `AlgebraicGeometry.Scheme.Modules.mem_range_app_toCycles_of_cech`: a degree-one class whose Čech
  cocycle on an affine cover is a coboundary vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance : PreservesFiniteLimits (restrictFunctor f) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

instance : PreservesFiniteColimits (restrictFunctor f) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

/-- The restriction of a complex of `𝒪_Y`-modules along an open immersion. -/
noncomputable abbrev restrictComplex (K : CochainComplex Y.Modules ℕ) :
    CochainComplex X.Modules ℕ :=
  ((restrictFunctor f).mapHomologicalComplex _).obj K

/-- Restriction along an open immersion keeps a complex exact. -/
lemma exactAt_restrict {K : CochainComplex Y.Modules ℕ} {i : ℕ} (h : K.ExactAt i) :
    (restrictComplex f K).ExactAt i :=
  ShortComplex.Exact.map h (restrictFunctor f)

/-- The cycles of the restriction of a complex are the restriction of its cycles. -/
noncomputable def restrictCyclesIso (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictComplex f K).cycles i ≅ (K.cycles i).restrict f :=
  (K.sc i).mapCyclesIso (restrictFunctor f)

@[reassoc]
lemma restrictCyclesIso_hom_iCycles (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictCyclesIso f K i).hom ≫ (restrictFunctor f).map (K.iCycles i) =
      (restrictComplex f K).iCycles i :=
  (K.sc i).mapCyclesIso_hom_iCycles (restrictFunctor f)
@[reassoc]
lemma restrictCyclesIso_inv_iCycles (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictCyclesIso f K i).inv ≫ (restrictComplex f K).iCycles i =
      (restrictFunctor f).map (K.iCycles i) := by
  rw [← restrictCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc]

@[reassoc]
lemma map_toCycles_restrictCyclesIso_inv (K : CochainComplex Y.Modules ℕ) (n : ℕ) :
    (restrictFunctor f).map (K.toCycles n (n + 1)) ≫ (restrictCyclesIso f K (n + 1)).inv =
      (restrictComplex f K).toCycles n (n + 1) := by
  rw [← cancel_mono ((restrictComplex f K).iCycles (n + 1)), Category.assoc,
    restrictCyclesIso_inv_iCycles, ← Functor.map_comp, HomologicalComplex.toCycles_i,
    HomologicalComplex.toCycles_i]
  rfl

/-- Restricting global sections of `M` to the open subscheme `X`. -/
noncomputable def restrictSections (M : Y.Modules) : Γ(M, ⊤) →+ Γ(M.restrict f, ⊤) :=
  (M.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op).hom

lemma restrictSections_naturality {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    restrictSections f N (φ.app ⊤ s) = ((restrictFunctor f).map φ).app ⊤ (restrictSections f M s) :=
  congrArg (fun g ↦ g s) (congrArg AddCommGrpCat.Hom.hom (φ.mapPresheaf.naturality
    (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op)).symm
/-- Restriction of global sections of the cycles `Zⁿ⁺¹` of `K` to sections of the cycles of the
restricted complex. -/
noncomputable def restrictCyclesSections (K : CochainComplex Y.Modules ℕ) (n : ℕ) :
    Γ(K.cycles (n + 1), ⊤) →+ Γ((restrictComplex f K).cycles (n + 1), ⊤) :=
  ((restrictCyclesIso f K (n + 1)).inv.app ⊤).hom.comp (restrictSections f (K.cycles (n + 1)))

lemma range_app_toCycles_le_comap_restrictCyclesSections (K : CochainComplex Y.Modules ℕ)
    (n : ℕ) :
    ((K.toCycles n (n + 1)).app ⊤).hom.range ≤
      (((restrictComplex f K).toCycles n (n + 1)).app ⊤).hom.range.comap
        (restrictCyclesSections f K n) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨restrictSections f (K.X n) t, ?_⟩
  change _ = ((restrictCyclesIso f K (n + 1)).inv.app ⊤)
    (restrictSections f _ ((K.toCycles n (n + 1)).app ⊤ t))
  rw [restrictSections_naturality, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    map_toCycles_restrictCyclesIso_inv]
  rfl

variable {ℱ : Y.Modules}

/-- **Restriction of cohomology classes to an open subscheme**, `H^{n+1}(Y, ℱ) ⟶ H^{n+1}(X, ℱ|_X)`
for an open immersion `f : X ⟶ Y`, computed with an injective resolution `I` of `ℱ`: a class is
represented by a section of the cycles `Zⁿ⁺¹` of `I` (`H.cyclesZeroSuccAddEquiv`), which is
restricted to `X`, where it represents a class of the acyclic resolution `I|_X` of `ℱ|_X`. -/
noncomputable def H.restrictSucc (I : InjectiveResolution ℱ) (n : ℕ) :
    ℱ.H (n + 1) →+ (ℱ.restrict f).H (n + 1) :=
  let K := I.cocomplex
  have hK' : ∀ j, (restrictComplex f K).ExactAt (j + 1) := fun j ↦
    exactAt_restrict f (I.cocomplex_exactAt_succ j)
  have hacyc' : ∀ j m, Subsingleton (((restrictComplex f K).X j).H (m + 1)) := fun j m ↦
    subsingleton_H_restrict_of_injective f (K.X j) m
  (H.map ((restrictCyclesIso f K 0).hom ≫ (restrictFunctor f).map I.isoCyclesZero.inv)
      (n + 1)).comp <|
  (H.cyclesZeroSuccAddEquiv (restrictComplex f K) hK' hacyc' n).symm.toAddMonoidHom.comp <|
  (QuotientAddGroup.map _ _ (restrictCyclesSections f K n)
      (range_app_toCycles_le_comap_restrictCyclesSections f K n)).comp <|
  (H.cyclesZeroSuccAddEquiv K I.cocomplex_exactAt_succ
      (fun _ m ↦ subsingleton_H_of_injective _ m) n).toAddMonoidHom.comp
    (H.map I.isoCyclesZero.hom (n + 1))
/-- `H.restrictSucc` on representatives: the class represented by a section `s` of the cycles
`Zⁿ⁺¹` of `I` restricts to the class represented by the restriction of `s`. -/
lemma H.restrictSucc_apply (I : InjectiveResolution ℱ) (n : ℕ)
    (s : Γ(I.cocomplex.cycles (n + 1), ⊤)) :
    H.restrictSucc f I n (H.map I.isoCyclesZero.inv (n + 1)
        ((H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
          (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm (QuotientAddGroup.mk s))) =
      H.map ((restrictCyclesIso f I.cocomplex 0).hom ≫
          (restrictFunctor f).map I.isoCyclesZero.inv) (n + 1)
        ((H.cyclesZeroSuccAddEquiv (restrictComplex f I.cocomplex)
          (fun j ↦ exactAt_restrict f (I.cocomplex_exactAt_succ j))
          (fun j m ↦ subsingleton_H_restrict_of_injective f (I.cocomplex.X j) m) n).symm
          (QuotientAddGroup.mk (restrictCyclesSections f I.cocomplex n s))) := by
  change H.map _ (n + 1) ((H.cyclesZeroSuccAddEquiv _ _ _ n).symm (QuotientAddGroup.map _ _
    (restrictCyclesSections f I.cocomplex n)
    (range_app_toCycles_le_comap_restrictCyclesSections f I.cocomplex n)
    (H.cyclesZeroSuccAddEquiv I.cocomplex _ _ n (H.map I.isoCyclesZero.hom (n + 1)
      (H.map I.isoCyclesZero.inv (n + 1) _))))) = _
  rw [← H.map_comp_apply, Iso.inv_hom_id, H.map_id_apply, AddEquiv.apply_symm_apply,
    QuotientAddGroup.map_mk]
/-- **Lifting cocycles over an affine open.** For a quasi-coherent `ℱ` with injective resolution
`I` and an affine open `U`, every section over `U` of the cycles `Z¹` of `I` comes from `I⁰`,
since `H¹(U, ℱ|_U) = 0` (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`). -/
lemma surjective_app_toCycles_restrict_of_isAffineOpen [ℱ.IsQuasicoherent]
    (I : InjectiveResolution ℱ) {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Surjective
      (((restrictComplex U.ι I.cocomplex).toCycles 0 (0 + 1)).app ⊤).hom := by
  have : IsAffine U.toScheme := hU
  have hK' : ∀ j, (restrictComplex U.ι I.cocomplex).ExactAt (j + 1) := fun j ↦
    exactAt_restrict U.ι (I.cocomplex_exactAt_succ j)
  have hacyc' : ∀ j m, Subsingleton (((restrictComplex U.ι I.cocomplex).X j).H (m + 1)) :=
    fun j m ↦ subsingleton_H_restrict_of_injective U.ι (I.cocomplex.X j) m
  -- `H¹(U, Z⁰|_U) = H¹(U, ℱ|_U) = 0`
  have : Subsingleton ((ℱ.restrict U.ι).H (0 + 1)) := subsingleton_H_succ_of_isAffine _ 0
  have : Subsingleton (((restrictComplex U.ι I.cocomplex).cycles 0).H (0 + 1)) :=
    subsingleton_H_of_iso ((restrictCyclesIso U.ι I.cocomplex 0) ≪≫
      (restrictFunctor U.ι).mapIso I.isoCyclesZero.symm).symm (0 + 1)
  have hq := (H.cyclesZeroSuccAddEquiv (restrictComplex U.ι I.cocomplex) hK' hacyc' 0).symm
  intro s
  have h0 : (QuotientAddGroup.mk s : _ ⧸ ((((restrictComplex U.ι I.cocomplex).toCycles 0
      (0 + 1)).app ⊤).hom.range)) = 0 :=
    hq.injective (Subsingleton.elim _ _)
  exact (QuotientAddGroup.eq_zero_iff s).mp h0

/-- A class represented by a section `s` of the cycles `Zⁿ⁺¹` of `I` vanishes on the open
subscheme `X` if and only if the restriction of `s` comes from `Iⁿ` over `X`. -/
lemma H.restrictSucc_eq_zero_iff (I : InjectiveResolution ℱ) (n : ℕ)
    (s : Γ(I.cocomplex.cycles (n + 1), ⊤)) :
    H.restrictSucc f I n (H.map I.isoCyclesZero.inv (n + 1)
        ((H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
          (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm (QuotientAddGroup.mk s))) = 0 ↔
      restrictCyclesSections f I.cocomplex n s ∈
        (((restrictComplex f I.cocomplex).toCycles n (n + 1)).app ⊤).hom.range := by
  rw [H.restrictSucc_apply, ← QuotientAddGroup.eq_zero_iff]
  let e := H.mapAddEquiv ((restrictCyclesIso f I.cocomplex 0) ≪≫
    (restrictFunctor f).mapIso I.isoCyclesZero.symm) (n + 1)
  change e _ = 0 ↔ _
  rw [map_eq_zero_iff e e.injective, AddEquiv.map_eq_zero_iff]

/-- **Gluing preimages.** Let `φ : M ⟶ N` be a morphism of `𝒪_Y`-modules, `(U i)` an open cover of
`Y` and `s` a global section of `N`. If over each `U i` the restriction of `s` is the image of a
section `t i` of `M`, and the `t i` agree on overlaps, then `s` is the image of a global section
of `M`. -/
lemma exists_app_top_eq_of_isCompatible {M N : Y.Modules} (φ : M ⟶ N) {ι : Type u}
    (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) (s : Γ(N, ⊤)) (t : ∀ i, Γ(M, U i))
    (ht : ∀ i, φ.app (U i) (t i) = N.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s)
    (hcompat : TopCat.Presheaf.IsCompatible M.presheaf U t) :
    ∃ u : Γ(M, ⊤), φ.app ⊤ u = s := by
  let 𝓜 : TopCat.Sheaf Ab Y := ⟨M.presheaf, M.isSheaf⟩
  let 𝓝 : TopCat.Sheaf Ab Y := ⟨N.presheaf, N.isSheaf⟩
  obtain ⟨u, hu, -⟩ := 𝓜.existsUnique_gluing' U ⊤ (fun i ↦ homOfLE le_top) hU.ge t hcompat
  refine ⟨u, 𝓝.eq_of_locally_eq' U ⊤ (fun i ↦ homOfLE le_top) hU.ge _ _ fun i ↦ ?_⟩
  change N.presheaf.map _ (φ.app ⊤ u) = _
  rw [← Hom.app_presheaf_map, ← ht i]
  exact congrArg (φ.app (U i)) (hu i)

/-- A global section `s` of the cycles `Z¹` of a complex `K` which has local lifts to `K⁰` over an
open cover, agreeing on overlaps, comes from a global section of `K⁰`. -/
lemma mem_range_app_toCycles_of_isCompatible (K : CochainComplex Y.Modules ℕ)
    (s : Γ(K.cycles 1, ⊤)) {ι : Type u} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (t : ∀ i, Γ(K.X 0, U i))
    (ht : ∀ i, (K.d 0 1).app (U i) (t i) =
      (K.X 1).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op ((K.iCycles 1).app ⊤ s))
    (hcompat : TopCat.Presheaf.IsCompatible (K.X 0).presheaf U t) :
    s ∈ ((K.toCycles 0 1).app ⊤).hom.range := by
  obtain ⟨u, hu⟩ := exists_app_top_eq_of_isCompatible (K.d 0 1) U hU _ t ht hcompat
  refine ⟨u, injective_app_of_mono (K.iCycles 1) ?_⟩
  change ((K.toCycles 0 1 ≫ K.iCycles 1).app ⊤) u = _
  rw [HomologicalComplex.toCycles_i]
  exact hu

/-- **Cocycles lift over affine opens.** For a quasi-coherent `ℱ` with injective resolution `I`
and an affine open `U`, every section over `U` of the cycles `Z¹` of `I` comes from `I⁰`. -/
lemma exists_app_toCycles_eq_of_isAffineOpen [ℱ.IsQuasicoherent] (I : InjectiveResolution ℱ)
    {U : Y.Opens} (hU : IsAffineOpen U) (z : Γ(I.cocomplex.cycles 1, U)) :
    ∃ t : Γ(I.cocomplex.X 0, U), (I.cocomplex.toCycles 0 1).app U t = z := by
  let K := I.cocomplex
  have e : U.ι ''ᵁ ⊤ = U := U.ι_image_top
  let z' : Γ((K.cycles 1).restrict U.ι, ⊤) := (K.cycles 1).presheaf.map (eqToHom e).op z
  obtain ⟨t', ht'⟩ := surjective_app_toCycles_restrict_of_isAffineOpen I hU
    ((restrictCyclesIso U.ι K 1).inv.app ⊤ z')
  have h1 : (K.toCycles 0 1).app (U.ι ''ᵁ ⊤) t' = z' := by
    apply injective_app_of_mono (restrictCyclesIso U.ι K 1).inv
    rw [← ht', ← map_toCycles_restrictCyclesIso_inv]
    rfl
  refine ⟨(K.X 0).presheaf.map (eqToHom e.symm).op t', ?_⟩
  rw [Hom.app_presheaf_map, h1]
  change (K.cycles 1).presheaf.map _ ((K.cycles 1).presheaf.map _ z) = z
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Čech criterion for the vanishing of a degree-one class.** Let `ℱ` be quasi-coherent with
injective resolution `I`, let `(U i)` be an open cover of `Y` by affine opens, and let `s` be a
global section of the cycles `Z¹` of `I`. Over each `U i`, `s` lifts to `I⁰`
(`exists_app_toCycles_eq_of_isAffineOpen`); if any such lifts can be corrected by sections of
`ker(I⁰ ⟶ I¹)` so that they agree on overlaps (the Čech cocycle of `s` is a coboundary), then `s`
comes from a global section of `I⁰`, i.e. its class in `H¹(Y, ℱ)` vanishes. -/
lemma mem_range_app_toCycles_of_cech [ℱ.IsQuasicoherent] (I : InjectiveResolution ℱ)
    {ι : Type u} (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    (s : Γ(I.cocomplex.cycles 1, ⊤))
    (hcech : ∀ t : ∀ i, Γ(I.cocomplex.X 0, U i), (∀ i, (I.cocomplex.toCycles 0 1).app (U i) (t i) =
        (I.cocomplex.cycles 1).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s) →
      ∃ a : ∀ i, Γ(I.cocomplex.X 0, U i), (∀ i, (I.cocomplex.d 0 1).app (U i) (a i) = 0) ∧
        TopCat.Presheaf.IsCompatible (I.cocomplex.X 0).presheaf U (fun i ↦ t i - a i)) :
    s ∈ ((I.cocomplex.toCycles 0 1).app ⊤).hom.range := by
  let K := I.cocomplex
  choose t ht using fun i ↦ exists_app_toCycles_eq_of_isAffineOpen I (hU i)
    ((K.cycles 1).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s)
  obtain ⟨a, ha, hcompat⟩ := hcech t ht
  refine mem_range_app_toCycles_of_isCompatible K s U hcover (fun i ↦ t i - a i) (fun i ↦ ?_)
    hcompat
  rw [map_sub, ha, sub_zero, ← HomologicalComplex.toCycles_i, Hom.comp_app,
    ConcreteCategory.comp_apply, ht, Hom.app_presheaf_map]

end AlgebraicGeometry.Scheme.Modules
