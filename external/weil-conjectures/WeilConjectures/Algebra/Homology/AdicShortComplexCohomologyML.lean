/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties

/-! # Mittag--Leffler cohomology of adic quotient complexes

Source: Stacks Project, Tag 09C5; the Artin--Rees argument is Tag 00IN.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AdicCohomology

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual ideal power submodule I^n M.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
abbrev power (M : ModuleCat.{u} R) (n : ℕ) : Submodule R M := I ^ n • ⊤

/-- Linear maps preserve ideal-power submodules.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
theorem map_power {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) :
    power I M n ≤ (power I N n).comap f.hom := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact smul_mono_right _ (by simp)

/-- Termwise quotient by the actual ideal power, retaining the original scalar ring.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
def quotient (n : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M ⧸ power I M n)
  map f := ModuleCat.ofHom ((power I _ n).mapQ (power I _ n) f.hom (map_power I f n))
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

instance adicShortComplexCohomologyMLInst1 (n : ℕ) : (quotient I n).Additive where
  map_add := by
    intro M N f g
    ext x
    exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

/-- The canonical quotient transition, including identities.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
def transition {n m : ℕ} (h : n ≤ m) : quotient I m ⟶ quotient I n where
  app M := ModuleCat.ofHom (Submodule.factor
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right h)))
  naturality := by
    intro M N f
    ext x
    exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

/-- The transition at a repeated index is the identity.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
theorem transition_refl (n : ℕ) : transition I (le_refl n) = 𝟙 _ := by
  ext M x
  exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

/-- Quotient transitions compose with their actual quotient maps.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
theorem transition_comp {n m t : ℕ} (h : n ≤ m) (k : m ≤ t) :
    transition I (k.trans' h) = transition I k ≫ transition I h := by
  ext M x
  exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

/-- The actual adic quotient diagram of a short complex, with exponent n+1 at level n.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
def shortComplexTower (S : ShortComplex (ModuleCat.{u} R)) :
    ℕᵒᵖ ⥤ ShortComplex (ModuleCat.{u} R) where
  obj n := S.map (quotient I (n.unop + 1))
  map f := S.mapNatTrans (transition I (Nat.add_le_add_right (leOfHom f.unop) 1))
  map_id n := by
    apply ShortComplex.hom_ext
    all_goals exact congrArg (fun η ↦ η.app _) (transition_refl I _)
  map_comp f g := by
    apply ShortComplex.hom_ext
    all_goals exact congrArg (fun η ↦ η.app _) (transition_comp I
      (Nat.add_le_add_right (leOfHom g.unop) 1)
      (Nat.add_le_add_right (leOfHom f.unop) 1))

/-- Cohomology of the actual adic quotient diagram.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
def tower (S : ShortComplex (ModuleCat.{u} R)) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  shortComplexTower I S ⋙ ShortComplex.homologyFunctor _

private theorem cycle_correction [IsNoetherianRing R]
    {M N : ModuleCat.{u} R} [Module.Finite R N] (d : M ⟶ N) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m → ∀ z : M,
      d z ∈ power I N m → ∃ x : M, d x = 0 ∧ z - x ∈ power I M n := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range d.hom)
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have hc' : c ≤ m := by omega
  have hdz : d z ∈ I ^ (m - c) • LinearMap.range d.hom := by
    have hmem : d z ∈ power I N m ⊓ LinearMap.range d.hom := ⟨hz, ⟨z, rfl⟩⟩
    rw [hc m hc'] at hmem
    exact (show I ^ (m - c) • (I ^ c • ⊤ ⊓ LinearMap.range d.hom) ≤
      I ^ (m - c) • LinearMap.range d.hom from smul_mono_right _ inf_le_right) hmem
  have hdz' : d z ∈ (power I M n).map d.hom := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (show n ≤ m - c by omega))) hdz
  obtain ⟨y, hy, he⟩ := hdz'
  refine ⟨z - y, ?_, ?_⟩
  · simp only [map_sub, he, sub_self]
  · rw [sub_sub_cancel]
    exact hy

private def cycle (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.cycles :=
  S.moduleCatCyclesIso.inv ⟨x, hx⟩

private theorem cycle_i (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂)
    (hx : S.g x = 0) : S.iCycles (cycle S x hx) = x := by
  change (S.moduleCatCyclesIso.inv ≫ S.iCycles) ⟨x, hx⟩ = x
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

private def cl (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.homology := S.homologyπ (cycle S x hx)

private theorem class_surjective (S : ShortComplex (ModuleCat.{u} R)) (a : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), cl S x hx = a := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  refine ⟨S.iCycles z, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f z) S.iCycles_g
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  · change S.homologyπ (cycle _ _ _) = S.homologyπ z
    apply congrArg (fun w ↦ S.homologyπ w)
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    exact cycle_i _ _ _

private theorem cl_naturality {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) (hy : T.g (f.τ₂ x) = 0) :
    ShortComplex.homologyMap f (cl S x hx) = cl T (f.τ₂ x) hy := by
  have hcyc : ShortComplex.cyclesMap f (cycle S x hx) = cycle T (f.τ₂ x) hy := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [cycle_i, ← ModuleCat.comp_apply, ShortComplex.cyclesMap_i,
      ModuleCat.comp_apply, cycle_i]
  dsimp only [cl]
  rw [← ModuleCat.comp_apply, ShortComplex.homologyπ_naturality,
    ModuleCat.comp_apply, hcyc]

/-- Artin--Rees stabilizes the cohomology images of the actual adic quotients.
Only the term following the cohomology degree needs to be finite.
Source: Stacks Project, Tag 09C5, final paragraph, using Tag 00IN.
(auxiliary; not a blueprint node).

Proof: apply Artin--Rees to the image of the outgoing differential in its finite
codomain. A cycle modulo I^(n+c) lifts to z with dz in I^(n+c). Artin--Rees writes
dz = dy for y in I^n. Thus z-y is a genuine cycle, with the same class modulo I^n,
and reduces to a cycle at every later level. These cycles give preimages under
all deeper transition maps, which is the Mittag--Leffler condition. -/
theorem isMittagLeffler [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₃] :
    (tower I S ⋙ forget _).IsMittagLeffler := by
  obtain ⟨c, hc⟩ := cycle_correction I S.g
  apply (Functor.isMittagLeffler_iff_subset_range_comp _).mpr
  intro n
  let m := op (n.unop + c)
  let f : m ⟶ n := (homOfLE (Nat.le_add_right n.unop c)).op
  refine ⟨m, f, ?_⟩
  intro t g a ha
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨z, hz, rfl⟩ := class_surjective ((shortComplexTower I S).obj m) a
  obtain ⟨z₀, rfl⟩ := (power I S.X₂ (m.unop + 1)).mkQ_surjective z
  have hdz : S.g z₀ ∈ power I S.X₃ (m.unop + 1) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨x, hx, hzx⟩ := hc (n.unop + 1) (m.unop + 1) (by dsimp [m]; omega) z₀ hdz
  have hn : (power I S.X₂ (n.unop + 1)).mkQ z₀ =
      (power I S.X₂ (n.unop + 1)).mkQ x :=
    (Submodule.Quotient.eq _).mpr hzx
  have hxt : ((shortComplexTower I S).obj t).g
      ((power I S.X₂ (t.unop + 1)).mkQ x) = 0 := by
    change (power I S.X₃ (t.unop + 1)).mkQ (S.g x) = 0
    rw [hx, map_zero]
  refine ⟨cl ((shortComplexTower I S).obj t) _ hxt, ?_⟩
  change ShortComplex.homologyMap ((shortComplexTower I S).map (g ≫ f)) _ =
    ShortComplex.homologyMap ((shortComplexTower I S).map f) _
  have hx' : ((shortComplexTower I S).obj n).g
      ((power I S.X₂ (n.unop + 1)).mkQ x) = 0 := by
    change (power I S.X₃ (n.unop + 1)).mkQ (S.g x) = 0
    rw [hx, map_zero]
  have hz' : ((shortComplexTower I S).obj n).g
      ((power I S.X₂ (n.unop + 1)).mkQ z₀) = 0 := by rw [hn]; exact hx'
  rw [cl_naturality _ _ _ hx', cl_naturality _ _ _ hz']
  congr 1
  exact hn.symm

variable {S₀ : Type u} [CommRing S₀]

private theorem map_range_le (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S₀)
    [F.Additive] [F.PreservesHomology]
    {M N P : ModuleCat.{u} R} (f : M ⟶ P) (g : N ⟶ P)
    (h : Set.range f ⊆ Set.range g) : Set.range (F.map f) ⊆ Set.range (F.map g) := by
  let C := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have he : C.Exact := ShortComplex.cokernelSequence_exact g
  have he' := he.map F
  have hz : f ≫ cokernel.π g = 0 := by
    ext x
    obtain ⟨y, hy⟩ := h (Set.mem_range_self x)
    rw [ModuleCat.comp_apply, ← hy]
    exact congrArg (fun k ↦ k y) (cokernel.condition g)
  rintro _ ⟨x, rfl⟩
  apply (ShortComplex.moduleCat_exact_iff (C.map F)).mp he'
  change (F.map (cokernel.π g)) ((F.map f) x) = 0
  have hzero := congrArg (fun k ↦ k x) (F.congr_map hz)
  simpa only [Functor.map_comp, Functor.map_zero, ModuleCat.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using hzero

/-- Exact additive functors between module categories preserve stabilized transition images.
Source: Stacks Project, Tag 09C5, exact sections argument.
(auxiliary; not a blueprint node). -/
theorem map_isMittagLeffler (T : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S₀) [F.Additive] [F.PreservesHomology]
    (hT : (T ⋙ forget _).IsMittagLeffler) : (T ⋙ F ⋙ forget _).IsMittagLeffler := by
  intro n
  obtain ⟨m, f, hf⟩ := hT n
  refine ⟨m, f, fun {_} g ↦ ?_⟩
  exact map_range_le F (T.map f) (T.map g) (hf g)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Sections of the actual constant module sheaf, retaining algebraic scalars.
Source: Stacks Project, Tag 09C5.
(auxiliary; not a blueprint node). -/
def sections (U : C) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  constantSheaf J (ModuleCat.{u} R) ⋙ sheafToPresheaf J (ModuleCat.{u} R) ⋙
    (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U)

instance adicShortComplexCohomologyMLInst2 (U : C) : (sections (R := R) J U).Additive := by
  dsimp [sections]
  infer_instance

/-- Constant module sections are exact, by the constant-section exactness theorem.
Source: Stacks Project, Tags 093J and 093K.
(auxiliary; not a blueprint node). -/
theorem sections_preservesHomology [IsNoetherianRing R] (U : C) :
    (sections (R := R) J U).PreservesHomology := by
  let F := sections (R := R) J U
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u} R)) :=
    comp_preservesFiniteLimits
      (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _) (presheafToSheaf J _)
  have : PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{u} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have hinj := (ModuleCat.mono_iff_injective (kernel.ι f)).mp inferInstance
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ShortComplex.kernelSequence f)).mp (ShortComplex.kernelSequence_exact f)
    have hsurj := (ModuleCat.epi_iff_surjective f).mp hf
    have h := (constantModule_section_properties J R).1
      _ _ _ (kernel.ι f) f hinj hex hsurj U
    exact (ModuleCat.epi_iff_surjective (F.map f)).mpr h.2.2
  exact Functor.preservesHomology_of_preservesEpis_and_kernels F

end AdicCohomology
