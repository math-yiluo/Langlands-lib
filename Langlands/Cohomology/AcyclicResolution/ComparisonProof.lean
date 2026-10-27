import Langlands.Cohomology.AcyclicResolution.Statement
import Langlands.Cohomology.ExtendMap
import Langlands.Cohomology.RightDerivedSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Acyclic resolutions compute right derived functors

Proof of `Langlands.Cohomology.AcyclicResolutionComparisonStatement`. Let `F` be a left
exact additive functor and `ε : A[0] ⟶ K` a right resolution of `A` by `F`-acyclic objects.
For an injective resolution `I` of `A` and a lift `φ : K ⟶ I.cocomplex` of `I.ι` along `ε`,
the map `F φ` is a quasi-isomorphism.

The proof extends `φ` by zero to integer-indexed complexes. The mapping cone of the extended
map is acyclic, bounded below and has `F`-acyclic terms. An acyclic bounded below complex
of `F`-acyclic objects stays acyclic after applying `F` (`acyclic_map`): it splices into short
exact sequences of cycles, whose terms are `F`-acyclic by the long exact sequence of right
derived functors. The image of the cone under `F` is the cone of `F` applied to the extended
map, so the latter is a quasi-isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AcyclicComparison

universe w w' u v u' v'

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/-- Right derived functors send zero objects to zero objects. -/
theorem isZero_rightDerived_obj_of_isZero (k : ℕ) {X : C} (hX : IsZero X) :
    IsZero ((F.rightDerived k).obj X) := by
  rw [IsZero.iff_id_eq_zero, ← (F.rightDerived k).map_id, hX.eq_of_src (𝟙 X) 0,
    DerivedPlus.rightDerived_map_zero]

/-- Vanishing of a right derived functor is invariant under isomorphism. -/
theorem isZero_rightDerived_obj_of_iso (k : ℕ) {X Y : C} (e : X ≅ Y)
    (hX : IsZero ((F.rightDerived k).obj X)) : IsZero ((F.rightDerived k).obj Y) :=
  hX.of_iso ((F.rightDerived k).mapIso e.symm)

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]

/-- A right derived functor vanishes on a binary biproduct if it vanishes on both summands. -/
theorem isZero_rightDerived_obj_biprod (k : ℕ) (X Y : C)
    (hX : IsZero ((F.rightDerived k).obj X)) (hY : IsZero ((F.rightDerived k).obj Y)) :
    IsZero ((F.rightDerived k).obj (X ⊞ Y)) :=
  (DerivedPlus.rightDerived_exact₂ F
    (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact k).isZero_X₂
    (hX.eq_of_src _ _) (hY.eq_of_tgt _ _)

end Derived

section Cycles

variable {C : Type u} [Category.{v} C] [Abelian C] (X : CochainComplex C ℤ)

/-- The short complex `Zⁱ ⟶ Xⁱ ⟶ Zʲ` of cycles of `X`, whose second map is induced by the
differential `Xⁱ ⟶ Xʲ`. -/
abbrev cyclesSc (i j : ℤ) : ShortComplex C :=
  ShortComplex.mk (X.iCycles i) (X.toCycles i j) (by
    rw [← cancel_mono (X.iCycles j), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

/-- If `X` is exact in degree `j = i + 1`, then `0 ⟶ Zⁱ ⟶ Xⁱ ⟶ Zʲ ⟶ 0` is short exact. -/
theorem cyclesSc_shortExact (i j : ℤ) (hij : i + 1 = j) (hX : X.ExactAt j) :
    (cyclesSc X i j).ShortExact := by
  have hk : (cyclesSc X i j).Exact := by
    let S' := ShortComplex.mk (X.iCycles i) (X.d i j) (X.iCycles_d i j)
    have hS' : S'.Exact := ShortComplex.exact_of_f_is_kernel _
      (X.cyclesIsKernel i j ((CochainComplex.next ℤ i).trans hij))
    let α : cyclesSc X i j ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := X.iCycles j
        comm₁₂ := by simp [S']
        comm₂₃ := by simp [S'] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 hS'
  have hi : (ComplexShape.up ℤ).prev j = i := (CochainComplex.prev ℤ j).trans (by omega)
  have hk' : (ComplexShape.up ℤ).next j = j + 1 := CochainComplex.next ℤ j
  have hE := (X.exactAt_iff' i j (j + 1) hi hk').1 hX
  have : Epi (X.toCycles i j) := by
    have : Epi (X.toCycles i j ≫ (X.cyclesIsoSc' i j (j + 1) hi hk').hom) := by
      rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
      exact hE.epi_toCycles
    rw [← Category.comp_id (X.toCycles i j), ← Iso.hom_inv_id (X.cyclesIsoSc' i j (j + 1) hi hk'),
      ← Category.assoc]
    infer_instance
  exact ShortComplex.ShortExact.mk' hk inferInstance this

end Cycles

section Key

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

/-- In an acyclic complex that vanishes below degree `m` and has `F`-acyclic terms, every
object of cycles is `F`-acyclic. -/
theorem isZero_rightDerived_cycles (X : CochainComplex C ℤ) (hX : X.Acyclic) (m : ℤ)
    (hm : ∀ i < m, IsZero (X.X i))
    (hacyc : ∀ (i : ℤ) (n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (X.X i)))
    (i : ℤ) (n : ℕ) :
    IsZero ((F.rightDerived (n + 1)).obj (X.cycles i)) := by
  have low : ∀ i < m, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (X.cycles i)) :=
    fun i hi n => isZero_rightDerived_obj_of_isZero F _ (IsZero.of_mono (X.iCycles i) (hm i hi))
  have key : ∀ i, m - 1 ≤ i → ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (X.cycles i)) := by
    intro i hi
    induction i, hi using Int.leInduction with
    | base => exact low _ (by omega)
    | succ i hi ih =>
      intro n
      have hS := cyclesSc_shortExact X i (i + 1) rfl (hX (i + 1))
      have := DerivedPlus.isIso_rightDerivedδ_of_isZero F hS (n + 1) (n + 2) rfl
        (hacyc i n) (hacyc i (n + 1))
      exact (ih (n + 1)).of_iso (asIso (DerivedPlus.rightDerivedδ F hS (n + 1) (n + 2) rfl))
  by_cases h : i < m
  · exact low i h n
  · exact key i (by omega) n

/-- A left exact functor sends an acyclic complex that vanishes below some degree and has
`F`-acyclic terms to an acyclic complex. -/
theorem acyclic_map [PreservesFiniteLimits F] (X : CochainComplex C ℤ) (hX : X.Acyclic)
    (m : ℤ) (hm : ∀ i < m, IsZero (X.X i))
    (hacyc : ∀ (i : ℤ) (n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (X.X i))) :
    ((F.mapHomologicalComplex _).obj X).Acyclic := by
  intro i
  have hZ := isZero_rightDerived_cycles F X hX m hm hacyc
  have h₁ := DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
    (cyclesSc_shortExact X (i - 1) i (by omega) (hX i)) (hZ (i - 1) 0)
  have h₂ := DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
    (cyclesSc_shortExact X i (i + 1) rfl (hX (i + 1))) (hZ i 0)
  have h₃ := DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
    (cyclesSc_shortExact X (i + 1) (i + 2) (by omega) (hX (i + 2))) (hZ (i + 1) 0)
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (CochainComplex.prev ℤ i)
    (CochainComplex.next ℤ i)]
  let S₃ := ShortComplex.mk (F.map (X.d (i - 1) i)) (F.map (X.toCycles i (i + 1)))
    (by rw [← F.map_comp, X.d_toCycles, F.map_zero])
  have : Epi (F.map (X.toCycles (i - 1) i)) := h₁.epi_g
  have : Mono (F.map (X.iCycles (i + 1))) := h₃.mono_f
  let α : S₃ ⟶ (cyclesSc X i (i + 1)).map F :=
    { τ₁ := F.map (X.toCycles (i - 1) i)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S₃, ← F.map_comp]
      comm₂₃ := by simp [S₃] }
  let β : S₃ ⟶ ((F.mapHomologicalComplex _).obj X).sc' (i - 1) i (i + 1) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (X.iCycles (i + 1))
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by
        change 𝟙 _ ≫ F.map (X.d i (i + 1)) =
          F.map (X.toCycles i (i + 1)) ≫ F.map (X.iCycles (i + 1))
        rw [Category.id_comp, ← F.map_comp, HomologicalComplex.toCycles_i] }
  have : Epi β.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso β.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono β.τ₃ := inferInstanceAs (Mono (F.map (X.iCycles (i + 1))))
  have : Epi α.τ₁ := inferInstanceAs (Epi (F.map (X.toCycles (i - 1) i)))
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 h₂.exact)

end Key

section Cone

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism of integer-indexed cochain complexes is a quasi-isomorphism if and only if
its mapping cone is acyclic. -/
theorem quasiIso_iff_acyclic_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

end Cone

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- A lift of an injective resolution along a right resolution by `F`-acyclic objects
becomes a quasi-isomorphism after applying `F`. -/
theorem quasiIso_map {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
    (hK : ∀ (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (K.X i)))
    (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex) (hφ : ε ≫ φ = I.ι) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have : QuasiIso (ε ≫ φ) := by rw [hφ]; infer_instance
  have : QuasiIso φ := quasiIso_of_comp_left ε φ
  let e := ComplexShape.embeddingUpNat
  have hcone : (CochainComplex.mappingCone (HomologicalComplex.extendMap φ e)).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone _).1 inferInstance
  have hext : ∀ (n : ℕ) (L : CochainComplex C ℕ)
      (_ : ∀ i : ℕ, IsZero ((F.rightDerived (n + 1)).obj (L.X i))) (j : ℤ),
      IsZero ((F.rightDerived (n + 1)).obj ((L.extend e).X j)) := by
    intro n L hL j
    obtain hj | ⟨k, hk⟩ := (e.r j).eq_none_or_eq_some
    · exact isZero_rightDerived_obj_of_isZero F _ (L.isZero_extend_X' e j hj)
    · exact isZero_rightDerived_obj_of_iso F _ (HomologicalComplex.extend.XIso L hk).symm (hL k)
  have hF := acyclic_map F _ hcone (-1)
    (fun i hi => by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨K.isZero_extend_X e _ (fun j => by simp [e]; omega),
        I.cocomplex.isZero_extend_X e _ (fun j => by simp [e]; omega)⟩)
    (fun i n => isZero_rightDerived_obj_of_iso F _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (HomologicalComplex.extendMap φ e)
        i (i + 1) rfl).symm
      (isZero_rightDerived_obj_biprod F _ _ _ (hext n K (fun i => hK i n) _)
        (hext n I.cocomplex
          (fun i => F.isZero_rightDerived_obj_injective_succ n (I.cocomplex.X i)) _)))
  have h₂ : (CochainComplex.mappingCone
      ((F.mapHomologicalComplex _).map (HomologicalComplex.extendMap φ e))).Acyclic :=
    fun i => (hF i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso _ F)
  have h₃ := (quasiIso_iff_acyclic_mappingCone _).2 h₂
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ e]
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (extendMapIso e F K) (extendMapIso e F I.cocomplex)
      (extendMapIso_hom_naturality e F φ).symm)).1 h₃

end Comparison

end AcyclicComparison

universe u v u' v'

/-- Acyclic resolutions compute right derived functors: for a left exact additive functor
`F` and a right resolution `ε : A[0] ⟶ K` by `F`-acyclic objects, every lift
`φ : K ⟶ I.cocomplex` of an injective resolution `I` of `A` along `ε` becomes a
quasi-isomorphism after applying `F`, and the induced map `Hⁿ(F K) ⟶ Rⁿ F A` is an
isomorphism. -/
theorem acyclicResolutionComparisonStatement :
    AcyclicResolutionComparisonStatement.{u, v, u', v'} := by
  intro C _ _ _ D _ _ F _ _ A K ε _ hK I φ hφ
  have : EnoughInjectives C := ⟨fun X =>
    ⟨{ J := (injectiveResolution X).cocomplex.X 0
       f := (injectiveResolution X).ι.f 0
       mono := (inferInstance : Mono ((injectiveResolution X).ι.f 0)) }⟩⟩
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have hq : QuasiIso ((F.mapHomologicalComplex _).map φ) :=
    AcyclicComparison.quasiIso_map F ε hK I φ hφ
  refine ⟨hq, fun n => ?_⟩
  exact IsIso.comp_isIso'
    ((quasiIsoAt_iff_isIso_homologyMap _ n).1 (hq.quasiIsoAt n)) inferInstance

end Langlands.Cohomology
