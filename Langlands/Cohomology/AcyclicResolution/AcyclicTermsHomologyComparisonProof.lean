import Langlands.Cohomology.AcyclicResolution.AcyclicTermsHomologyComparisonStatement
import Langlands.Cohomology.AcyclicResolution.ComparisonProof
import Langlands.Cohomology.RightDerivedSequence

/-!
# Homology comparison for acyclic terms and acyclic homology

Proof of `Langlands.Cohomology.AcyclicTermsHomologyComparisonStatement`. Let `F` be a left
exact additive functor and `K` a nonnegative cochain complex whose terms and homology objects
are `F`-acyclic. For `i + 1 = j` write `Bʲ` for the kernel of `Zʲ ⟶ Hʲ`, realized as the
cycles of the short complex `Kⁱ ⟶ Zʲ ⟶ Hʲ`. The short exact sequences
`0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bʲ ⟶ 0` and `0 ⟶ Bʲ ⟶ Zʲ ⟶ Hʲ ⟶ 0` and the long exact sequence of right
derived functors show by induction that all cycles and boundaries are `F`-acyclic, starting
from `Z⁰ ≅ H⁰`. Hence `F` keeps both sequences short exact, so `F Zⁿ` is the kernel of the
mapped differential and `F Hⁿ` is the cokernel of `F Kⁿ⁻¹ ⟶ F Zⁿ`. These form a left homology
datum of the mapped complex in degree `n`, whose homology is therefore `F Hⁿ`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AcyclicTermsComparison

universe w w' u v u' v'

section Sequences

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

/-- The short complex `Kⁱ ⟶ Zʲ ⟶ Hʲ` formed by `K.toCycles i j` and `K.homologyπ j`. -/
abbrev homologySc (i j : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (K.toCycles_comp_homologyπ i j)

/-- The short complex `Kⁱ ⟶ Zʲ ⟶ Hʲ` is exact when `i` is the predecessor of `j`. -/
theorem homologySc_exact (i j : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) :
    (homologySc K i j).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hi)

/-- The short complex `Bʲ ⟶ Zʲ ⟶ Hʲ`, where `Bʲ` is the cycles object of
`homologySc K i j`. -/
abbrev boundariesSc (i j : ℕ) : ShortComplex C :=
  ShortComplex.mk (homologySc K i j).iCycles (K.homologyπ j) (homologySc K i j).iCycles_g

/-- `0 ⟶ Bʲ ⟶ Zʲ ⟶ Hʲ ⟶ 0` is short exact. -/
theorem boundariesSc_shortExact (i j : ℕ) : (boundariesSc K i j).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (homologySc K i j).cyclesIsKernel)
    inferInstance inferInstance

/-- `K.iCycles i ≫ K.toCycles i j = 0`. -/
@[reassoc]
theorem iCycles_toCycles (i j : ℕ) : K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_d, zero_comp]

/-- The short complex `Zⁱ ⟶ Kⁱ ⟶ Bʲ`. -/
abbrev cyclesSc (i j : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (homologySc K i j).toCycles (by
    rw [← cancel_mono (homologySc K i j).iCycles, Category.assoc,
      ShortComplex.toCycles_i, zero_comp]
    exact iCycles_toCycles K i j)

/-- `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bⁱ⁺¹ ⟶ 0` is short exact. -/
theorem cyclesSc_shortExact (i j : ℕ) (hij : i + 1 = j) : (cyclesSc K i j).ShortExact := by
  have hprev : (ComplexShape.up ℕ).prev j = i := by
    subst hij
    exact CochainComplex.prev_nat_succ i
  have hnext : (ComplexShape.up ℕ).next i = j := (CochainComplex.next ℕ i).trans hij
  let S' := ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)
  have hS' : S'.Exact := ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j hnext)
  let α : cyclesSc K i j ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (homologySc K i j).iCycles ≫ K.iCycles j
      comm₁₂ := by simp [S']
      comm₂₃ := by simp [S'] }
  have : Mono α.τ₃ := inferInstanceAs (Mono ((homologySc K i j).iCycles ≫ K.iCycles j))
  have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  exact ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 hS')
    inferInstance (homologySc_exact K i j hprev).epi_toCycles

end Sequences

section Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
variable (hX : ∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.X i)))
variable (hH : ∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.homology i)))

include hX in
/-- If `Zⁱ` is `F`-acyclic, then so is `Bⁱ⁺¹`. -/
theorem isZero_rightDerived_boundaries (i : ℕ)
    (hZ : ∀ r : ℕ, IsZero ((F.rightDerived (r + 1)).obj (K.cycles i))) (r : ℕ) :
    IsZero ((F.rightDerived (r + 1)).obj (homologySc K i (i + 1)).cycles) :=
  (DerivedPlus.rightDerived_exact₃ F (cyclesSc_shortExact K i (i + 1) rfl) (r + 1) (r + 1 + 1)
    rfl).isZero_X₂ ((hX i r).eq_of_src _ _) ((hZ (r + 1)).eq_of_tgt _ _)

include hH in
/-- If `Bʲ` is `F`-acyclic, then so is `Zʲ`. -/
theorem isZero_rightDerived_cycles_of_boundaries (i j : ℕ)
    (hB : ∀ r : ℕ, IsZero ((F.rightDerived (r + 1)).obj (homologySc K i j).cycles)) (r : ℕ) :
    IsZero ((F.rightDerived (r + 1)).obj (K.cycles j)) :=
  (DerivedPlus.rightDerived_exact₂ F (boundariesSc_shortExact K i j) (r + 1)).isZero_X₂
    ((hB r).eq_of_src _ _) ((hH j r).eq_of_tgt _ _)

include hX hH in
/-- All cycles of `K` are `F`-acyclic. -/
theorem isZero_rightDerived_cycles (i r : ℕ) :
    IsZero ((F.rightDerived (r + 1)).obj (K.cycles i)) := by
  induction i generalizing r with
  | zero =>
    exact AcyclicComparison.isZero_rightDerived_obj_of_iso F _
      (CochainComplex.isoHomologyπ₀ K).symm (hH 0 r)
  | succ i ih =>
    exact isZero_rightDerived_cycles_of_boundaries F K hH i (i + 1)
      (isZero_rightDerived_boundaries F K hX i ih) r

end Acyclic

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (K : CochainComplex C ℕ)

/-- If `F Kⁱ ⟶ F Zⁿ ⟶ F Hⁿ` is exact for the predecessor `i` of `n` and `F` preserves the
epimorphism `Zⁿ ⟶ Hⁿ`, then `F Zⁿ` and `F Hⁿ` form a left homology datum of the mapped
complex in degree `n`, so its homology is isomorphic to `F Hⁿ`. -/
theorem nonempty_homology_map_iso (n : ℕ)
    (hT : ((homologySc K ((ComplexShape.up ℕ).prev n) n).map F).Exact)
    [Epi (F.map (K.homologyπ n))] :
    Nonempty ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ≅
      F.obj (K.homology n)) := by
  let S := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n
  have wi : F.map (K.iCycles n) ≫ S.g = 0 := by
    change F.map (K.iCycles n) ≫ F.map (K.d n _) = 0
    rw [← F.map_comp, HomologicalComplex.iCycles_d, F.map_zero]
  let hi : IsLimit (KernelFork.ofι (F.map (K.iCycles n)) wi) :=
    KernelFork.mapIsLimit _ (K.cyclesIsKernel n _ rfl) F
  have hf' : hi.lift (KernelFork.ofι _ S.zero) =
      F.map (K.toCycles ((ComplexShape.up ℕ).prev n) n) :=
    Fork.IsLimit.hom_ext hi ((Fork.IsLimit.lift_ι hi).trans (by
      change F.map (K.d _ n) = F.map (K.toCycles _ n) ≫ F.map (K.iCycles n)
      rw [← F.map_comp, HomologicalComplex.toCycles_i]))
  have wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ F.map (K.homologyπ n) = 0 := by
    rw [hf']
    exact (F.map_comp _ _).symm.trans (by
      rw [HomologicalComplex.toCycles_comp_homologyπ, F.map_zero]; rfl)
  let T := ShortComplex.mk (hi.lift (KernelFork.ofι _ S.zero)) (F.map (K.homologyπ n)) wπ
  have hT' : T.Exact := by
    let α : T ⟶ (homologySc K ((ComplexShape.up ℕ).prev n) n).map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := (Category.id_comp _).trans (hf'.symm.trans (Category.comp_id _).symm)
        comm₂₃ := by simp [T] }
    have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 _))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 hT
  have : Epi T.g := inferInstanceAs (Epi (F.map (K.homologyπ n)))
  let h : S.LeftHomologyData :=
    { K := F.obj (K.cycles n)
      H := F.obj (K.homology n)
      i := F.map (K.iCycles n)
      π := F.map (K.homologyπ n)
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hT'.gIsCokernel }
  exact ⟨h.homologyIso⟩

end Homology

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (K : CochainComplex C ℕ)

/-- For a left exact `F` and a nonnegative complex `K` whose terms and homology objects are
`F`-acyclic, the homology of the mapped complex is isomorphic to `F` of the homology of `K`
in every degree. -/
theorem nonempty_homologyIso
    (hX : ∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.X i)))
    (hH : ∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.homology i))) (n : ℕ) :
    Nonempty ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ≅
      F.obj (K.homology n)) := by
  cases n with
  | zero =>
    have : IsIso (F.map (K.homologyπ 0)) := inferInstance
    refine nonempty_homology_map_iso F K 0 ?_
    rw [CochainComplex.prev_nat_zero, ShortComplex.exact_iff_mono]
    · exact inferInstanceAs (Mono (F.map (K.homologyπ 0)))
    · change F.map (K.toCycles 0 0) = 0
      rw [K.toCycles_eq_zero (by simp), F.map_zero]
  | succ m =>
    have hZ := isZero_rightDerived_cycles F K hX hH
    have h₁ := DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
      (cyclesSc_shortExact K m (m + 1) rfl) (hZ m 0)
    have h₂ := DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
      (boundariesSc_shortExact K m (m + 1))
      (isZero_rightDerived_boundaries F K hX m (fun r => hZ m r) 0)
    have : Epi (F.map (K.homologyπ (m + 1))) := h₂.epi_g
    refine nonempty_homology_map_iso F K (m + 1) ?_
    rw [CochainComplex.prev_nat_succ]
    let α : (homologySc K m (m + 1)).map F ⟶ (boundariesSc K m (m + 1)).map F :=
      { τ₁ := F.map (homologySc K m (m + 1)).toCycles
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change F.map _ ≫ F.map _ = F.map _ ≫ 𝟙 _
          rw [← F.map_comp, ShortComplex.toCycles_i, Category.comp_id]
        comm₂₃ := by simp }
    have : Epi α.τ₁ := h₁.epi_g
    have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 _))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 h₂.exact

end Comparison

end AcyclicTermsComparison

universe u v u' v'

/-- A left exact additive functor commutes with the homology of a nonnegative complex whose
terms and homology objects are all acyclic for its positive right derived functors. -/
theorem acyclicTermsHomologyComparisonStatement :
    AcyclicTermsHomologyComparisonStatement.{u, v, u', v'} := by
  intro C _ _ _ D _ _ F _ _ K hX hH n
  have : EnoughInjectives C := ⟨fun X =>
    ⟨{ J := (injectiveResolution X).cocomplex.X 0
       f := (injectiveResolution X).ι.f 0
       mono := (inferInstance : Mono ((injectiveResolution X).ι.f 0)) }⟩⟩
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  exact AcyclicTermsComparison.nonempty_homologyIso F K hX hH n

end Langlands.Cohomology
