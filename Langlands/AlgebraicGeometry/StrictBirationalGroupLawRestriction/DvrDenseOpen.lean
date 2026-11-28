import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric
import Langlands.AlgebraicGeometry.ConstructibleGenerizations

/-! # Dense open subschemes from neighbourhoods of fibre generic points over a DVR -/

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction

/-- Let `X` be smooth, quasi-compact and locally of finite type over a discrete valuation ring
`R`, and let `G` be a property of points of `X`. Suppose every generic point `ξ` of a fibre
component has an open neighbourhood on whose specializations of `ξ` the property `G` holds.
Then `G` holds on an open subset of `X` containing all generic points of fibre components. -/
theorem exists_opens_of_forall_fibreGeneric (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [QuasiCompact f] [LocallyOfFiniteType f] (G : X → Prop)
    (hN : ∀ ξ ∈ fibreGenericPoints f,
      ∃ N : Set X, IsOpen N ∧ ξ ∈ N ∧ ∀ x ∈ N, ξ ⤳ x → G x) :
    ∃ X' : X.Opens, fibreGenericPoints f ⊆ X' ∧ ∀ x ∈ X', G x := by
  classical
  have : Finite (Spec (CommRingCat.of R)) := SmoothDvrFibreGenericPoints.finite_base R
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  set F := fibreGenericPoints f with hFdef
  have hFfin : F.Finite := finite_fibreGenericPoints f
  have hFgen (ξ : X) (hξ : ξ ∈ F) : IsFibreGeneric f ξ := (mem_fibreGenericPoints_iff f ξ).mp hξ
  choose! N hNo hξN hNG using hN
  -- Shrink each neighbourhood so that its points in the fibre of `ξ` specialize `ξ`.
  let O : X → Set X := fun ξ => N ξ \ ⋃ ξ' ∈ {ξ' | ξ' ∈ F ∧ ¬ ξ' ⤳ ξ}, closure {ξ'}
  have hOo (ξ : X) (hξ : ξ ∈ F) : IsOpen (O ξ) :=
    (hNo ξ hξ).sdiff ((hFfin.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure)
  have hξO (ξ : X) (hξ : ξ ∈ F) : ξ ∈ O ξ := by
    refine ⟨hξN ξ hξ, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro ξ' hξ' hmem
    exact hξ'.2 (specializes_iff_mem_closure.mpr hmem)
  have hOG (ξ : X) (hξ : ξ ∈ F) (x : X) (hx : x ∈ O ξ) (hfx : f x = f ξ) : G x := by
    obtain ⟨ξ'', hξ''F, hf'', hξ''x⟩ := exists_fibreGenericPoint_specializes f x
    have hsp : ξ'' ⤳ ξ := by
      by_contra hne
      exact hx.2 (Set.mem_biUnion ⟨hξ''F, hne⟩ (specializes_iff_mem_closure.mp hξ''x))
    have heq := hFgen ξ hξ ξ'' hsp (hf''.trans hfx)
    subst heq
    exact hNG ξ'' hξ x hx.1 hξ''x
  -- The two points of the spectrum of a discrete valuation ring.
  let η : Spec (CommRingCat.of R) := (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  have hdich (s : Spec (CommRingCat.of R)) : s = η ∨ s = s₀ :=
    SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed R s
  have hne : η ≠ s₀ := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field R this.symm
  have hs₀ : IsClosed ({s₀} : Set (Spec (CommRingCat.of R))) :=
    IsLocalRing.isClosed_singleton_closedPoint R
  let Os := ⋃ ξ ∈ {ξ | ξ ∈ F ∧ f ξ = s₀}, O ξ
  let Oη := ⋃ ξ ∈ {ξ | ξ ∈ F ∧ f ξ = η}, O ξ
  have hOs : IsOpen Os := isOpen_biUnion fun ξ hξ => hOo ξ hξ.1
  have hOη : IsOpen Oη := isOpen_biUnion fun ξ hξ => hOo ξ hξ.1
  let C₁ := f ⁻¹' {s₀} ∩ Osᶜ
  let E := (f ⁻¹' {s₀})ᶜ ∩ Oηᶜ
  have hC₁ : IsClosed C₁ := (hs₀.preimage f.continuous).inter hOs.isClosed_compl
  have hEc : closure E ⊆ Oηᶜ := closure_minimal Set.inter_subset_right hOη.isClosed_compl
  refine ⟨⟨(C₁ ∪ closure E)ᶜ, (hC₁.union isClosed_closure).isOpen_compl⟩, ?_, ?_⟩
  · intro ξ hξ
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff,
      Set.mem_union, not_or]
    rcases hdich (f ξ) with h | h
    · refine ⟨fun hC => hne (h.symm.trans hC.1), fun hE => hEc hE ?_⟩
      exact Set.mem_biUnion ⟨hξ, h⟩ (hξO ξ hξ)
    · refine ⟨fun hC => hC.2 (Set.mem_biUnion ⟨hξ, h⟩ (hξO ξ hξ)), fun hE => ?_⟩
      -- A point of `E` specializing to `ξ` would be a generic point of `X`.
      have hEcon : IsConstructible E := by
        have hR (V : Set X) (hV : IsOpen V) : IsRetrocompact V :=
          fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _
        have hopen : IsOpen ((f ⁻¹' {s₀})ᶜ) := (hs₀.preimage f.continuous).isOpen_compl
        exact (IsRetrocompact.isConstructible hopen (hR _ hopen)).inter
          (IsRetrocompact.isConstructible hOη (hR _ hOη)).compl
      obtain ⟨e, he, heξ⟩ := exists_specializes_of_mem_closure_of_isConstructible hEcon hE
      have hfe : f e = η := (hdich (f e)).resolve_right he.1
      obtain ⟨_, hdvr⟩ := Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R f ξ h
        (fun y hy hfy => hFgen ξ hξ y hy (hfy.trans h.symm))
      have hrange (y : X) (hy : y ⤳ ξ) : y ∈ Set.range (X.fromSpecStalk ξ) := by
        rw [Scheme.range_fromSpecStalk]; exact hy
      have hgen : IsFibreGeneric f e := by
        intro e' he'e hfe'
        obtain ⟨P, rfl⟩ := hrange e heξ
        obtain ⟨P', rfl⟩ := hrange e' (he'e.trans heξ)
        have hP'P : P' ⤳ P := (X.fromSpecStalk ξ).isEmbedding.isInducing.specializes_iff.mp he'e
        have hPbot : P = (⟨⊥, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk ξ)) := by
          refine (SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed _ P).resolve_right ?_
          intro hP
          apply hne
          rw [← hfe, hP, Scheme.fromSpecStalk_closedPoint, h]
        have hle := (PrimeSpectrum.le_iff_specializes P' P).mpr hP'P
        have : P' = P := by
          apply PrimeSpectrum.ext
          refine le_antisymm (show P'.asIdeal ≤ P.asIdeal from hle) ?_
          rw [hPbot]; exact bot_le
        rw [this]
      have heF : e ∈ F := (mem_fibreGenericPoints_iff f e).mpr hgen
      exact he.2 (Set.mem_biUnion ⟨heF, hfe⟩ (hξO e heF))
  · intro x hx
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_union, not_or] at hx
    rcases hdich (f x) with h | h
    · have hxO : x ∈ Oη := by
        by_contra hxO
        exact hx.2 (subset_closure ⟨fun hs => hne (h.symm.trans hs), hxO⟩)
      obtain ⟨ξ, ⟨hξF, hfξ⟩, hxξ⟩ := Set.mem_iUnion₂.mp hxO
      exact hOG ξ hξF x hxξ (h.trans hfξ.symm)
    · have hxO : x ∈ Os := by
        by_contra hxO
        exact hx.1 ⟨h, hxO⟩
      obtain ⟨ξ, ⟨hξF, hfξ⟩, hxξ⟩ := Set.mem_iUnion₂.mp hxO
      exact hOG ξ hξF x hxξ (h.trans hfξ.symm)

end Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction
