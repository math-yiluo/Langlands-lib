import Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry
import Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision

/-! # Dividing sections by a uniformizer on an abelian scheme over a DVR -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))

/-- The pulled-back uniformizer restricted to an open. -/
abbrev unifRes (π : R) (W : A.X.left.Opens) : Γ(A.X.left, W) :=
  A.X.left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (unifX A π)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The principal open of the restricted uniformizer. -/
theorem basicOpen_unifRes (π : R) (W : A.X.left.Opens) :
    A.X.left.basicOpen (unifRes A π W) = W ⊓ A.X.left.basicOpen (unifX A π) :=
  Scheme.basicOpen_res _ _ _

/-- The pulled-back uniformizer is a nonzerodivisor on functions over every open. -/
theorem eq_zero_of_unifRes_mul_eq_zero {π : R} (hπ : Irreducible π) {W : A.X.left.Opens}
    (a : Γ(A.X.left, W)) (ha : unifRes A π W * a = 0) : a = 0 := by
  have : IsIntegral A.X.left := isIntegral_total A
  have := geometricallyIntegral A
  by_cases hW : W = ⊥
  · subst hW
    exact Subsingleton.elim _ _
  · obtain ⟨x, hx⟩ : (W : Set A.X.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hW (Opens.ext h)
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    have hc : unifRes A π W ≠ 0 := by
      intro h0
      obtain ⟨y, hy⟩ := A.X.hom.surjective (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
      have hyD : y ∈ A.X.left.basicOpen (unifX A π) := by
        rw [mem_basicOpen_unifX_iff A hπ, hy]
        exact bot_ne_closedPoint
      obtain ⟨z, hzW, hzD⟩ := nonempty_preirreducible_inter W.isOpen
        (A.X.left.basicOpen (unifX A π)).isOpen ⟨x, hx⟩ ⟨y, hyD⟩
      have hz : z ∈ A.X.left.basicOpen (unifRes A π W) := by
        rw [basicOpen_unifRes]
        exact ⟨hzW, hzD⟩
      rw [h0, Scheme.basicOpen_zero] at hz
      exact hz
    exact (mul_eq_zero.mp ha).resolve_left hc

/-- Division by the uniformizer of a function on an affine open vanishing at every point of
the special fibre. -/
theorem exists_eq_unifRes_mul_of_isAffineOpen {π : R} (hπ : Irreducible π)
    {V : A.X.left.Opens} (hV : IsAffineOpen V) (h : Γ(A.X.left, V))
    (hh : ∀ x ∈ V, A.X.hom x = IsLocalRing.closedPoint R → x ∉ A.X.left.basicOpen h) :
    ∃ h' : Γ(A.X.left, V), h = unifRes A π V * h' := by
  have e : V ≤ A.X.hom ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  let g : CommRingCat.of R ⟶ Γ(A.X.left, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ A.X.hom.appLE ⊤ V e
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appLE @Smooth A.X.hom inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e)
  algebraize [g.hom]
  have : Algebra.Smooth R Γ(A.X.left, V) := RingHom.smooth_algebraMap.mp hg
  have halg : algebraMap R Γ(A.X.left, V) π = unifRes A π V := rfl
  have key := Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision.dvd_of_forall_mem_prime
    hπ h ?_
  · obtain ⟨h', hh'⟩ := key
    exact ⟨h', by rw [hh', halg]⟩
  · intro P hP hπP
    let p : PrimeSpectrum Γ(A.X.left, V) := ⟨P, hP⟩
    let x := hV.fromSpec p
    have hxV : x ∈ V := hV.range_fromSpec.le ⟨p, rfl⟩
    have hmem : ∀ a : Γ(A.X.left, V), x ∈ A.X.left.basicOpen a ↔ a ∉ P := fun a ↦ by
      change p ∈ hV.fromSpec ⁻¹ᵁ A.X.left.basicOpen a ↔ _
      rw [hV.fromSpec_preimage_basicOpen]
      rfl
    have hx : A.X.hom x = IsLocalRing.closedPoint R := by
      by_contra hne
      have hxD : x ∈ A.X.left.basicOpen (unifX A π) := (mem_basicOpen_unifX_iff A hπ x).mpr hne
      have : x ∈ A.X.left.basicOpen (unifRes A π V) := by
        rw [basicOpen_unifRes]
        exact ⟨hxV, hxD⟩
      rw [hmem, ← halg] at this
      exact this hπP
    by_contra hhP
    exact hh x hxV hx ((hmem h).mpr hhP)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Restricting the restricted uniformizer gives the restricted uniformizer. -/
theorem res_unifRes (π : R) {W W' : A.X.left.Opens} (hW : W' ≤ W) :
    A.X.left.presheaf.map (homOfLE hW).op (unifRes A π W) = unifRes A π W' := by
  rw [unifRes, unifRes, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Division by the uniformizer of a function on an arbitrary open vanishing at every point
of the special fibre. -/
theorem exists_eq_unifRes_mul {π : R} (hπ : Irreducible π) {U : A.X.left.Opens}
    (h : Γ(A.X.left, U))
    (hh : ∀ x ∈ U, A.X.hom x = IsLocalRing.closedPoint R → x ∉ A.X.left.basicOpen h) :
    ∃ h' : Γ(A.X.left, U), h = unifRes A π U * h' := by
  have hV : ∀ x : U, ∃ V : A.X.left.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ U := fun x ↦ by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      A.X.left.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.2
    exact ⟨V, hV, hxV, hVU⟩
  choose V hVa hxV hVU using hV
  have hloc : ∀ x : U, ∃ b : Γ(A.X.left, V x),
      A.X.left.presheaf.map (homOfLE (hVU x)).op h = unifRes A π (V x) * b := fun x ↦ by
    apply exists_eq_unifRes_mul_of_isAffineOpen A hπ (hVa x)
    intro y hy hys hyb
    rw [Scheme.basicOpen_res] at hyb
    exact hh y (hVU x hy) hys hyb.2
  choose b hb using hloc
  have key : ∀ x y : U,
      A.X.left.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op (b x) =
        A.X.left.presheaf.map (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op (b y) := by
    intro x y
    apply sub_eq_zero.mp
    apply eq_zero_of_unifRes_mul_eq_zero A hπ
    have t1 : unifRes A π (V x ⊓ V y) *
        A.X.left.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op (b x) =
        A.X.left.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op
          (A.X.left.presheaf.map (homOfLE (hVU x)).op h) := by
      rw [← res_unifRes A π (inf_le_left : V x ⊓ V y ≤ V x), ← map_mul, ← hb x]
    have t2 : unifRes A π (V x ⊓ V y) *
        A.X.left.presheaf.map (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op (b y) =
        A.X.left.presheaf.map (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op
          (A.X.left.presheaf.map (homOfLE (hVU y)).op h) := by
      rw [← res_unifRes A π (inf_le_right : V x ⊓ V y ≤ V y), ← map_mul, ← hb y]
    rw [mul_sub, t1, t2, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, sub_eq_zero]
    rfl
  let F := A.X.left.sheaf
  have hcompat : TopCat.Presheaf.IsCompatible F.1 V b := key
  have hcover : U ≤ iSup V := fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  obtain ⟨h', hh', -⟩ := F.existsUnique_gluing' V U (fun x ↦ homOfLE (hVU x)) hcover b hcompat
  let g : Γ(A.X.left, U) := h'
  have hg : ∀ x : U, A.X.left.presheaf.map (homOfLE (hVU x)).op g = b x := hh'
  refine ⟨g, ?_⟩
  have hloc : ∀ x : U, A.X.left.presheaf.map (homOfLE (hVU x)).op h =
      A.X.left.presheaf.map (homOfLE (hVU x)).op (unifRes A π U * g) := by
    intro x
    rw [map_mul, res_unifRes, hb x, hg x]
  exact F.eq_of_locally_eq' V U (fun x ↦ homOfLE (hVU x)) hcover h (unifRes A π U * g) hloc

/-- Krull intersection: a function divisible by every power of the uniformizer near a point of
the special fibre vanishes. -/
theorem eq_zero_of_forall_unifRes_pow_dvd {π : R} (hπ : Irreducible π) {W : A.X.left.Opens}
    (h : Γ(A.X.left, W)) {x : A.X.left} (hx : x ∈ W)
    (hxs : A.X.hom x = IsLocalRing.closedPoint R)
    (hdiv : ∀ j : ℕ, ∃ hj : Γ(A.X.left, W), h = unifRes A π W ^ j * hj) : h = 0 := by
  have : IsIntegral A.X.left := isIntegral_total A
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  let germ := A.X.left.presheaf.germ W x hx
  let c := germ (unifRes A π W)
  have hc : c ∈ IsLocalRing.maximalIdeal (A.X.left.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hxb : x ∈ A.X.left.basicOpen (unifRes A π W) :=
      (Scheme.mem_basicOpen A.X.left (unifRes A π W) x hx).mpr hu
    rw [basicOpen_unifRes] at hxb
    exact (mem_basicOpen_unifX_iff A hπ x).mp hxb.2 hxs
  have hI : Ideal.span {c} ≠ ⊤ := by
    intro htop
    have : Ideal.span {c} ≤ IsLocalRing.maximalIdeal _ :=
      (Ideal.span_singleton_le_iff_mem _).mpr hc
    rw [htop] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)
  have hmem : germ h ∈ ⨅ i : ℕ, (Ideal.span {c}) ^ i := by
    rw [Ideal.mem_iInf]
    intro i
    obtain ⟨hj, hhj⟩ := hdiv i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hhj, map_mul, map_pow]
    exact dvd_mul_right _ _
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI, Ideal.mem_bot] at hmem
  exact germ_injective_of_isIntegral A.X.left x hx (by rw [hmem, map_zero])

end Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry
