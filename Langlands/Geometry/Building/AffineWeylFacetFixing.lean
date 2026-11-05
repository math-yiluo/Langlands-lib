import Langlands.Geometry.Building.AffineChamberTransitivity
import Mathlib.Algebra.Module.Submodule.Union

/-! # Pointwise fixing of facets by affine Weyl elements -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Every point is in the closure of some regular facet. -/
theorem IsLocallyFiniteReflectionArrangement.exists_regularPoint_closure
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p : A) :
    ∃ x : A, IsRegular Ψ x ∧ p ∈ facetClosure Ψ x := by
  classical
  let : Finite (derivativeRoots Ψ) := hΨ.finite_derivativeRoots.to_subtype
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun a : derivativeRoots Ψ => (a : Module.Dual ℝ V)) (by
      rintro ⟨a, ψ, hψ, rfl⟩
      by_contra h
      simp only [not_exists, not_not] at h
      exact hΨ.linear_ne_zero ψ hψ (LinearMap.ext h))
  obtain ⟨ε, hε, hsign⟩ := exists_pos_of_eventually
    (eventually_sign_smul_vadd hΨ p u)
  refine ⟨ε • u +ᵥ p, ?_, ?_⟩
  · intro ψ hψ
    by_cases hp : ψ p = 0
    · rw [apply_smul_vadd, hp, zero_add]
      exact mul_ne_zero hε.ne' (hu ⟨ψ.linear, ψ, hψ, rfl⟩)
    · intro hz
      have hs := hsign ψ hψ hp
      rw [hz, sign_zero, eq_comm, sign_eq_zero_iff] at hs
      exact hp hs
  · intro ψ hψ
    by_cases hp : ψ p = 0
    · exact Or.inl (by rw [hp, sign_zero])
    · exact Or.inr (hsign ψ hψ hp).symm

/-- Root-preserving affine maps preserve and reflect incidence with facet closures. -/
theorem mem_facetClosure_apply_iff {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (p x : A) :
    e p ∈ facetClosure Ψ (e x) ↔ p ∈ facetClosure Ψ x := by
  constructor
  · intro h ψ hψ
    have hψ' := (comp_mem_iff (inv_mem he) ψ).2 hψ
    simpa only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
      AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] using h _ hψ'
  · intro h ψ hψ
    exact h _ ((comp_mem_iff he ψ).2 hψ)

/-- A separating root vanishes at any common point of the two chamber closures. -/
theorem root_eq_zero_of_mem_closures {p x y : A}
    (hpx : p ∈ facetClosure Ψ x) (hpy : p ∈ facetClosure Ψ y)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hsep : ψ x * ψ y < 0) :
    ψ p = 0 := by
  by_contra hp
  have hx := (hpx ψ hψ).resolve_left (by simpa only [sign_eq_zero_iff] using hp)
  have hy := (hpy ψ hψ).resolve_left (by simpa only [sign_eq_zero_iff] using hp)
  have hpos := mul_pos_of_sign_eq
    (show ψ x ≠ 0 by rintro h; rw [h, zero_mul] at hsep; exact lt_irrefl _ hsep)
    (hx.symm.trans hy)
  exact (not_lt_of_ge hpos.le) hsep

/-- Chambers whose closures contain a point can be transported by an affine Weyl
element fixing that point. -/
theorem exists_facetRel_fixing (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {p x y : A} (hx : IsRegular Ψ x) (hy : IsRegular Ψ y)
    (hpx : p ∈ facetClosure Ψ x) (hpy : p ∈ facetClosure Ψ y) :
    ∃ w : affineWeylGroup Ψ,
      (w : A ≃ᵃ[ℝ] A) p = p ∧ facetRel Ψ ((w : A ≃ᵃ[ℝ] A) x) y := by
  suffices H : ∀ n : ℕ, ∀ x : A, IsRegular Ψ x →
      p ∈ facetClosure Ψ x → (separatingRoots Ψ x y).ncard = n →
        ∃ w : affineWeylGroup Ψ,
          (w : A ≃ᵃ[ℝ] A) p = p ∧ facetRel Ψ ((w : A ≃ᵃ[ℝ] A) x) y from
    H _ x hx hpx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hpx hn
    by_cases hne : (separatingRoots Ψ x y).Nonempty
    · obtain ⟨ψ, hψ, v, hv, hs, hsep⟩ := exists_wall hΨ hx hy hne
      let s : affineWeylGroup Ψ :=
        ⟨affineReflection ψ hv.1, affineReflection_mem_affineWeylGroup hψ hv⟩
      have hst : (s : A ≃ᵃ[ℝ] A) ∈ rootStabilizer Ψ :=
        affineReflection_mem_rootStabilizer hv
      have hsp : (s : A ≃ᵃ[ℝ] A) p = p :=
        affineReflection_apply_of_mem ψ hv.1 (root_eq_zero_of_mem_closures hpx hpy hψ hsep)
      have hpsx : p ∈ facetClosure Ψ ((s : A ≃ᵃ[ℝ] A) x) := by
        simpa only [hsp] using (mem_facetClosure_apply_iff hst p x).2 hpx
      have hlt : (separatingRoots Ψ ((s : A ≃ᵃ[ℝ] A) x) y).ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard (separatingRoots_ssubset hΨ hψ hv hx hy hs hsep)
          (finite_separatingRoots hΨ _ _)
      obtain ⟨w, hwp, hwy⟩ := ih _ hlt ((s : A ≃ᵃ[ℝ] A) x) (hx.apply hst) hpsx rfl
      refine ⟨w * s, ?_, ?_⟩
      · change (w : A ≃ᵃ[ℝ] A) ((s : A ≃ᵃ[ℝ] A) p) = p
        rw [hsp, hwp]
      · exact hwy
    · refine ⟨1, rfl, fun ψ hψ =>
        sign_eq_of_not_mul_neg (hx ψ hψ) (hy ψ hψ) fun h => hne ?_⟩
      exact ⟨ψ, hψ, h⟩

/-- A chosen affine Weyl transport between two chambers incident to a point.
The transport fixes their common incident point. -/
def pointFixingChamberTransport (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {p x y : A} (hx : IsRegular Ψ x) (hy : IsRegular Ψ y)
    (hpx : p ∈ facetClosure Ψ x) (hpy : p ∈ facetClosure Ψ y) :
    affineWeylGroup Ψ :=
  Classical.choose (exists_facetRel_fixing hΨ hx hy hpx hpy)

/-- The chosen incident-chamber transport fixes the common point. -/
theorem pointFixingChamberTransport_apply
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {p x y : A} (hx : IsRegular Ψ x) (hy : IsRegular Ψ y)
    (hpx : p ∈ facetClosure Ψ x) (hpy : p ∈ facetClosure Ψ y) :
    (pointFixingChamberTransport hΨ hx hy hpx hpy : A ≃ᵃ[ℝ] A) p = p :=
  (Classical.choose_spec (exists_facetRel_fixing hΨ hx hy hpx hpy)).1

/-- The chosen incident-chamber transport carries the first point into the
second chamber. -/
theorem pointFixingChamberTransport_facetRel
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {p x y : A} (hx : IsRegular Ψ x) (hy : IsRegular Ψ y)
    (hpx : p ∈ facetClosure Ψ x) (hpy : p ∈ facetClosure Ψ y) :
    facetRel Ψ
      ((pointFixingChamberTransport hΨ hx hy hpx hpy : A ≃ᵃ[ℝ] A) x) y :=
  (Classical.choose_spec (exists_facetRel_fixing hΨ hx hy hpx hpy)).2

/-- An affine Weyl element carrying a point into its own facet fixes that point. -/
theorem eq_of_facetRel_apply (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    (w : affineWeylGroup Ψ) (p : A) (hp : facetRel Ψ p ((w : A ≃ᵃ[ℝ] A) p)) :
    (w : A ≃ᵃ[ℝ] A) p = p := by
  obtain ⟨x, hx, hpx⟩ := hΨ.exists_regularPoint_closure p
  have hwst := affineWeylGroup_le_rootStabilizer Ψ w.property
  have hwpwx : (w : A ≃ᵃ[ℝ] A) p ∈ facetClosure Ψ ((w : A ≃ᵃ[ℝ] A) x) :=
    (mem_facetClosure_apply_iff hwst p x).2 hpx
  have hpwx : p ∈ facetClosure Ψ ((w : A ≃ᵃ[ℝ] A) x) := by
    intro ψ hψ
    rw [hp ψ hψ]
    exact hwpwx ψ hψ
  let v := pointFixingChamberTransport hΨ hx (hx.apply hwst) hpx hpwx
  have hvp : (v : A ≃ᵃ[ℝ] A) p = p :=
    pointFixingChamberTransport_apply hΨ hx (hx.apply hwst) hpx hpwx
  have hvx : facetRel Ψ ((v : A ≃ᵃ[ℝ] A) x) ((w : A ≃ᵃ[ℝ] A) x) :=
    pointFixingChamberTransport_facetRel hΨ hx (hx.apply hwst) hpx hpwx
  obtain ⟨hgen, -⟩ :=
    Langlands.Geometry.Building.affineReflectionGalleryGeometry V A Ψ hΨ x hx
  have himage : (v : A ≃ᵃ[ℝ] A) '' facet Ψ x =
      (w : A ≃ᵃ[ℝ] A) '' facet Ψ x := by
    rw [image_facet (affineWeylGroup_le_rootStabilizer Ψ v.property),
      image_facet hwst]
    exact facet_eq_facet_iff.2 hvx
  have hfix : ((v⁻¹ * w : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) '' facet Ψ x =
      facet Ψ x := by
    change ((v : A ≃ᵃ[ℝ] A)⁻¹ * (w : A ≃ᵃ[ℝ] A)) '' facet Ψ x =
      facet Ψ x
    calc
      _ = (v : A ≃ᵃ[ℝ] A).symm '' ((w : A ≃ᵃ[ℝ] A) '' facet Ψ x) := by
        rw [AffineEquiv.coe_mul, AffineEquiv.inv_def]
        exact (Set.image_image (v : A ≃ᵃ[ℝ] A).symm
          (w : A ≃ᵃ[ℝ] A) (facet Ψ x)).symm
      _ = (v : A ≃ᵃ[ℝ] A).symm '' ((v : A ≃ᵃ[ℝ] A) '' facet Ψ x) := by
        rw [himage]
      _ = facet Ψ x := by
        rw [Set.image_image]
        simp only [AffineEquiv.symm_apply_apply]
        exact Set.image_id _
  have heq := chamber_stabilizer_eq_one
    Langlands.Geometry.Building.ReflectionGallery.reflectionGalleryFreeness
    (⟨facet Ψ x, ⟨x, hx, rfl⟩⟩ : Chambers Ψ) (mem_facet_self Ψ x) hgen (v⁻¹ * w) hfix
  have hvw : v = w := inv_mul_eq_one.mp heq
  rwa [← hvw]

/-- A setwise facet stabilizer in the affine Weyl group fixes every point of it. -/
theorem affineWeyl_facet_fixing (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {F : Set A} (hF : IsFacet Ψ F) (w : affineWeylGroup Ψ)
    (hfix : (w : A ≃ᵃ[ℝ] A) '' F = F) :
    ∀ p ∈ F, (w : A ≃ᵃ[ℝ] A) p = p := by
  obtain ⟨x, rfl⟩ := hF
  intro p hp
  have hwp : (w : A ≃ᵃ[ℝ] A) p ∈ facet Ψ x := by
    rw [← hfix]
    exact Set.mem_image_of_mem _ hp
  exact eq_of_facetRel_apply hΨ w p
    ((facetRel_equivalence Ψ).trans ((facetRel_equivalence Ψ).symm hp) hwp)

end Langlands.Geometry.Building.AffineRootSystem
