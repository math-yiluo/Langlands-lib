import Mathlib
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.PolynomialJacobian

/-! # Regularity of fibres through a Jacobian criterion -/

universe u

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open IsLocalRing MvPolynomial TensorProduct

/-- A family in the maximal ideal of a Noetherian local ring generates the maximal ideal exactly
when its classes span the cotangent space. -/
theorem span_range_toCotangent_eq_top_iff {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {ι : Type*} (f : ι → R) (hf : ∀ i, f i ∈ maximalIdeal R) :
    Submodule.span (ResidueField R)
        (Set.range fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩) = ⊤ ↔
      Ideal.span (Set.range f) = maximalIdeal R := by
  have h1 : (Set.range fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩) =
      (maximalIdeal R).toCotangent '' Set.range (fun i => (⟨f i, hf i⟩ : maximalIdeal R)) := by
    rw [← Set.range_comp]
    rfl
  rw [h1, CotangentSpace.span_image_eq_top_iff,
    ← (Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype).eq_iff,
    Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

/-- A prime `N` of a Noetherian ring `P` contains a finite family whose images in `P_N` form a
basis of the cotangent space; such a family generates the maximal ideal of `P_N`. -/
theorem exists_cotangent_basis {P : Type u} [CommRing P] [IsNoetherianRing P] (N : Ideal P)
    [N.IsPrime] :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → P)
      (hg : ∀ j, algebraMap P (Localization.AtPrime N) (g j) ∈
        maximalIdeal (Localization.AtPrime N)),
      LinearIndependent (ResidueField (Localization.AtPrime N))
          (fun j => (maximalIdeal (Localization.AtPrime N)).toCotangent ⟨_, hg j⟩) ∧
        Ideal.span (Set.range fun j => algebraMap P (Localization.AtPrime N) (g j)) =
          maximalIdeal (Localization.AtPrime N) := by
  classical
  set L := Localization.AtPrime N
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian N
  have hsN : ∀ x : s, (x : P) ∈ N := fun x => hs ▸ Submodule.subset_span x.2
  have hmem : ∀ x : s, algebraMap P L x ∈ maximalIdeal L := fun x =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L N x).mpr (hsN x)
  let v : s → CotangentSpace L := fun x => (maximalIdeal L).toCotangent ⟨_, hmem x⟩
  have hspan : Submodule.span (ResidueField L) (Set.range v) = ⊤ := by
    refine (span_range_toCotangent_eq_top_iff (fun x : s => algebraMap P L x) hmem).mpr ?_
    have h2 : Ideal.map (algebraMap P L) (Ideal.span (s : Set P)) = maximalIdeal L := by
      rw [show Ideal.span (s : Set P) = N from hs]
      exact Localization.AtPrime.map_eq_maximalIdeal
    rw [← h2, Ideal.map_span]
    congr 1
    ext y
    simp
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (ResidueField L) v
  have : Finite κ := Finite.of_injective a ha
  refine ⟨κ, Fintype.ofFinite κ, fun j => (a j : P), fun j => hmem (a j), hli, ?_⟩
  refine (span_range_toCotangent_eq_top_iff (fun j => algebraMap P L (a j))
    (fun j => hmem (a j))).mp ?_
  rw [← hspan, ← hsp]
  rfl

variable {R₀ : Type*} [CommRing R₀] [IsNoetherianRing R₀] {τ : Type*} [Fintype τ]
  [DecidableEq τ]

/-- **Fibre regularity.** Let `B` be a regular ring which is an algebra over the polynomial ring
`P = R₀[X_v, v ∈ τ]` over a Noetherian ring `R₀`, and let `N` be a prime of `P` whose residue field
is formally smooth over `R₀`. Suppose that at every prime `r` of `B` the partial derivatives
`∂/∂X_v`, reduced to `κ(r)`, extend to `B`, in the sense of a ring homomorphism
`Φ r : B → κ(r) ⊕ κ(r)^τ` (trivial square-zero extension) lifting the residue map whose second
component on the image of `g ∈ P` is `(∂g/∂X_v)_v`. Then the fibre `κ(N) ⊗_P B` is regular. -/
theorem isRegularRing_fiber_of_jacobian {B : Type*} [CommRing B]
    [Algebra (MvPolynomial τ R₀) B] [IsRegularRing B]
    (N : Ideal (MvPolynomial τ R₀)) [N.IsPrime] [Algebra.FormallySmooth R₀ N.ResidueField]
    (Φ : ∀ (r : Ideal B) [r.IsPrime], B →+* TrivSqZeroExt r.ResidueField (τ → r.ResidueField))
    (hΦ₁ : ∀ (r : Ideal B) [r.IsPrime] (b : B), (Φ r b).fst = algebraMap B r.ResidueField b)
    (hΦ₂ : ∀ (r : Ideal B) [r.IsPrime] (g : MvPolynomial τ R₀),
      (Φ r (algebraMap _ B g)).snd =
        fun v => algebraMap B r.ResidueField (algebraMap _ B (pderiv v g))) :
    IsRegularRing (N.Fiber B) := by
  classical
  have hnoeth : IsNoetherianRing (N.Fiber B) := by
    have : IsNoetherianRing (Localization (Algebra.algebraMapSubmonoid B N.primeCompl)) :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid B N.primeCompl) _
        inferInstance
    let : Algebra B (N.Fiber B) := Algebra.TensorProduct.rightAlgebra
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ (S := B) N).symm.toRingEquiv
  refine (isRegularRing_iff).mpr fun q _ => ?_
  set r : Ideal B := q.comap (Algebra.TensorProduct.includeRight :
    B →ₐ[MvPolynomial τ R₀] N.ResidueField ⊗[MvPolynomial τ R₀] B)
  have hNr : N = r.comap (algebraMap (MvPolynomial τ R₀) B) := by
    ext x
    rw [Ideal.mem_of_liesOver q N x]
    simp [r, Algebra.TensorProduct.algebraMap_apply]
  set L := Localization.AtPrime N
  set Br := Localization.AtPrime r
  obtain ⟨ι, _, g, hgm, hgli, hgspan⟩ := exists_cotangent_basis N
  have hjac := linearIndependent_pderiv_of_linearIndependent_cotangent (L := L) g hgm hgli
  let ρ := Ideal.ResidueField.map N r (algebraMap (MvPolynomial τ R₀) B) hNr
  let : Algebra N.ResidueField r.ResidueField := ρ.toAlgebra
  have hunit : ∀ y : r.primeCompl, IsUnit (Φ r y) := fun y => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hΦ₁, isUnit_iff_ne_zero, Ne,
      Ideal.algebraMap_residueField_eq_zero]
    exact y.2
  let Ψ : Br →+* TrivSqZeroExt r.ResidueField (τ → r.ResidueField) :=
    IsLocalization.lift (M := r.primeCompl) hunit
  have hΨ : ∀ x, (Ψ x).fst = residue Br x := by
    have : (TrivSqZeroExt.fstHom r.ResidueField r.ResidueField
        (τ → r.ResidueField)).toRingHom.comp Ψ = residue Br := by
      refine IsLocalization.ringHom_ext r.primeCompl (RingHom.ext fun b => ?_)
      change (Ψ (algebraMap B Br b)).fst = residue Br (algebraMap B Br b)
      rw [IsLocalization.lift_eq, hΦ₁]
      rfl
    exact fun x => RingHom.congr_fun this x
  let f : ι → Br := fun j => algebraMap B Br (algebraMap (MvPolynomial τ R₀) B (g j))
  have hgN : ∀ j, g j ∈ N := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L N (g j)).mp (hgm j)
  have hfm : ∀ j, f j ∈ maximalIdeal Br := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Br r _).mpr (by
      have := hgN j
      rwa [hNr, Ideal.mem_comap] at this)
  have hf : LinearIndependent r.ResidueField (fun j => (Ψ (f j)).snd) := by
    have : (fun j => (Ψ (f j)).snd) = fun j => algebraMap N.ResidueField r.ResidueField ∘
        (fun v => residue L (algebraMap (MvPolynomial τ R₀) L (pderiv v (g j)))) := by
      funext j v
      simp only [Ψ, f, IsLocalization.lift_eq, hΦ₂, Function.comp_apply,
        RingHom.algebraMap_toAlgebra]
      exact (Ideal.ResidueField.map_algebraMap N r _ hNr _).symm
    rw [this, linearIndependent_algebraMap_comp_iff]
    exact hjac
  have hreg := isRegularLocalRing_quotient_of_trivSqZeroExt Ψ hΨ f hfm hf
  have hideal : Ideal.span (Set.range f) =
      (N.map (algebraMap (MvPolynomial τ R₀) B)).map (algebraMap B Br) := by
    have hloc : (algebraMap B Br).comp (algebraMap (MvPolynomial τ R₀) B) =
        (Localization.localRingHom N r (algebraMap _ B) hNr).comp
          (algebraMap (MvPolynomial τ R₀) L) :=
      RingHom.ext fun x => (Localization.localRingHom_to_map N r _ hNr x).symm
    rw [Ideal.map_map, hloc, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal,
      ← hgspan, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (Localization.localRingHom_to_map N r _ hNr (g j)).symm
  rw [hideal] at hreg
  exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ N q).symm.toRingEquiv

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
