import Mathlib

/-! # Étale coordinates from differentials

Let `B` be a smooth `A`-algebra and `θ : A →+* B` a ring map whose differentials `d θ(a)` span
`Ω[B⁄A]`. At every prime `q` of `B`, finitely many `g_i ∈ A` make `B` étale at `q` over the
polynomial ring `A[X_i]`, where `X_i ↦ θ(g_i)`. Conversely, at a prime where `B` is étale over
`A[X_i]`, the differentials of the `θ(g_i)` span the residue cotangent space.
-/

universe u

open TensorProduct IsLocalRing

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

section FormallyEtale

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  [Algebra S T] [IsScalarTower A S T]

/-- If `T` is formally smooth over `A` and `T ⊗_S Ω_{S/A} → Ω_{T/A}` is bijective, then `T` is
formally étale over `S`. -/
lemma formallyEtale_of_bijective_mapBaseChange [Algebra.FormallySmooth A T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange A S T)) :
    Algebra.FormallyEtale S T := by
  refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun x y ↦ ?_⟩⟩
  · have hz : ∀ z : Ω[T⁄S], z = 0 := by
      intro z
      obtain ⟨z, rfl⟩ := KaehlerDifferential.map_surjective A S T z
      obtain ⟨z, rfl⟩ := h.2 z
      have : KaehlerDifferential.mapBaseChange A S T z ∈
          LinearMap.ker (KaehlerDifferential.map A S T T) := by
        rw [← KaehlerDifferential.range_mapBaseChange]
        exact ⟨z, rfl⟩
      exact this
    rw [hz x, hz y]
  · have hz : ∀ z : Algebra.H1Cotangent S T, z = 0 := by
      intro z
      have h1 : Algebra.H1Cotangent.δ A S T z = 0 := by
        apply h.1
        rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange A S T _).mpr ⟨z, rfl⟩, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ A S T z).mp h1
      rw [← hw, Subsingleton.elim w 0, map_zero]
    rw [hz x, hz y]

/-- Let `T` be a formally smooth local `A`-algebra with `Ω[T⁄A]` finitely presented, and let `T`
be an algebra over the polynomial ring `A[X_i]`. If the elements `1 ⊗ d X_i` form a basis of
`κ ⊗ Ω[T⁄A]`, then `T` is formally étale over `A[X_i]`. -/
lemma formallyEtale_mvPolynomial {ι : Type*} [IsLocalRing T] [Algebra.FormallySmooth A T]
    [Module.FinitePresentation T Ω[T⁄A]] [Algebra (MvPolynomial ι A) T]
    [IsScalarTower A (MvPolynomial ι A) T]
    (hli : LinearIndependent (ResidueField T) fun i ↦
      (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T
        (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i)))
    (hsp : Submodule.span (ResidueField T) (Set.range fun i ↦
      (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T
        (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i))) = ⊤) :
    Algebra.FormallyEtale (MvPolynomial ι A) T := by
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange
    (fun i ↦ KaehlerDifferential.D A T (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i)))
    hli hsp (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  let b' := (KaehlerDifferential.mvPolynomialBasis A ι).baseChange T
  apply formallyEtale_of_bijective_mapBaseChange (A := A)
  have hX : ∀ i, KaehlerDifferential.mvPolynomialBasis A ι i =
      KaehlerDifferential.D A (MvPolynomial ι A) (MvPolynomial.X i) := fun i ↦
    Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X A ι i)
  have : KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) T =
      (b'.equiv b (Equiv.refl ι)).toLinearMap := by
    refine b'.ext fun i ↦ ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hb, Module.Basis.baseChange_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, hX, KaehlerDifferential.map_D]
  rw [this]
  exact LinearEquiv.bijective _

/-- `formallyEtale_mvPolynomial` with the images of the variables named `z i`. -/
lemma formallyEtale_mvPolynomial_of_eq {ι : Type*} [IsLocalRing T] [Algebra.FormallySmooth A T]
    [Module.FinitePresentation T Ω[T⁄A]] [Algebra (MvPolynomial ι A) T]
    [IsScalarTower A (MvPolynomial ι A) T] (z : ι → T)
    (hX : ∀ i, algebraMap (MvPolynomial ι A) T (MvPolynomial.X i) = z i)
    (hli : LinearIndependent (ResidueField T) fun i ↦
      (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (z i))
    (hsp : Submodule.span (ResidueField T) (Set.range fun i ↦
      (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (z i)) = ⊤) :
    Algebra.FormallyEtale (MvPolynomial ι A) T := by
  have h : (fun i ↦ (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T
      (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i))) =
      fun i ↦ (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (z i) :=
    funext fun i ↦ by rw [hX]
  exact formallyEtale_mvPolynomial (A := A) (h ▸ hli) (h ▸ hsp)

end FormallyEtale

section Coordinates

/-- If `s` spans `M` over a local ring `T`, then the elements `1 ⊗ m`, `m ∈ s`, span
`κ ⊗ M` over the residue field `κ`. -/
lemma span_one_tmul_eq_top {T M : Type*} [CommRing T] [IsLocalRing T] [AddCommGroup M]
    [Module T M] {s : Set M} (hs : Submodule.span T s = ⊤) :
    Submodule.span (ResidueField T) ((fun m ↦ (1 : ResidueField T) ⊗ₜ[T] m) '' s) = ⊤ := by
  set N := Submodule.span (ResidueField T) ((fun m ↦ (1 : ResidueField T) ⊗ₜ[T] m) '' s)
  have key : ∀ m ∈ Submodule.span T s, (1 : ResidueField T) ⊗ₜ[T] m ∈ N := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [tmul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [tmul_smul, ← algebraMap_smul (ResidueField T) a]
      exact N.smul_mem _ hx
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | tmul k m =>
    have : k ⊗ₜ[T] m = k • ((1 : ResidueField T) ⊗ₜ[T] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact N.smul_mem _ (key m (hs ▸ Submodule.mem_top))
  | add x y hx hy => exact add_mem hx hy

variable {A : Type u} {T : Type*} [CommRing A] [CommRing T] [IsLocalRing T] [Algebra A T]

/-- If the differentials of `θ(A)` span `Ω[T⁄A]`, some of them give a basis of `κ ⊗ Ω[T⁄A]`. -/
lemma exists_coordinates (θ : A →+* T)
    (hθ : Submodule.span T (Set.range fun a ↦ KaehlerDifferential.D A T (θ a)) = ⊤) :
    ∃ (ι : Type u) (g : ι → A),
      LinearIndependent (ResidueField T)
        (fun i ↦ (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (θ (g i))) ∧
      Submodule.span (ResidueField T) (Set.range fun i ↦
        (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (θ (g i))) = ⊤ := by
  obtain ⟨ι, g, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField T)
    (fun a : A ↦ (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T (θ a))
  refine ⟨ι, g, hli, ?_⟩
  rw [Function.comp_def] at hsp
  rw [hsp, ← span_one_tmul_eq_top hθ, ← Set.range_comp]
  rfl

/-- If `T` is formally étale over `A[X_i]`, the elements `1 ⊗ d X_i` span `κ ⊗ Ω[T⁄A]`. -/
lemma span_one_tmul_D_X_eq_top {ι : Type*} [Algebra (MvPolynomial ι A) T]
    [IsScalarTower A (MvPolynomial ι A) T] [Algebra.FormallyEtale (MvPolynomial ι A) T] :
    Submodule.span (ResidueField T) (Set.range fun i ↦
      (1 : ResidueField T) ⊗ₜ[T] KaehlerDifferential.D A T
        (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i))) = ⊤ := by
  have hsurj : LinearMap.range (KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) T) = ⊤ := by
    rw [KaehlerDifferential.range_mapBaseChange, LinearMap.ker_eq_top]
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
  have hX : ∀ i, KaehlerDifferential.mvPolynomialBasis A ι i =
      KaehlerDifferential.D A (MvPolynomial ι A) (MvPolynomial.X i) := fun i ↦
    Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X A ι i)
  have hspan : Submodule.span T (Set.range fun i ↦
      KaehlerDifferential.D A T (algebraMap (MvPolynomial ι A) T (MvPolynomial.X i))) = ⊤ := by
    rw [← hsurj, LinearMap.range_eq_map,
      ← ((KaehlerDifferential.mvPolynomialBasis A ι).baseChange T).span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 1
    ext i
    simp [Module.Basis.baseChange_apply, hX, KaehlerDifferential.map_D]
  have h := span_one_tmul_eq_top hspan
  rwa [← Set.range_comp] at h

end Coordinates

section EtaleCoordinates

variable {A : Type u} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Étale coordinates.** Let `B` be a smooth `A`-algebra and `θ : A →+* B` a ring map such that
the differentials of `θ(A)` span `Ω[B⁄A]`. For every prime `q` of `B` there are finitely many
`g_i ∈ A` such that `B` is étale at `q` over `A[X_i]`, where `X_i ↦ θ(g_i)`. -/
theorem exists_etale_coordinates [Algebra.Smooth A B] (θ : A →+* B)
    (hθ : Submodule.span B (Set.range fun a ↦ KaehlerDifferential.D A B (θ a)) = ⊤)
    (q : Ideal B) [q.IsPrime] :
    ∃ (ι : Type u) (_ : Finite ι) (g : ι → A),
      ∀ [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B],
        (∀ i, algebraMap (MvPolynomial ι A) B (MvPolynomial.X i) = θ (g i)) →
          Algebra.IsEtaleAt (MvPolynomial ι A) q := by
  let T := Localization.AtPrime q
  have hT : Submodule.span T (Set.range fun a ↦
      KaehlerDifferential.D A T ((algebraMap B T).comp θ a)) = ⊤ := by
    have := span_eq_top_of_isLocalizedModule T q.primeCompl
      (KaehlerDifferential.map A A B T) hθ
    rw [← Set.range_comp] at this
    convert this using 3
    ext a
    simp [KaehlerDifferential.map_D]
  obtain ⟨ι, g, hli, hsp⟩ := exists_coordinates ((algebraMap B T).comp θ) hT
  have hfin : Finite ι := Module.Finite.finite_basis (Module.Basis.mk hli hsp.ge)
  refine ⟨ι, hfin, g, fun hX ↦ ?_⟩
  have hX' : ∀ i, algebraMap (MvPolynomial ι A) T (MvPolynomial.X i) =
      (algebraMap B T).comp θ (g i) := fun i ↦ by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι A) B T, hX]
    rfl
  have : IsScalarTower A (MvPolynomial ι A) T := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B T,
      IsScalarTower.algebraMap_apply A (MvPolynomial ι A) B,
      ← IsScalarTower.algebraMap_apply (MvPolynomial ι A) B T]
  exact formallyEtale_mvPolynomial_of_eq (A := A) _ hX' hli hsp

/-- At a prime where `B` is étale over `A[X_i]`, with `X_i ↦ θ(g_i)`, the differentials of the
`θ(g_i)` span `κ(P) ⊗ Ω[B_P⁄A]`. -/
lemma residueSpan_eq_top_of_isEtaleAt {ι : Type*} (θ : A →+* B) (g : ι → A)
    [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B]
    (hX : ∀ i, algebraMap (MvPolynomial ι A) B (MvPolynomial.X i) = θ (g i))
    (P : Ideal B) [P.IsPrime] [Algebra.IsEtaleAt (MvPolynomial ι A) P] :
    Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range fun i ↦
      (1 : ResidueField (Localization.AtPrime P)) ⊗ₜ[Localization.AtPrime P]
        KaehlerDifferential.D A (Localization.AtPrime P)
          (algebraMap B (Localization.AtPrime P) (θ (g i)))) = ⊤ := by
  have : IsScalarTower A (MvPolynomial ι A) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime P),
        IsScalarTower.algebraMap_apply A (MvPolynomial ι A) B,
        ← IsScalarTower.algebraMap_apply (MvPolynomial ι A) B (Localization.AtPrime P)]
  have h := span_one_tmul_D_X_eq_top (A := A) (T := Localization.AtPrime P) (ι := ι)
  simpa only [IsScalarTower.algebraMap_apply (MvPolynomial ι A) B (Localization.AtPrime P),
    hX] using h

end EtaleCoordinates

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
