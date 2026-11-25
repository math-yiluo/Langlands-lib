import Langlands.MathlibBase

/-! # `H₁(L_{κ/A})` is the cotangent space `𝔪/𝔪²` of a local ring -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open IsLocalRing

open scoped TensorProduct

/-- The extension `A → κ(A)` of a local ring onto its residue field, with underlying ring `A`. -/
noncomputable abbrev residueExt (A : Type u) [CommRing A] [IsLocalRing A] :
    Algebra.Extension.{u} A (ResidueField A) where
  Ring := A
  σ x := (residue_surjective x).choose
  algebraMap_σ x := (residue_surjective x).choose_spec

variable (A : Type u) [CommRing A] [IsLocalRing A]

theorem residueExt_ker : (residueExt A).ker = maximalIdeal A := by
  ext x
  rw [RingHom.mem_ker]
  exact residue_eq_zero_iff x

/-- Every element of the conormal module of `A → κ(A)` lies in `H₁`, since `Ω_{A/A} = 0`. -/
theorem residueExt_h1Cotangentι_surjective :
    Function.Surjective (residueExt A).h1Cotangentι := by
  have : Subsingleton Ω[A⁄A] :=
    KaehlerDifferential.subsingleton_of_surjective (R := A) (S := A) fun x => ⟨x, rfl⟩
  intro z
  exact ⟨(⟨z, LinearMap.mem_ker.mpr (Subsingleton.elim _ _)⟩ :
    LinearMap.ker (residueExt A).cotangentComplex), rfl⟩

/-- `H₁(L_{κ(A)/A})` is identified with `H₁` of the extension `A → κ(A)`. -/
theorem residueExt_map_defaultHom_bijective :
    Function.Bijective (Algebra.Extension.H1Cotangent.map
      (Algebra.Extension.defaultHom _ _ (residueExt A))) := by
  let g : (residueExt A).Hom (Algebra.Generators.self A (ResidueField A)).toExtension :=
    { toRingHom := algebraMap A (MvPolynomial (ResidueField A) A)
      toRingHom_algebraMap := fun x => rfl
      algebraMap_toRingHom := fun x => by
        exact (Algebra.Generators.algebraMap_apply (P := Algebra.Generators.self A (ResidueField A))
          (MvPolynomial.C x)).trans (by rw [MvPolynomial.aeval_C]; rfl) }
  exact (Algebra.Extension.H1Cotangent.equiv (Algebra.Extension.defaultHom _ _ _) g).bijective

theorem residueExt_ker_le : (residueExt A).ker ≤ (maximalIdeal A).comap (AlgHom.id A A) := by
  rw [residueExt_ker]
  exact fun x hx => hx

/-- The comparison map from the conormal module of `A → κ(A)` to the cotangent space. -/
noncomputable def residueExtCotangentMap :
    (residueExt A).Cotangent →ₗ[ResidueField A] CotangentSpace A where
  toFun x := Ideal.mapCotangent (residueExt A).ker (maximalIdeal A) (AlgHom.id A A)
    (residueExt_ker_le A) x.val
  map_add' x y := map_add _ x.val y.val
  map_smul' c x := by
    change Ideal.mapCotangent (residueExt A).ker (maximalIdeal A) (AlgHom.id A A)
      (residueExt_ker_le A) ((residueExt A).σ c • x.val) = c • _
    rw [map_smul]
    conv_rhs => rw [← (residueExt A).algebraMap_σ c]
    exact (algebraMap_smul (ResidueField A) ((residueExt A).σ c) _).symm

theorem residueExtCotangentMap_apply (y : A) (hy : y ∈ (residueExt A).ker) :
    residueExtCotangentMap A
        (Algebra.Extension.Cotangent.of (Ideal.toCotangent (residueExt A).ker ⟨y, hy⟩)) =
      Ideal.toCotangent (maximalIdeal A) ⟨y, residueExt_ker_le A hy⟩ :=
  rfl

theorem residueExtCotangentMap_bijective : Function.Bijective (residueExtCotangentMap A) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨w, rfl⟩ : ∃ w, Algebra.Extension.Cotangent.of w = x :=
      ⟨x.val, Algebra.Extension.Cotangent.of_val x⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective (residueExt A).ker w
    rw [residueExtCotangentMap_apply, Ideal.toCotangent_eq_zero] at hx
    apply Algebra.Extension.Cotangent.ext
    rw [Algebra.Extension.Cotangent.val_of, Algebra.Extension.Cotangent.val_zero,
      Ideal.toCotangent_eq_zero]
    change y ∈ (residueExt A).ker ^ 2
    rw [residueExt_ker]
    exact hx
  · intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal A) z
    have hy' : y ∈ (residueExt A).ker := (residueExt_ker A).symm ▸ hy
    exact ⟨_, residueExtCotangentMap_apply A y hy'⟩

/-- `dim_κ H₁(L_{κ/A}) = dim_κ 𝔪/𝔪²` for a local ring `A` with residue field `κ`. -/
theorem rank_h1Cotangent_residueField :
    Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) =
      Module.rank (ResidueField A) (CotangentSpace A) := by
  let e₁ := LinearEquiv.ofBijective _ (residueExt_map_defaultHom_bijective A)
  let e₂ := LinearEquiv.ofBijective (residueExt A).h1Cotangentι
    ⟨Subtype.val_injective, residueExt_h1Cotangentι_surjective A⟩
  let e₃ := LinearEquiv.ofBijective _ (residueExtCotangentMap_bijective A)
  exact (e₁.trans (e₂.trans e₃)).rank_eq

/-- For a Noetherian local ring, `dim_κ H₁(L_{κ/A})` is the embedding dimension. -/
theorem rank_h1Cotangent_residueField_eq_finrank [IsNoetherianRing A] :
    Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) =
      Module.finrank (ResidueField A) (CotangentSpace A) := by
  rw [rank_h1Cotangent_residueField, Module.finrank_eq_rank]

end Faltings

end Langlands.CommutativeAlgebra.Popescu
