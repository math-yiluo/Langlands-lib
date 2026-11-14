import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityStatement
import Langlands.AbelianScheme.CanonicalH1Primitive
import Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethProof
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof

/-!
# Dimensions of structure-sheaf cohomology of a product over a field

For smooth proper `X`, `Y` over a field `K`, structure-sheaf cohomology `Hⁿ(X, 𝒪_X)` is
finite-dimensional, `H⁰(X, 𝒪_X)` is one-dimensional when `X` is geometrically connected, and the
published coherent Künneth formula gives
`dim Hⁿ(X ⨯ Y, 𝒪) = ∑_{a + b = n} dim Hᵃ(X, 𝒪) · dim Hᵇ(Y, 𝒪)`. For an abelian scheme `A`
this yields `dim H²(A ⨯ A, 𝒪) = dim H²(A) + (dim H¹(A))² + dim H²(A)`, so every injective
`K`-linear map `H²(A) × ⨂² H¹(A) × H²(A) ⟶ H²(A ⨯ A, 𝒪)` is bijective
(`bijective_of_injective_degreeTwo`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)

open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard

section Generic

variable {K : Type u} [Field K] (X : Over (Spec (CommRingCat.of K)))

/-- Structure-sheaf cohomology of a proper scheme over a field is finite-dimensional. -/
instance finiteDimensional_structureCohomology [IsProper X.hom] (n : ℕ) :
    FiniteDimensional K (structureCohomology X n) :=
  (properCoherentCohomologyFinite K X.left X.hom inferInstance _
    (CechDegreeOne.isQuasicoherent_unit X.left) (fun _ => Module.Finite.self _)).1 n

/-- For a smooth, proper and geometrically connected `X` over a field, the structure map
`K ⟶ Γ(X, ⊤)` is bijective. -/
lemma bijective_structureRingHom [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] :
    Function.Bijective (structureRingHom X.hom).hom := by
  have : IsIso X.hom.appTop :=
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
      X.left (Spec (CommRingCat.of K)) X.hom inferInstance inferInstance inferInstance ⊤
  have : IsIso (structureRingHom X.hom) := by
    unfold structureRingHom
    infer_instance
  exact (asIso (structureRingHom X.hom)).commRingCatIsoToRingEquiv.bijective

/-- `H⁰(X, 𝒪_X)` is one-dimensional for `X` smooth, proper and geometrically connected over a
field. -/
lemma finrank_structureCohomology_zero [Smooth X.hom] [IsProper X.hom]
    [GeometricallyConnected X.hom] : Module.finrank K (structureCohomology X 0) = 1 := by
  let G := (relativeGlobalSections X.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)
  let g : G := (show Γ(X.left, ⊤) from 1)
  let f : K →ₗ[K] G := LinearMap.toSpanSingleton K G g
  have hf : ∀ r : K, (show Γ(X.left, ⊤) from f r) = (structureRingHom X.hom).hom r := by
    intro r
    change (structureRingHom X.hom).hom r * 1 = _
    rw [mul_one]
  have hbij : Function.Bijective f := by
    have h := bijective_structureRingHom X
    refine ⟨fun a b hab => h.1 ?_, fun y => ?_⟩
    · rw [← hf, ← hf, hab]
    · obtain ⟨r, hr⟩ := h.2 (show Γ(X.left, ⊤) from y)
      exact ⟨r, (hf r).trans hr⟩
  rw [((relativeCohomologyZeroIso X.hom).app _).toLinearEquiv.finrank_eq,
    ← (LinearEquiv.ofBijective f hbij).finrank_eq, Module.finrank_self]

/-- The pairs `(a, b)` of natural numbers with `a + b = n` are indexed by `Fin (n + 1)`. -/
def antidiagonalEquiv (n : ℕ) : Fin (n + 1) ≃ {ab : ℕ × ℕ // ab.1 + ab.2 = n} where
  toFun i := ⟨((i : ℕ), n - i), by omega⟩
  invFun ab := ⟨ab.1.1, by omega⟩
  left_inv i := Fin.ext rfl
  right_inv ab := Subtype.ext (Prod.ext rfl (by simp only; omega))

instance (n : ℕ) : Fintype {ab : ℕ × ℕ // ab.1 + ab.2 = n} :=
  Fintype.ofEquiv _ (antidiagonalEquiv n)

variable (Y : Over (Spec (CommRingCat.of K)))

/-- The external tensor product of the structure sheaves is the structure sheaf of the
product. -/
def externalTensorUnitIso :
    Langlands.Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (prod.fst : X ⨯ Y ⟶ X).left).obj
          (SheafOfModules.unit X.left.ringCatSheaf))
        ((Scheme.Modules.pullback (prod.snd : X ⨯ Y ⟶ Y).left).obj
          (SheafOfModules.unit Y.left.ringCatSheaf)) ≅
      SheafOfModules.unit (X ⨯ Y).left.ringCatSheaf :=
  (Langlands.Scheme.Modules.tensorFunctor _).mapIso
      (Iso.prod (Langlands.Scheme.Modules.pullbackUnitIso _)
        (Langlands.Scheme.Modules.pullbackUnitIso _)) ≪≫
    Langlands.Scheme.Modules.tensorLeftUnitor _

/-- **Dimension form of the coherent Künneth formula for structure sheaves.** -/
theorem finrank_structureCohomology_prod [Smooth X.hom] [IsProper X.hom] [Smooth Y.hom]
    [IsProper Y.hom] (n : ℕ) :
    Module.finrank K (structureCohomology (X ⨯ Y) n) =
      ∑ ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
        Module.finrank K (structureCohomology X ab.1.1) *
          Module.finrank K (structureCohomology Y ab.1.2) := by
  obtain ⟨e⟩ := coherentFieldExternalTensorKunneth K X Y (LineBundle.trivial X.left)
    (LineBundle.trivial Y.left) n
  have e' := ((relativeCohomology (X ⨯ Y).hom n).mapIso (externalTensorUnitIso X Y)).symm ≪≫ e
  have : ∀ a, FiniteDimensional K ((relativeCohomology X.hom a).obj
      (LineBundle.trivial X.left).obj) := fun a => finiteDimensional_structureCohomology X a
  have : ∀ b, FiniteDimensional K ((relativeCohomology Y.hom b).obj
      (LineBundle.trivial Y.left).obj) := fun b => finiteDimensional_structureCohomology Y b
  rw [e'.toLinearEquiv.finrank_eq, Module.finrank_directSum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact Module.finrank_tensorProduct

end Generic

section TensorPower

variable {K : Type u} [Field K] (H : Type*) [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- A basis of the second tensor power, from a basis of `H`. -/
def tensorPowerTwoBasis :
    Module.Basis (Fin 2 → Fin (Module.finrank K H)) K (⨂[K]^2 H) :=
  Basis.piTensorProduct (fun _ : Fin 2 => Module.finBasis K H)

instance finiteDimensional_tensorPower_two : FiniteDimensional K (⨂[K]^2 H) :=
  Module.Finite.of_basis (tensorPowerTwoBasis H)

omit [FiniteDimensional K H] in
lemma finrank_tensorPower_two [FiniteDimensional K H] :
    Module.finrank K (⨂[K]^2 H) = Module.finrank K H * Module.finrank K H := by
  rw [Module.finrank_eq_card_basis (tensorPowerTwoBasis H), Fintype.card_pi, Fin.prod_univ_two,
    Fintype.card_fin]

end TensorPower

section Abelian

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

instance isProper_prod_hom : IsProper (A.X ⨯ A.X).hom := by
  have : IsProper (prod.snd : A.X ⨯ A.X ⟶ A.X).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_prod A)
      (inferInstance : IsProper A.X.hom)
  rw [← Over.w (prod.snd : A.X ⨯ A.X ⟶ A.X)]
  infer_instance

/-- **The dimension of `H²(A × A, 𝒪)`.** For an abelian scheme `A` over a field,
`dim H²(A × A, 𝒪) = dim H²(A, 𝒪) + (dim H¹(A, 𝒪))² + dim H²(A, 𝒪)`. -/
theorem finrank_structureCohomology_prod_two :
    Module.finrank K (structureCohomology (A.X ⨯ A.X) 2) =
      Module.finrank K (structureCohomology A.X 2) +
        Module.finrank K (structureCohomology A.X 1) *
          Module.finrank K (structureCohomology A.X 1) +
        Module.finrank K (structureCohomology A.X 2) := by
  set f : ℕ → ℕ := fun a => Module.finrank K (structureCohomology A.X a) with hf
  have h0 : f 0 = 1 := finrank_structureCohomology_zero A.X
  have hsum : Module.finrank K (structureCohomology (A.X ⨯ A.X) 2) =
      ∑ ab : {ab : ℕ × ℕ // ab.1 + ab.2 = 2}, f ab.1.1 * f ab.1.2 :=
    finrank_structureCohomology_prod A.X A.X 2
  rw [hsum, ← (antidiagonalEquiv 2).sum_comp, Fin.sum_univ_three]
  change f 0 * f (2 - 0) + f 1 * f (2 - 1) + f 2 * f (2 - 2) = f 2 + f 1 * f 1 + f 2
  rw [h0]
  simp only [Nat.sub_zero]
  ring

/-- **Surjectivity from injectivity in degree two.** Any injective `K`-linear map
`H²(A) × ⨂² H¹(A) × H²(A) ⟶ H²(A × A)` is bijective, by the dimension count. -/
theorem bijective_of_injective_degreeTwo
    (Φ : (structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2)
    (hΦ : Function.Injective Φ) : Function.Bijective Φ := by
  have h : Module.finrank K (structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
      structureCohomology A.X 2) = Module.finrank K (structureCohomology (A.X ⨯ A.X) 2) := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_tensorPower_two,
      finrank_structureCohomology_prod_two]
    ring
  exact ⟨hΦ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp hΦ⟩

/-- The linear equivalence given by an injective degree-two comparison map. -/
def degreeTwoEquivOfInjective
    (Φ : (structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2)
    (hΦ : Function.Injective Φ) :
    (structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
      structureCohomology A.X 2) ≃ₗ[K] structureCohomology (A.X ⨯ A.X) 2 :=
  LinearEquiv.ofBijective Φ (bijective_of_injective_degreeTwo A Φ hΦ)

end Abelian

end Langlands.AbelianScheme
