import Langlands.Representation.Archimedean.DiagonalEnvelopingFactors
import Langlands.Representation.Archimedean.DiagonalEnvelopingInjective
import Mathlib.RingTheory.Adjoin.Tower

/-! # Finiteness of the block Levi centre over the ambient centre -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

open Langlands.Algebra Langlands.GeneralLinear Langlands.Geometric MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

section Diagonal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

local notation "P" => MvPolynomial (DiagonalCoordinate n) ℂ
local notation "Image" => AlgHom.range (diagonalCenterPolynomial n)

private def matrixFactorDiagonalImage (i : ι) : VermaCentral.imA (n i) →ₐ[ℂ] Image :=
  ((rename (fun a : Fin (n i) => (⟨i, a⟩ : DiagonalCoordinate n))).comp (VermaCentral.imA (n i)).val).codRestrict Image (by
    rintro ⟨p, z, rfl⟩
    exact ⟨matrixFactorCenterInclusion n i z, diagonalCenterPolynomial_factor n i z⟩)

private theorem diagonalCoordinate_isIntegral (a : DiagonalCoordinate n) : IsIntegral Image (X a : P) := by
  obtain ⟨i, a⟩ := a
  have hx : IsIntegral (VermaCentral.imA (n i)) (X a : MvPolynomial (Fin (n i)) ℂ) :=
    IsIntegral.of_finite _ _
  let f : Fin (n i) → DiagonalCoordinate n := fun p => ⟨i, p⟩
  let ψ : MvPolynomial (Fin (n i)) ℂ →ₐ[ℂ] P := rename f
  have hm := IsIntegral.map_of_comp_eq (S := MvPolynomial (Fin (n i)) ℂ) (U := P)
    (matrixFactorDiagonalImage n i).toRingHom ψ.toRingHom rfl hx
  change IsIntegral Image (rename f (X a)) at hm
  rwa [rename_X] at hm

/-- The polynomial algebra on the diagonal is finite over the image of the centre. -/
theorem diagonalCenterImage_moduleFinite : Module.Finite Image P := by
  have : Algebra.IsIntegral Image P := by
    constructor
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      change IsIntegral Image (algebraMap ℂ P c)
      rw [IsScalarTower.algebraMap_apply ℂ Image P]
      exact isIntegral_algebraMap
    | add p q hp hq => exact hp.add hq
    | mul_X p a hp => exact hp.mul (diagonalCoordinate_isIntegral n a)
  have : Algebra.FiniteType Image P := Algebra.FiniteType.of_restrictScalars_finiteType ℂ Image P
  exact Algebra.IsIntegral.finite

/-- The diagonal centre map is a finite ring homomorphism. -/
theorem diagonalCenterPolynomial_finite : (diagonalCenterPolynomial n).toRingHom.Finite := by
  let e := (diagonalCenterPolynomialEquiv n).toRingEquiv
  have h : (algebraMap Image P).Finite :=
    (RingHom.finite_algebraMap (A := Image) (B := P)).mpr (diagonalCenterImage_moduleFinite n)
  have he : (diagonalCenterPolynomial n).toRingHom = (algebraMap Image P).comp e.toRingHom :=
    RingHom.ext fun z => rfl
  rw [he]
  exact h.comp e.finite

/-- The centre of a complex matrix product enveloping algebra is Noetherian. -/
theorem diagonalCenter_isNoetherian :
    IsNoetherianRing (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ n))) := by
  have hfg : (⊤ : Subalgebra ℂ Image).FG :=
    fg_of_fg_of_fg ℂ Image P (Algebra.FiniteType.out (R := ℂ) (A := P))
      (diagonalCenterImage_moduleFinite n).1 Subtype.val_injective
  have : IsNoetherianRing (⊤ : Subalgebra ℂ Image) := isNoetherianRing_of_fg hfg
  have : IsNoetherianRing Image := isNoetherianRing_of_ringEquiv _ (Subalgebra.topEquiv (R := ℂ)).toRingEquiv
  exact isNoetherianRing_of_ringEquiv _ (diagonalCenterPolynomialEquiv n).symm.toRingEquiv

end Diagonal

section Block

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {r : ℕ} (B : BlockShape r)

omit [Fintype ι] [DecidableEq ι] in
private theorem blockDiagonalCoord_injective : Function.Injective (blockDiagonalCoord B (ι := ι)) := by
  rintro ⟨⟨i, j⟩, a⟩ ⟨⟨i', j'⟩, a'⟩ h
  have he : (⟨i, B.index j a⟩ : DiagonalCoordinate (fun _ : ι => r)) = ⟨i', B.index j' a'⟩ := h
  have hi : i = i' := congrArg Sigma.fst he
  subst i'
  have ha : B.index j a = B.index j' a' := congrArg (fun b => b.2) he
  have hj : j = j' := by simpa using congrArg (blockIndex B) ha
  subst j'
  rw [(B.index j).injective ha]

local notation "G" => (fun _ : ι => r)
local notation "M" => blockRanks B ι
local notation "Zg" => Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : ι => r)))
local notation "Zm" => Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (blockRanks B ι)))

/-- The action of the ambient centre on the Levi centre through the standard block projection. -/
abbrev blockCenterAlgebra : Algebra Zg Zm :=
  (blockEnvelopingDecomposition B).centerProjection.toRingHom.toAlgebra

/-- The Levi enveloping centre is finite over the ambient enveloping centre via the projection. -/
theorem blockCenter_moduleFinite :
    letI := blockCenterAlgebra B (ι := ι)
    Module.Finite Zg Zm := by
  let P := MvPolynomial (DiagonalCoordinate G) ℂ
  have : IsNoetherianRing Zg := diagonalCenter_isNoetherian G
  let : Algebra Zg P := (diagonalCenterPolynomial G).toRingHom.toAlgebra
  have : Module.Finite Zg P := diagonalCenterPolynomial_finite G
  let : Algebra Zg Zm := blockCenterAlgebra B
  let f := (rename (blockDiagonalCoord B)).comp (diagonalCenterPolynomial M)
  let g : Zm →ₗ[Zg] P :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun z m => by
        rw [Algebra.smul_def, Algebra.smul_def]
        change f ((blockEnvelopingDecomposition B).centerProjection z * m) =
          diagonalCenterPolynomial G z * f m
        rw [map_mul]
        congr 1
        exact (diagonalCenterPolynomial_blockProjection B z).symm }
  exact Module.Finite.of_injective g ((rename_injective _ (blockDiagonalCoord_injective B)).comp
    (diagonalCenterPolynomial_injective M))

end Block

end Langlands.Archimedean.Kostant
