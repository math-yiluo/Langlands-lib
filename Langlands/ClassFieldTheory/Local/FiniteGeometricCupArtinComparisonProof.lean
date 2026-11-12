import Langlands.ClassFieldTheory.Local.CyclicCupArtinComparison
import Langlands.ClassFieldTheory.Local.NonnormalCupCorestriction
import Langlands.ClassFieldTheory.Local.FiniteArtinNorm
import Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparison

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

open Langlands.LocalClassField
open FiniteArtinTransferReduction
open scoped FiniteArtinSymbol

namespace FiniteArtinSymbol

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

/-- The actual norm image is killed by the carry symbol on the Galois
abelianization, without an abelian-extension assumption. -/
theorem normSubgroup_le_ker_abelianizedArtinSymbol :
    normSubgroup F.Carrier D ≤ (abelianizedArtinSymbol F D).ker := by
  intro a ha
  rw [MonoidHom.mem_ker]
  apply eq_of_forall_character (card_abelianized_galois_dvd F D)
  intro ψ
  have hp : Abelianization.lift (ψ.comp Abelianization.of) = ψ :=
    Abelianization.lift.apply_symm_apply ψ
  rw [← hp, character_abelianizedArtinSymbol, map_one, ofAdd_eq_one,
    symbolValue_eq_iff, map_zero, ZeroMemClass.coe_zero]
  rw [(cyclicClass_eq_zero_iff_mem_normSubgroup (ψ.comp Abelianization.of) a).mpr
    (normSubgroup_le_of_tower F.Carrier D
      (IntermediateField.fixedField (ψ.comp Abelianization.of).ker) ha), map_zero]

/-- The carry symbol descended to the actual determinant-norm quotient. -/
def abelianizedArtinQuotient :
    NormQuotient F.Carrier D →* Abelianization Gal(D/F.Carrier) :=
  QuotientGroup.lift _ (abelianizedArtinSymbol F D)
    (normSubgroup_le_ker_abelianizedArtinSymbol F D)

@[simp] theorem abelianizedArtinQuotient_projection (a : F.Carrierˣ) :
    abelianizedArtinQuotient F D (normQuotientProjection F.Carrier D a) =
      abelianizedArtinSymbol F D a := rfl

end FiniteArtinSymbol

section Cyclic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
  [IsCyclic Gal(D/F.Carrier)]

/-- Cyclic character separation identifies geometric inverse cup with the
carry symbol itself. -/
theorem geometricReciprocityOfCup_eq_symbol_of_isCyclic
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    geometricReciprocityOfCup F.Carrier D c h
        (normQuotientProjection F.Carrier D a) =
      FiniteArtinSymbol.abelianizedArtinSymbol F D a := by
  apply FiniteArtinSymbol.eq_of_forall_character
    (FiniteArtinSymbol.card_abelianized_galois_dvd F D)
  intro ψ
  have hp : Abelianization.lift (ψ.comp Abelianization.of) = ψ :=
    Abelianization.lift.apply_symm_apply ψ
  have h₁ := geometricReciprocityOfCup_character_of_isCyclic F D c hc h
    (ψ.comp Abelianization.of) a
  have h₂ := FiniteArtinSymbol.character_abelianizedArtinSymbol F D
    (ψ.comp Abelianization.of) a
  rw [hp] at h₁ h₂
  exact h₁.trans h₂.symm

/-- On a cyclic upper extension, carry reciprocity after forward cup is
inversion in the actual Galois abelianization. -/
theorem abelianizedArtinQuotient_cup_of_isCyclic
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (x : Abelianization Gal(D/F.Carrier)) :
    FiniteArtinSymbol.abelianizedArtinQuotient F D
        (abelianizationCupEquiv F.Carrier D c h x) = x⁻¹ := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (normSubgroup F.Carrier D)
    (abelianizationCupEquiv F.Carrier D c h x)
  change normQuotientProjection F.Carrier D a = _ at ha
  rw [← ha, FiniteArtinSymbol.abelianizedArtinQuotient_projection,
    ← geometricReciprocityOfCup_eq_symbol_of_isCyclic F D c hc h a, ha,
    geometricReciprocityOfCup_eq_inv]
  change ((abelianizationCupEquiv F.Carrier D c h).symm
    (abelianizationCupEquiv F.Carrier D c h x))⁻¹ = x⁻¹
  rw [MulEquiv.symm_apply_apply]

end Cyclic

section Tower

variable {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p)
  (D : Type u) [Field D]
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [Algebra F.Carrier D] [Algebra E.Carrier D] [IsScalarTower F.Carrier E.Carrier D]
  [FiniteDimensional F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier D] [FiniteDimensional E.Carrier D]
  [IsGalois F.Carrier D] [IsGalois E.Carrier D]

/-- Carry reciprocity on norm quotients commutes with actual field norms
through arbitrary finite middle fields. -/
theorem abelianizedArtinQuotient_norm (a : NormQuotient E.Carrier D) :
    FiniteArtinSymbol.abelianizedArtinQuotient F D
        (normQuotientTowerNorm F.Carrier E.Carrier D a) =
      Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)
        (FiniteArtinSymbol.abelianizedArtinQuotient E D a) := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    exact (FiniteArtinSymbol.abelianizedArtinSymbol_norm F E D a).symm

set_option maxRecDepth 2048 in
/-- The constructed forward cup equivalences commute with inclusion and
the actual determinant norm, without middle-field normality. -/
theorem abelianizationCupEquiv_corestriction_nonnormal
    (c : relativeCohomology F.Carrier D 2) (d : relativeCohomology E.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (hd : IsFundamentalClass E.Carrier D (FiniteArtinSymbol.relInv E D) d)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (k : Function.Bijective (relativeTateCup E.Carrier D (-2) d))
    (x : Abelianization Gal(D/E.Carrier)) :
    abelianizationCupEquiv F.Carrier D c h
        (Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier) x) =
      normQuotientTowerNorm F.Carrier E.Carrier D
        (abelianizationCupEquiv E.Carrier D d k x) := by
  exact congrArg Additive.toMul
    (abelianizationCupToNormQuotient_corestriction_nonnormal F.Carrier E.Carrier D
      (FiniteArtinSymbol.relInv F D) (FiniteArtinSymbol.relInv E D)
      (classFormationTransferLaws p (localInvariantFamily unramifiedH2Exhaustion p)
        canonicalClassFormation F E D).2 c d hc hd (Additive.ofMul x))

end Tower

section General

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

set_option maxRecDepth 2048 in
/-- Carry reciprocity after forward fundamental cup is inversion for every
finite Galois extension. -/
theorem abelianizedArtinQuotient_cup
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (x : Abelianization Gal(D/F.Carrier)) :
    FiniteArtinSymbol.abelianizedArtinQuotient F D
        (abelianizationCupEquiv F.Carrier D c h x) = x⁻¹ := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator Gal(D/F.Carrier)) x
  let H := Subgroup.zpowers g
  let E := IntermediateField.fixedField H
  let : Algebra (Padic p) E :=
    ((algebraMap F.Carrier E).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  have : IsScalarTower (Padic p) F.Carrier E := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let E' : PadicField.{u} p := PadicField.ofField E
  let : Algebra F.Carrier E'.Carrier := (inferInstance : Algebra F.Carrier E)
  let : Algebra E'.Carrier D := (inferInstance : Algebra E D)
  have : IsScalarTower (Padic p) F.Carrier E'.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E)
  have : IsScalarTower F.Carrier E'.Carrier D := (inferInstance : IsScalarTower F.Carrier E D)
  have : FiniteDimensional F.Carrier E'.Carrier := (inferInstance : FiniteDimensional F.Carrier E)
  have : FiniteDimensional E'.Carrier D := (inferInstance : FiniteDimensional E D)
  have : IsGalois E'.Carrier D := (inferInstance : IsGalois E D)
  let e : H ≃* Gal(D/E'.Carrier) := IntermediateField.subgroupEquivAlgEquiv H
  have : IsCyclic Gal(D/E'.Carrier) := isCyclic_of_surjective e e.surjective
  let σ : Gal(D/E'.Carrier) := e ⟨g, Subgroup.mem_zpowers g⟩
  have hσ : (AlgEquiv.restrictScalarsHom F.Carrier) σ = g := by
    apply AlgEquiv.ext
    intro a
    rfl
  have hof :
      Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)
        (Abelianization.of σ) = Abelianization.of g := by
    rw [Abelianization.map_of, hσ]
  let d := fundamentalClass E' D
  have hd := fundamentalClass_spec E' D
  let k := cup_bijective E' D d hd
  change FiniteArtinSymbol.abelianizedArtinQuotient F D
    (abelianizationCupEquiv F.Carrier D c h (Abelianization.of g)) =
      (Abelianization.of g)⁻¹
  have hcup := abelianizationCupEquiv_corestriction_nonnormal
    F E' D c d hc hd h k (Abelianization.of σ)
  rw [hof] at hcup
  have hnorm := abelianizedArtinQuotient_norm F E' D
    (abelianizationCupEquiv E'.Carrier D d k (Abelianization.of σ))
  have hcyc := abelianizedArtinQuotient_cup_of_isCyclic
    E' D d hd k (Abelianization.of σ)
  rw [hcup, hnorm, hcyc, map_inv, hof]

set_option maxRecDepth 2048 in
/-- Geometric inverse fundamental cup equals the actual arithmetic carry
symbol for arbitrary finite Galois extensions. -/
theorem geometricReciprocityOfCup_eq_symbol
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    geometricReciprocityOfCup F.Carrier D c h
        (normQuotientProjection F.Carrier D a) =
      FiniteArtinSymbol.abelianizedArtinSymbol F D a := by
  have hx := abelianizedArtinQuotient_cup F D c hc h
    (arithmeticReciprocityOfCup F.Carrier D c h
      (normQuotientProjection F.Carrier D a))
  change FiniteArtinSymbol.abelianizedArtinQuotient F D
    ((abelianizationCupEquiv F.Carrier D c h)
      ((abelianizationCupEquiv F.Carrier D c h).symm
        (normQuotientProjection F.Carrier D a))) = _ at hx
  rw [MulEquiv.apply_symm_apply, FiniteArtinSymbol.abelianizedArtinQuotient_projection] at hx
  exact hx.symm

end General

/-- The positive carry-character comparison for geometric inverse cup,
with its complete published telescope. -/
theorem finiteGeometricCupArtinCharacterComparison :
    FiniteGeometricCupArtinCharacterComparison.{u} := by
  intro p _ F D _ _ _ _ c hc h ψ a
  rw [geometricReciprocityOfCup_eq_symbol F D c hc h a,
    FiniteArtinSymbol.character_abelianizedArtinSymbol]

end Langlands.ClassFieldTheory.Local
