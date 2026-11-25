import Langlands.ClassFieldTheory.Global.ArchimedeanNormOneRadicals
import Langlands.GroupScheme.Rational.CentralMuLocalCorrection
import Langlands.GroupScheme.Rational.CentralNormOneKummerCocycle

/-! # Local corrections with norm-one torsion coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open GaloisPoint Langlands.Algebra Langlands.ClassFieldTheory.Global.TensorUnitShapiro

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Coefficients

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [Normal F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

/-- A cochain that twists the local restriction of a lifted cocycle into the central
kernel, together with the resulting crossed coefficients. -/
structure LocalCentralCorrection (ζ : Cocycle G (GaloisCocycle.cover F L)) where
  cochain : G.affinePoints (CommAlgCat.of F M)
  correction : Gal(M/K) → GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M)
  correction_spec : ∀ σ : Gal(M/K), hf.kernelPointInclusion M (correction σ) =
    cochain⁻¹ *
      relativeExtend F L M G (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)) *
      relativeConjugate F K M G σ cochain
  correction_mul : ∀ σ τ : Gal(M/K), correction (σ * τ) = correction σ *
    relativeConjugate F K M hf.commutativeKernel.toGrp σ (correction τ)

private theorem relativeExtend_value_mul [FiniteDimensional K M] [IsGalois K M]
    (ζ : Cocycle G (GaloisCocycle.cover F L)) (σ τ : Gal(M/K)) :
    relativeExtend F L M G (GaloisCocycle.value ζ (((σ * τ).restrictScalars F).restrictNormal L)) =
      relativeExtend F L M G (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)) *
      relativeConjugate F K M G σ
        (relativeExtend F L M G (GaloisCocycle.value ζ ((τ.restrictScalars F).restrictNormal L))) := by
  let ξ := GaloisCocycle.scalarExtension (K := K) (M := M) ζ
  let P := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) G
  have h := congrArg P (GaloisCocycle.value_mul ξ σ τ)
  simpa only [P, ξ, map_mul, GaloisCocycle.scalarExtensionPointsEquiv_conjugate,
    GaloisCocycle.value_scalarExtension] using h

/-- A local trivialization of the projection lifts over an algebraically closed
coefficient field and yields a local central correction of the source. -/
theorem nonempty_localCentralCorrection [IsAlgClosed M] [FiniteDimensional K M] [IsGalois K M]
    (ζ : Cocycle G (GaloisCocycle.cover F L))
    (h : ((ζ.map f).baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    Nonempty (hf.LocalCentralCorrection (K := K) (M := M) ζ) := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) (ζ.map f) h
  obtain ⟨x, hx⟩ := hf.exists_coeffPoint_lift_of_isAlgClosed y
  let A (σ : Gal(M/K)) := relativeExtend F L M G
    (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L))
  let g (σ : Gal(M/K)) := relativeConjugate F K M G σ
  let a (σ : Gal(M/K)) := x⁻¹ * A σ * g σ x
  let p := GroupScheme.affinePointsTarget G f (CommAlgCat.of F M)
  have hA (σ : Gal(M/K)) : p (A σ) = y * (relativeConjugate F K M H σ y)⁻¹ := by
    have hh := hy σ
    let b := GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)
    change GaloisCocycle.coverMap F L M ≫ (b ≫ f.hom.hom) = _ at hh
    change (GaloisCocycle.coverMap F L M ≫ b) ≫ f.hom.hom = _
    rw [Category.assoc]
    exact hh
  have hg (σ : Gal(M/K)) : p (g σ x) = relativeConjugate F K M H σ y := by
    change (GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ x) ≫ f.hom.hom =
      GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ y
    rw [Category.assoc, hx]
  have hp (σ : Gal(M/K)) : p (a σ) = 1 := by
    change p (x⁻¹ * A σ * g σ x) = 1
    rw [map_mul, map_mul, map_inv, show p x = y from hx, hA, hg]
    group
  have ha (σ τ : Gal(M/K)) : a (σ * τ) = a σ * g σ (a τ) := by
    change x⁻¹ * A (σ * τ) * g (σ * τ) x =
      (x⁻¹ * A σ * g σ x) * g σ (x⁻¹ * A τ * g τ x)
    rw [show A (σ * τ) = A σ * g σ (A τ) from relativeExtend_value_mul ζ σ τ,
      show g (σ * τ) x = g σ (g τ x) from relativeConjugate_mul F K M G σ τ x]
    simp only [map_mul, map_inv]
    group
  have hker (σ : Gal(M/K)) : ∃ c, hf.kernelPointInclusion M c = a σ :=
    (mem_range_kernelι_iff f _).mpr (hp σ)
  choose c hc using hker
  refine ⟨⟨x, c, hc, fun σ τ => ?_⟩⟩
  apply (cancel_mono (kernelι f).hom.hom).mp
  change hf.kernelPointInclusion M (c (σ * τ)) =
    hf.kernelPointInclusion M (c σ * relativeConjugate F K M hf.commutativeKernel.toGrp σ (c τ))
  have hσ : hf.kernelPointInclusion M (relativeConjugate F K M hf.commutativeKernel.toGrp σ (c τ)) =
      g σ (hf.kernelPointInclusion M (c τ)) :=
    Category.assoc (GaloisCocycle.arrow F M (σ.restrictScalars F)) (c τ) (kernelι f).hom.hom
  rw [map_mul, hσ, hc, hc, hc, ha]

end Coefficients

section Archimedean

variable {F B L : Type u} [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [Normal F L]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M]
  [Algebra F M] [Algebra L M] [IsScalarTower F v.Completion M] [IsScalarTower F L M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (n : ℕ) (e : kernel f ≅ WeilGm.normOneTorsion F B n)

local notation "Kv" => InfinitePlace.Completion v

/-- A norm-one correction has a local radical, its descended power and its scalar norm. -/
structure LocalNormOneCorrection (ζ : Cocycle G (GaloisCocycle.cover F L)) where
  coeff : hf.LocalCentralCorrection (K := Kv) (M := M) ζ
  radicand : (B ⊗[F] Kv)ˣ
  scalar : Kvˣ
  radical : (B ⊗[F] M)ˣ
  radical_pow : radical ^ n = extendTensorUnit M radicand
  radical_norm : tensorNormUnits F B M radical = Units.map (algebraMap Kv M).toMonoidHom scalar
  radicand_norm : tensorNormUnits F B Kv radicand = scalar ^ n
  unit_eq : ∀ σ : Gal(M/Kv),
    kernelTensorUnitMap (kernelNormOneToWeil n e) M (coeff.correction σ) =
      tensorCoboundary radical (σ.restrictScalars F)

/-- A trivial projection on the complete pullback cover provides a local correction
with actual tensor coordinates on an algebraically closed finite Galois coefficient field. -/
theorem nonempty_localNormOneCorrection [IsAlgClosed M] [FiniteDimensional v.Completion M]
    [IsGalois v.Completion M] (ζ : Cocycle G (GaloisCocycle.cover F L))
    (h : ((ζ.map f).baseChangePullback (Spec.algebraMap F Kv)).IsTrivial) :
    Nonempty (hf.LocalNormOneCorrection v (M := M) n e ζ) := by
  obtain ⟨d⟩ := hf.nonempty_localCentralCorrection (K := Kv) (M := M) ζ h
  let k := kernelNormOneToWeil n e
  let j := kernelTensorUnitMap k M
  let c (σ : Gal(M/Kv)) := j (d.correction σ)
  have hc (σ τ : Gal(M/Kv)) : c (σ * τ) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ := by
    change j (d.correction (σ * τ)) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ
    rw [d.correction_mul, map_mul]
    have hσ : j (relativeConjugate F Kv M hf.commutativeKernel.toGrp σ (d.correction τ)) =
        tensorAction F B M (σ.restrictScalars F) (c τ) :=
      kernelTensorUnitMap_naturality k (σ.restrictScalars F).toAlgHom (d.correction τ)
    rw [hσ, mul_comm]
  have hp (σ : Gal(M/Kv)) : c σ ^ n = 1 := kernelTensorUnitMap_pow_eq_one n e M (d.correction σ)
  have hN (σ : Gal(M/Kv)) : tensorNormUnits F B M (c σ) = 1 :=
    kernelTensorUnitMap_norm_eq_one n e M (d.correction σ)
  obtain ⟨x, b, s, hb, hs, hbs, hx⟩ := exists_archimedeanNormOneRadical v n c hc hp hN
  exact ⟨⟨d, b, s, x, hb, hs, hbs, fun σ => (hx σ).symm⟩⟩

end Archimedean

end Langlands.GroupScheme.IsCentralIsogeny
