import Langlands.Galois.Local.SpectralProof
import Langlands.LocalField.Definitions
import Mathlib.NumberTheory.LocalField.Basic

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

@[instance_reducible]
def localRankOne : (valuation K).RankOne where
  hom' := IsRankLeOne.nonempty.some.emb.comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

@[instance_reducible]
def localNormedField : NontriviallyNormedField K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := localRankOne K
  exact Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem localNormedField_topology :
    (localNormedField K).toNormedField.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace K› := rfl

theorem localNormedField_complete :
    letI := localNormedField K
    CompleteSpace K := by
  let := localNormedField K
  infer_instance

theorem localNormedField_ultrametric :
    letI := localNormedField K
    IsUltrametricDist K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  infer_instance

theorem localNormedField_integer :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    (NormedField.valuation (K := K)).integer = (valuation K).integer := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  ext x
  exact Valued.toNormedField.norm_le_one_iff

theorem localNormedField_le (x y : K) :
    letI := localNormedField K
    ‖x‖ ≤ ‖y‖ ↔ valuation K x ≤ valuation K y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  exact Valued.toNormedField.norm_le_iff

open IsLocalRing in
def localResidueEquiv :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    ResidueField (baseIntegers K) ≃+* 𝓀[K] := by
  let := localNormedField K
  let := localNormedField_ultrametric K
  exact ResidueField.mapEquiv (RingEquiv.subringCongr (localNormedField_integer K))

open IsLocalRing in
theorem localResidue_finite :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    Finite (ResidueField (baseIntegers K)) := by
  let := localNormedField K
  let := localNormedField_ultrametric K
  exact Finite.of_equiv 𝓀[K] (localResidueEquiv K).symm.toEquiv

end Langlands.LocalGalois

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

abbrev closureIntegers := extensionIntegers K (AlgebraicClosure K)

def localClosureValuation : Valuation (AlgebraicClosure K) ℝ≥0 :=
  spectralValuation K (AlgebraicClosure K)

instance localClosureValuation_extends :
    (valuation K).HasExtension (localClosureValuation K) where
  val_isEquiv_comap x y := by
    change valuation K x ≤ valuation K y ↔
      spectralNorm K (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K) x) ≤
        spectralNorm K (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K) y)
    simp only [spectralNorm_extends]
    exact (localNormedField_le K x y).symm

def localIntegerMap : 𝒪[K] →+* closureIntegers K :=
  algebraMap (valuation K).valuationSubring (localClosureValuation K).valuationSubring

def localResidueClosureEquiv :
    ResidueField (closureIntegers K) ≃+* AlgebraicClosure 𝓀[K] := by
  letI := residueExtension_isAlgClosure K (AlgebraicClosure K)
  exact IsAlgClosure.equivOfEquiv _ _ (localResidueEquiv K)

omit [CharZero K] in
theorem localResidueClosureEquiv_base (x : ResidueField (baseIntegers K)) :
    localResidueClosureEquiv K (algebraMap _ (ResidueField (closureIntegers K)) x) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (localResidueEquiv K x) := by
  let := residueExtension_isAlgClosure K (AlgebraicClosure K)
  exact IsAlgClosure.equivOfEquiv_algebraMap _ _ (localResidueEquiv K) x

@[instance_reducible]
def standardResidueAlgebra : Algebra 𝓀[K] (ResidueField (closureIntegers K)) :=
  ((algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K))).comp
    (localResidueEquiv K).symm.toRingHom).toAlgebra

def localResidueClosureAlgEquiv :
    letI := standardResidueAlgebra K
    ResidueField (closureIntegers K) ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K] := by
  letI := standardResidueAlgebra K
  exact
    { localResidueClosureEquiv K with
      commutes' := by
        intro x
        change localResidueClosureEquiv K
            (algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K))
              ((localResidueEquiv K).symm x)) = _
        rw [localResidueClosureEquiv_base, RingEquiv.apply_symm_apply] }

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable {K k L M : Type*} [Field K] [Field k] [Field L] [Field M]
    [Algebra K L] [Algebra k M]

def semilinearAutCongr (b : K ≃+* k) (e : L ≃+* M)
    (h : ∀ x, e (algebraMap K L x) = algebraMap k M (b x)) :
    Gal(L/K) ≃* Gal(M/k) := by
  have hi (y : k) : e.symm (algebraMap k M y) = algebraMap K L (b.symm y) := by
    apply e.injective
    rw [e.apply_symm_apply, h, b.apply_symm_apply]
  exact
    { toFun := fun σ =>
        { e.symm.trans (σ.toRingEquiv.trans e) with
          commutes' := by
            intro y
            change e (σ (e.symm (algebraMap k M y))) = algebraMap k M y
            rw [hi, σ.commutes, h, b.apply_symm_apply] }
      invFun := fun τ =>
        { e.trans (τ.toRingEquiv.trans e.symm) with
          commutes' := by
            intro x
            change e.symm (τ (e (algebraMap K L x))) = algebraMap K L x
            rw [h, τ.commutes, hi, b.symm_apply_apply] }
      left_inv := by
        intro σ
        ext x
        change e.symm (e (σ (e.symm (e x)))) = σ x
        rw [e.symm_apply_apply, e.symm_apply_apply]
      right_inv := by
        intro τ
        ext y
        change e (e.symm (τ (e (e.symm y)))) = τ y
        rw [e.apply_symm_apply, e.apply_symm_apply]
      map_mul' := by
        intro σ τ
        ext y
        change e (σ (τ (e.symm y))) = e (σ (e.symm (e (τ (e.symm y)))))
        rw [e.symm_apply_apply] }

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

def integerInclusion (E : IntermediateField K L) :
    extensionIntegers K E →ₐ[baseIntegers K] extensionIntegers K L where
  toFun x := ⟨(x : E), by
    change spectralNorm K L (algebraMap E L (x : E)) ≤ 1
    rw [← spectralNorm.eq_of_tower (x : E)]
    exact x.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

instance integerInclusion_isLocalHom (E : IntermediateField K L) :
    IsLocalHom (integerInclusion K L E) where
  map_nonunit x hx := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K E))).mpr
    have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K L))).mp hx
    apply NNReal.eq
    have h' := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    change spectralNorm K L (algebraMap E L (x : E)) = 1 at h'
    change spectralNorm K E (x : E) = 1
    rwa [spectralNorm.eq_of_tower (L := L) (x : E)]

def residueInclusion (E : IntermediateField K L) :
    ResidueField (extensionIntegers K E) →ₐ[ResidueField (baseIntegers K)]
      ResidueField (extensionIntegers K L) :=
  ResidueField.mapAlgHom' (integerInclusion K L E)

end Langlands.LocalGalois

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

def localResidueTransport :
    Gal(ResidueField (closureIntegers K)/ResidueField (baseIntegers K)) ≃*
      Field.absoluteGaloisGroup 𝓀[K] :=
  semilinearAutCongr (localResidueEquiv K) (localResidueClosureEquiv K)
    (localResidueClosureEquiv_base K)

def absoluteResidueHom :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K] :=
  (localResidueTransport K).toMonoidHom.comp (residueHom K (AlgebraicClosure K))

def absoluteInertia : Subgroup (Field.absoluteGaloisGroup K) :=
  inertia K (AlgebraicClosure K)

instance absoluteInertia_normal : (absoluteInertia K).Normal :=
  inertia_normal K (AlgebraicClosure K)

end Langlands.LocalGalois

namespace Langlands.PadicField

open ValuativeRel IsLocalRing

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

abbrev residueField : Type u := by
  letI := T.valuativeRel
  exact 𝓀[F.Carrier]

abbrev closureIntegers : ValuationSubring (AlgebraicClosure F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact LocalGalois.closureIntegers F.Carrier

def absoluteResidueHom :
    Field.absoluteGaloisGroup F.Carrier →* Field.absoluteGaloisGroup (F.residueField T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteResidueHom F.Carrier

def absoluteInertia : Subgroup (Field.absoluteGaloisGroup F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteInertia F.Carrier

instance absoluteInertia_normal : (F.absoluteInertia T).Normal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteInertia_normal F.Carrier

end Langlands.PadicField
