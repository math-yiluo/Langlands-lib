import Langlands.Geometry.FormalGroup.DrinfeldLineIntegralCentralizer
import Langlands.Geometry.FormalGroup.FieldScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.RationalEndAlgebra
import Langlands.Geometry.FormalGroup.ScalarIsogenyTensorInverse

/-! # The rational commutant of the reduced Lubin–Tate line -/

noncomputable section

namespace Langlands.FormalGroup

universe u

namespace LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing ModuleLaw
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance lineRationalCentralizerLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) {π : 𝒪[K]} (hπ : Irreducible π)

local notation "C" => SubfieldIntegerRing K D ι
local notation "H" => drinfeldLubinTateLine ι χ hL hπ
local notation "EndH" => ModuleLaw.Hom H H
local notation "EndK" => ModuleLaw.RationalHom K H H
local notation "nr" => RationalHom.ofHomEnd (F := K) (M := H)
local notation "fc" => drinfeldLineCoefficientEnd ι χ hL hπ

/-- The embedded coefficients act on the line's rational Hom. -/
def drinfeldLineRationalCoefficient : C →+* EndK := (nr).comp fc

variable (p : ℕ) [ExpChar κ p] {e : ℕ} (hcard : Nat.card 𝓀[K] = p ^ e)
variable (σ : L ≃ₐ[K] L)
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "τ" => subfieldIntegerFrobenius ι σ hL
local notation "tc" => drinfeldLineFrobeniusEnd ι χ hL hπ p hcard σ hσ

/-- The rational image of the line's arithmetic Frobenius. -/
def drinfeldLineRationalFrobenius : EndK := nr tc

local notation "f" => drinfeldLineRationalCoefficient ι χ hL hπ
local notation "t" => drinfeldLineRationalFrobenius ι χ hL hπ p hcard σ hσ
local notation "ιK" => algebraMap K EndK

/-- The reduced-degree power of the rational Frobenius is the field uniformizer. -/
theorem drinfeldLineRationalFrobenius_pow :
    t ^ CentralSimple.reducedDegree K D = ιK (algebraMap 𝒪[K] K π) := by
  rw [RationalHom.algebraMap_eq_smul_id, ← RationalHom.ofHom_scalarHom]
  change nr tc ^ CentralSimple.reducedDegree K D = nr ((H).scalarHom π)
  rw [← (nr).map_pow]
  apply congrArg nr
  let forget : EndH →+* CommLaw.Hom (H).groupLaw (H).groupLaw :=
    { toFun := Hom.toHom, map_zero' := rfl, map_one' := rfl,
      map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
  apply Hom.ext
  change forget (tc ^ CentralSimple.reducedDegree K D) = forget ((H).scalarHom π)
  rw [map_pow]
  change (tc).toHom ^ CentralSimple.reducedDegree K D = ((H).scalarHom π).toHom
  rw [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id]
  exact drinfeldLubinTateFrobenius_pow ι χ hL hπ p hcard σ hσ

/-- Arithmetic Frobenius is invertible on the actual rational Hom. -/
def drinfeldLineRationalFrobeniusUnit : EndKˣ :=
  (show IsUnit t by
    apply (isUnit_pow_iff (reducedDegree_pos K D).ne').mp
    rw [drinfeldLineRationalFrobenius_pow]
    exact (isUnit_iff_ne_zero.mpr (show algebraMap 𝒪[K] K π ≠ 0 by
      simpa only [map_zero] using (IsFractionRing.injective 𝒪[K] K).ne hπ.ne_zero)).map ιK).unit

@[simp]
theorem drinfeldLineRationalFrobeniusUnit_val :
    ↑(drinfeldLineRationalFrobeniusUnit ι χ hL hπ p hcard σ hσ) = t := IsUnit.unit_spec _

/-- The rationalized arithmetic Frobenius intertwines each coefficient with its arithmetic image. -/
theorem drinfeldLineRationalFrobenius_mul (a : C) : t * f a = f (τ a) * t := by
  change nr tc * nr (fc a) = nr (fc (τ a)) * nr tc
  rw [← (nr).map_mul, ← (nr).map_mul]
  apply congrArg nr
  exact Hom.ext (drinfeldLubinTateFrobenius_mul ι χ hL hπ p hcard σ hσ a)

/-- Iterated arithmetic Frobenius obeys the corresponding iterated coefficient relation. -/
theorem drinfeldLineRationalFrobenius_pow_mul (n : ℕ) (a : C) :
    t ^ n * f a = f ((τ ^ n) a) * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, drinfeldLineRationalFrobenius_mul, mul_assoc]
    congr 2
    rw [pow_succ', AlgEquiv.mul_apply]

/-- The subalgebra of rational maps commuting with the embedded coefficients and arithmetic Frobenius. -/
def drinfeldLineRationalCentralizer : Subalgebra K EndK :=
  Subalgebra.centralizer K (Set.range f ∪ {t})

theorem mem_drinfeldLineRationalCentralizer (z : EndK) :
    z ∈ drinfeldLineRationalCentralizer ι χ hL hπ p hcard σ hσ ↔
    (∀ a : C, Commute z (f a)) ∧ Commute z t := by
  change z ∈ Subalgebra.centralizer K (Set.range f ∪ {t}) ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hz
    exact ⟨fun a => (hz _ (Or.inl ⟨a, rfl⟩)).symm, (hz _ (Or.inr rfl)).symm⟩
  · rintro ⟨hz, ht⟩ _ (⟨a, rfl⟩ | rfl)
    exacts [(hz a).symm.eq, ht.symm.eq]

variable [Algebra.IsAlgebraic 𝓀[K] κ]

include hcard in
/-- Field scalars embed in the actual rational endomorphisms of the reduced line. -/
theorem drinfeldLineRationalScalar_injective : Function.Injective ιK := by
  have hne : (1 : EndK) ≠ 0 := by
    intro h
    have hi : Function.Injective nr := RationalHom.ofHom_injective_of_isPiDivisible hπ
      (drinfeldLine_isPiDivisible ι χ hL hπ p hcard)
    have he : (1 : EndH) = 0 := by
      apply hi
      rw [map_one, map_zero]
      exact h
    have hd := congrArg (fun g : EndH => CommLaw.Hom.lineDerivative (H).groupLaw g.toHom) he
    change CommLaw.Hom.lineDerivative (H).groupLaw 1 = CommLaw.Hom.lineDerivative (H).groupLaw 0 at hd
    exact one_ne_zero (by simpa only [map_one, map_zero] using hd)
  let : Nontrivial EndK := ⟨⟨1, 0, hne⟩⟩
  exact (ιK).injective

/-- The full rational commutant of the line is the original scalar field. -/
def drinfeldLineRationalScalarEndEquiv : K ≃ₐ[K] drinfeldLineRationalCentralizer ι χ hL hπ p hcard σ hσ := by
  let S := drinfeldLineRationalCentralizer ι χ hL hπ p hcard σ hσ
  let scalar : K →ₐ[K] S := Algebra.ofId K S
  refine AlgEquiv.ofBijective scalar ⟨?_, ?_⟩
  · intro a b hab
    exact drinfeldLineRationalScalar_injective ι χ hL hπ p hcard (congrArg Subtype.val hab)
  · intro z
    have hz := (mem_drinfeldLineRationalCentralizer ι χ hL hπ p hcard σ hσ z.val).mp z.property
    obtain ⟨n, g, hg⟩ := RationalHom.exists_uniformizerPower_ofHom hπ z.val
    let r : K := (algebraMap 𝒪[K] K π) ^ n
    have hr : r ≠ 0 := pow_ne_zero n (by
      simpa only [map_zero] using (IsFractionRing.injective 𝒪[K] K).ne hπ.ne_zero)
    have hcomm (b : EndH) (hb : Commute z.val (nr b)) : Commute g b := by
      apply (RationalHom.ofHom_injective_of_isPiDivisible (F := K) hπ
        (drinfeldLine_isPiDivisible ι χ hL hπ p hcard))
      change nr (g * b) = nr (b * g)
      rw [map_mul, map_mul]
      change (RationalHom.ofHom g).comp (RationalHom.ofHom b) =
        (RationalHom.ofHom b).comp (RationalHom.ofHom g)
      rw [← hg, RationalHom.smul_comp, RationalHom.comp_smul]
      exact congrArg (r • ·) hb.eq
    let g' : drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ :=
      ⟨g, (mem_drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ g).mpr
        ⟨fun b => hcomm (fc b) (hz.1 b), hcomm tc hz.2⟩⟩
    let equiv := drinfeldLineScalarEndEquiv ι χ hL hπ p hcard σ hσ
    let a := equiv.symm g'
    have ha : (H).scalarHom a = g := congrArg Subtype.val (equiv.apply_symm_apply g')
    refine ⟨r⁻¹ * algebraMap 𝒪[K] K a, Subtype.ext ?_⟩
    change ιK (r⁻¹ * algebraMap 𝒪[K] K a) = z.val
    rw [map_mul (ιK), ← Algebra.smul_def, RationalHom.algebraMap_eq_smul_id,
      ← RationalHom.ofHom_scalarHom, ha, ← hg]
    exact inv_smul_smul₀ hr z.val

@[simp]
theorem drinfeldLineRationalScalarEndEquiv_val (a : K) :
    (drinfeldLineRationalScalarEndEquiv ι χ hL hπ p hcard σ hσ a).val = ιK a := rfl

end LocalDivision
end Langlands.FormalGroup
