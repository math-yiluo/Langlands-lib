import Langlands.Correspondence.Laumon.UnramifiedLines
import Langlands.Correspondence.Laumon.FieldMonodromyBaseChange
import Langlands.Correspondence.Laumon.CompletionGaloisProof
import Langlands.Weil.Local.SepClosedTopology

/-!
# Unramified lines from the field monodromy and ramification comparisons
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

-- Use the instances with which the lisse stalk functor was defined.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

namespace Langlands.Henniart.Laumon

open ProEtale Langlands.Henniart.LocalNumerical Langlands.Weil Langlands.Weil.Local.SepClosed

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

section Realization

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {ℓ : ℕ} [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ
local notation "s" => fieldGeometricPoint K Ω

/-- Realize a continuous character as monodromy of a lisse line. -/
private theorem exists_lisseLine_of_character (h : IsHomeomorph (fieldGaloisToAut K Ω))
    (θ : Gal(Ω/K) →ₜ* Eˣ) :
    ∃ G : LisseSheaf ℓ (Spec (.of K)),
      Module.finrank E (LisseMonodromy.StalkSpace s G) = 1 ∧
      ∀ σ v, fieldMonodromy ℓ K Ω G σ v = (θ σ : E) • v := by
  let e := MulEquiv.ofBijective (fieldGaloisToAut K Ω) h.bijective
  have he : Continuous e.symm := (h.homeomorph (fieldGaloisToAut K Ω)).symm.continuous
  let V := ULift.{u + 1} E
  let ρ : Representation E (Aut (Scheme.FiniteEtale.fiber s)) V :=
    (Algebra.lsmul E E V).toMonoidHom.comp
      ((Units.coeHom E).comp (θ.toMonoidHom.comp e.symm.toMonoidHom))
  have hρ (φ : Module.Dual E V) (v : V) : Continuous fun g ↦ φ (ρ g v) := by
    change Continuous fun g ↦ φ ((θ (e.symm g) : E) • v)
    simp only [map_smul, smul_eq_mul]
    exact ((Units.continuous_val.comp θ.continuous).comp he).mul continuous_const
  obtain ⟨G, b, hb⟩ :=
    (universalLisseMonodromy_isEquivalenceAt ℓ (Spec (.of K)) Ω s).essSurj V ρ hρ
  refine ⟨G, b.finrank_eq.trans (ULift.moduleEquiv.finrank_eq.trans (Module.finrank_self E)), ?_⟩
  intro σ v
  apply b.injective
  rw [map_smul]
  have eσ : e.symm (fieldGaloisToAut K Ω σ) = σ := e.symm_apply_apply σ
  exact (hb (fieldGaloisToAut K Ω σ) v).trans
    (congrArg (fun g ↦ (θ g : E) • b v) eσ)

end Realization

section Residue

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "X" => LaurentSeries k
local notation "ΩX" => SeparableClosure (LaurentSeries k)
local notation "E" => PadicAlgCl ℓ
local notation "W" => localWeilGroup X ΩX
local notation "F" => localGeometricFrobenius X ΩX

/-- A character trivial on inertia descends continuously along the residue degree. -/
private theorem exists_profiniteCharacter
    (χ : ladicUnramifiedCharacters X ΩX ℓ) :
    ∃ ψ : ProfiniteIntegers →ₜ* Eˣ,
      ∀ σ, ψ (localResidueDegree X ΩX σ) = χ.1 σ := by
  let q := localResidueDegree X ΩX
  have hker : q.toMonoidHom.ker ≤ χ.1.toMonoidHom.ker := by
    change (localResidueDegree X ΩX).toMonoidHom.ker ≤ _
    rw [localResidueDegree_ker]
    exact fun g hg ↦ χ.2.1 ⟨g, hg⟩
  let hsurj := localResidueDegree_surjective X ΩX
  let ψ := q.toMonoidHom.liftOfSurjective hsurj ⟨χ.1.toMonoidHom, hker⟩
  have hψ (σ : Gal(ΩX/X)) : ψ (q σ) = χ.1 σ :=
    q.toMonoidHom.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hsurj)
      ⟨χ.1.toMonoidHom, hker⟩ σ
  have hq := (localResidueDegree_isOpenMap X ΩX).isQuotientMap q.continuous hsurj
  have hcontinuous : Continuous ψ := hq.continuous_iff.mpr
    ((show (ψ ∘ q) = χ.1 from funext hψ).symm ▸ χ.1.continuous)
  exact ⟨⟨ψ, hcontinuous⟩, hψ⟩

private theorem profiniteCharacter_geometric (χ : ladicUnramifiedCharacters X ΩX ℓ)
    {ψ : ProfiniteIntegers →ₜ* Eˣ}
    (hψ : ∀ σ, ψ (localResidueDegree X ΩX σ) = χ.1 σ) :
    ψ (frobenius (Multiplicative.ofAdd 1)) = unramifiedScalar k ℓ χ := by
  rw [← localGeometricFrobenius_degree X ΩX]
  exact (congrArg ψ (localGeometricFrobenius X ΩX).property).symm.trans
    (hψ (localProjection X ΩX F))

private theorem unramifiedCharacter_on_weil (χ : ladicUnramifiedCharacters X ΩX ℓ)
    {ψ : ProfiniteIntegers →ₜ* Eˣ}
    (hψ : ∀ σ, ψ (localResidueDegree X ΩX σ) = χ.1 σ) (w : W) :
    χ.1 (localProjection X ΩX w) = unramifiedScalar k ℓ χ ^ localDegreeInt X ΩX w := by
  have hd : localDegree X ΩX w =
      (Multiplicative.ofAdd (1 : ℤ)) ^ localDegreeInt X ΩX w := by
    apply Multiplicative.toAdd.injective
    simp [localDegreeInt]
  calc
    χ.1 (localProjection X ΩX w) = ψ (frobenius (localDegree X ΩX w)) :=
      (hψ _).symm.trans (congrArg ψ w.property)
    _ = unramifiedScalar k ℓ χ ^ localDegreeInt X ΩX w := by
      rw [hd, map_zpow, map_zpow, profiniteCharacter_geometric k ℓ χ hψ]

end Residue

section Ends

variable (k : Type u) [Field k] [Finite k]

local notation "X" => LaurentSeries k
local notation "ΩX" => SeparableClosure (LaurentSeries k)
local notation "W" => localWeilGroup X ΩX
local notation "arith" => Galois.FiniteField.arithmetic k (AlgebraicClosure k)
local notation "geom" => Galois.FiniteField.geometric k (AlgebraicClosure k)

local instance : Algebra k (endField k) :=
  ((endRing k).subtype.comp (endConstantHom k)).toAlgebra

attribute [local instance] endClosureConstantAlgebra

local instance : IsScalarTower k (endField k) (endGenericClosure k) :=
  IsScalarTower.of_algebraMap_eq' rfl

private def baseClosureToEnd : AlgebraicClosure k →ₐ[k] endGenericClosure k :=
  letI : IsSepClosed (endGenericClosure k) := IsSepClosure.sep_closed (endField k)
  IsSepClosed.lift

private theorem baseClosureToEnd_mem (x : AlgebraicClosure k) :
    baseClosureToEnd k x ∈ endConstants k :=
  mem_algebraicClosure_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic x).algHom (baseClosureToEnd k))

private theorem arithmeticFrobenius_pow_apply (m : ℕ) (x : AlgebraicClosure k) :
    (arith ^ m) x = x ^ (Nat.card k ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, Galois.FiniteField.arithmetic_apply, ih, ← pow_mul, pow_succ]

/-- The signed power equation on end constants gives the Frobenius action on the embedded
algebraic closure of `k`. -/
private theorem endFrobenius_commutes (hRam : HenselianCompletionRamificationStatement.{u})
    (w : W) (x : AlgebraicClosure k) :
    baseClosureToEnd k ((geom ^ localDegreeInt X ΩX w) x) =
      completionRestriction k (localProjection X ΩX w) (baseClosureToEnd k x) := by
  let τ := completionRestriction k (localProjection X ΩX w)
  have hpow (y : AlgebraicClosure k) :
      (τ (baseClosureToEnd k y)) ^ (Nat.card k ^ (localDegreeInt X ΩX w).toNat) =
      (baseClosureToEnd k y) ^ (Nat.card k ^ (-localDegreeInt X ΩX w).toNat) :=
    (hRam k).2.2.1 w ⟨baseClosureToEnd k y, baseClosureToEnd_mem k y⟩
  change _ = τ (baseClosureToEnd k x)
  have hgeom : geom = arith⁻¹ := rfl
  generalize localDegreeInt X ΩX w = n at hpow ⊢
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast] at hpow ⊢
    simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, pow_one] at hpow
    rw [zpow_natCast, hgeom, inv_pow]
    let y := (arith ^ m)⁻¹ x
    calc
      baseClosureToEnd k y = (τ (baseClosureToEnd k y)) ^ (Nat.card k ^ m) := (hpow y).symm
      _ = τ (baseClosureToEnd k (y ^ (Nat.card k ^ m))) := by rw [map_pow, map_pow]
      _ = τ (baseClosureToEnd k x) := by
        rw [← arithmeticFrobenius_pow_apply]
        exact congrArg (fun t ↦ τ (baseClosureToEnd k t)) (AlgEquiv.apply_symm_apply _ _)
  | negSucc m =>
    change baseClosureToEnd k ((geom ^ (-((m + 1 : ℕ) : ℤ))) x) = _
    rw [zpow_neg, zpow_natCast, hgeom, inv_pow, inv_inv, arithmeticFrobenius_pow_apply, map_pow]
    simpa using (hpow x).symm

variable {ℓ : ℕ} [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

private theorem representation_zpow_scalar {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module E V]
    (ρ : Representation E Γ V) (g : Γ) (c : Eˣ) (h : ∀ v, ρ g v = (c : E) • v)
    (n : ℤ) (v : V) : ρ (g ^ n) v = ((c ^ n : Eˣ) : E) • v := by
  let μ : Eˣ →* (Module.End E V)ˣ := Units.map (Algebra.lsmul E E V).toMonoidHom
  have he : ρ.toHomUnits g = μ c := Units.ext (LinearMap.ext h)
  have he' : ρ.toHomUnits (g ^ n) = μ (c ^ n) := by simp only [map_zpow, he]
  exact congrArg (fun f : (Module.End E V)ˣ ↦ (f : Module.End E V) v) he'

private theorem endMonodromy_on_weil (hRam : HenselianCompletionRamificationStatement.{u})
    {G : LisseSheaf ℓ (Spec (.of k))} {c : Eˣ} (hG : IsUnramifiedLineFor k ℓ c G)
    (e : FourierEnd) (w : W)
    (v : LisseMonodromy.StalkSpace (fieldGeometricPoint (endField k) (endGenericClosure k))
      (G.upperStar ℓ (puncturedEndToBase k e))) :
    fieldMonodromy ℓ (endField k) (endGenericClosure k)
        (G.upperStar ℓ (puncturedEndToBase k e))
        (completionRestriction k (localProjection X ΩX w)) v =
      ((c ^ localDegreeInt X ΩX w : Eˣ) : E) • v := by
  let σ := geom ^ localDegreeInt X ΩX w
  let τ := completionRestriction k (localProjection X ΩX w)
  let b := fieldMonodromyBaseChange (L := endField k) (baseClosureToEnd k) G
  obtain ⟨x, rfl⟩ := b.surjective v
  calc
    _ = b (fieldMonodromy ℓ k (AlgebraicClosure k) G σ x) :=
      (fieldMonodromyBaseChange_commutes (baseClosureToEnd k) G σ τ
        (endFrobenius_commutes k hRam w) x).symm
    _ = _ := by
      rw [show σ = geom ^ localDegreeInt X ΩX w from rfl,
        representation_zpow_scalar _ geom c hG.2]
      exact b.map_smul _ _

private theorem endMonodromy_of_on_weil
    (h : IsHomeomorph (fieldGaloisToAut (endField k) (endGenericClosure k)))
    (χ : ladicUnramifiedCharacters X ΩX ℓ) (G : LisseSheaf ℓ (Spec (.of k)))
    (e : FourierEnd)
    (hW : ∀ w (v : LisseMonodromy.StalkSpace (fieldGeometricPoint (endField k) (endGenericClosure k))
      (G.upperStar ℓ (puncturedEndToBase k e))),
      fieldMonodromy ℓ (endField k) (endGenericClosure k)
          (G.upperStar ℓ (puncturedEndToBase k e))
          (completionRestriction k (localProjection X ΩX w)) v =
        (χ.1 (localProjection X ΩX w) : E) • v) :
    ∀ σ (v : LisseMonodromy.StalkSpace (fieldGeometricPoint (endField k) (endGenericClosure k))
      (G.upperStar ℓ (puncturedEndToBase k e))),
      fieldMonodromy ℓ (endField k) (endGenericClosure k)
          (G.upperStar ℓ (puncturedEndToBase k e)) (completionRestriction k σ) v =
        (χ.1 σ : E) • v := by
  intro σ v
  let t := fieldGeometricPoint (endField k) (endGenericClosure k)
  let H := G.upperStar ℓ (puncturedEndToBase k e)
  have hφ (φ : Module.Dual E (LisseMonodromy.StalkSpace t H)) :
      Continuous fun g : Gal(ΩX/X) ↦
        φ (fieldMonodromy ℓ (endField k) (endGenericClosure k) H (completionRestriction k g) v) :=
    ((universalLisseMonodromy_isEquivalenceAt ℓ (Spec (.of (endField k)))
      (endGenericClosure k) t).continuous_rep H φ v).comp
        (h.continuous.comp (henselianCompletionGalois k).continuous)
  have hc (φ : Module.Dual E (LisseMonodromy.StalkSpace t H)) :
      Continuous fun g : Gal(ΩX/X) ↦ φ ((χ.1 g : E) • v) := by
    simp only [map_smul, smul_eq_mul]
    exact (Units.continuous_val.comp χ.1.continuous).mul continuous_const
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro φ
  rw [map_sub, sub_eq_zero]
  exact congrFun ((localProjection_denseRange X ΩX).equalizer (hφ φ) (hc φ)
    (funext fun w ↦ congrArg φ (hW w v))) σ

end Ends

/-- The finite étale and completion ramification comparisons imply the unramified-line
monodromy statement. -/
def UnramifiedLineMonodromyReduction : Prop :=
  FiniteEtaleFieldMonodromyStatement.{u} →
    HenselianCompletionRamificationStatement.{u} →
    UnramifiedLineMonodromyStatement.{u}

theorem unramifiedLineMonodromy_of_comparisons : UnramifiedLineMonodromyReduction.{u} := by
  classical
  intro hFinite hRam k _ _ ℓ _ χ
  obtain ⟨ψ, hψ⟩ := exists_profiniteCharacter k ℓ χ
  let θ := ψ.comp (Galois.FiniteField.toProfiniteIntegers k)
  have hθ : θ (Galois.FiniteField.geometricFrobenius k) = unramifiedScalar k ℓ χ := by
    change ψ (Galois.FiniteField.profiniteEquivalence k (Galois.FiniteField.geometricFrobenius k)) = _
    rw [Galois.FiniteField.profiniteEquivalence_geometric]
    exact profiniteCharacter_geometric k ℓ χ hψ
  have hex : ∃ G, IsUnramifiedLineFor k ℓ (unramifiedScalar k ℓ χ) G := by
    obtain ⟨G, hr, hG⟩ := exists_lisseLine_of_character
      (hFinite k (AlgebraicClosure k)).1 θ
    exact ⟨G, hr, fun v ↦ hθ ▸ hG (Galois.FiniteField.geometricFrobenius k) v⟩
  have hline : IsUnramifiedLineFor k ℓ (unramifiedScalar k ℓ χ) (unramifiedLine k ℓ χ) := by
    rw [unramifiedLine, dite_eq_left hex]
    exact hex.choose_spec
  have hW := unramifiedCharacter_on_weil k ℓ χ hψ
  refine ⟨hline, fun e ↦ endMonodromy_of_on_weil k
    (hFinite (endField k) (endGenericClosure k)).1 χ (unramifiedLine k ℓ χ) e ?_, hW⟩
  intro w v
  rw [hW w]
  exact endMonodromy_on_weil k hRam hline e w v

end Langlands.Henniart.Laumon
