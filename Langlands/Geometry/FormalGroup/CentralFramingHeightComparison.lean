import Langlands.Geometry.FormalGroup.CentralFramingHeightZero
import Langlands.Geometry.FormalGroup.RationalHeightFieldRank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Prime and central residue-cardinality normalization of the same rank height -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem Hom.exists_residueCard_power_of_constant_rank
    {C : Type c} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Finite (IsLocalRing.ResidueField C)]
    {S : Type v} [CommRing S] [Nontrivial S] [Algebra C S]
    {σ τ : Type} [Finite σ] [Finite τ]
    {M : ModuleLaw C S σ} {N : ModuleLaw C S τ}
    {π : C} {H r : ℕ} {g : Hom M N} (hπ : Irreducible π)
    (hM : M.HasPiHeight π (Nat.card (IsLocalRing.ResidueField C)) H) (hN : N.IsPiDivisible π)
    (hg : g.IsIsogeny) (hr : g.HasKernelRank r) :
    ∃ j : ℕ, r = Nat.card (IsLocalRing.ResidueField C) ^ j := by
  let : Nonempty (PrimeSpectrum S) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  let x : PrimeSpectrum S := Classical.arbitrary _
  let κ := CommAlgCat.of S x.asIdeal.ResidueField
  let φ := IsScalarTower.toAlgHom C S κ
  let y : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨P, hP⟩ := hr
  obtain ⟨j, hj⟩ := Hom.finrank_finiteKernel_eq_pow_residueCard hπ (hM.map φ) (hN.map φ)
    (hg.map φ) (P.baseChange φ)
  have h₁ : (P.baseChange φ).rank y = Module.finrank κ (P.baseChange φ).coordinateAlgebra :=
    congrFun Module.rankAtStalk_eq_finrank_of_free y
  have h₂ : (P.baseChange φ).rank y = r := (P.rank_baseChange φ y).trans (hP _)
  exact ⟨j, h₂.symm.trans (h₁.trans hj)⟩

namespace RationalSection

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [IsFractionRing O F] [Field K] [Algebra C K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction D M} {G : OrderAction D N}
variable {hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {ht : ∀ (a : C) (x : τ → R),
  G.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {U V : Opens (PrimeSpectrum R)} {p q H e l : ℕ} {π : C} {u : Cˣ}
namespace HeightPresentation

variable {z : RationalSection F M N U} {i : V ⟶ U}
variable (P : HeightPresentation (p : O) p (RationalSection.restrict i z))
variable (hz : IsOrderLinear E G z) (hπ : Irreducible (p : O)) (hM : M.IsPiDivisible (p : O))

/-- The actual centrally linear numerator has the same kernel algebra and rank. -/
theorem centralNumerator_hasHeight :
    ((P.orderNumerator hz hπ hM).centralNumerator (hs := hs) (ht := ht)).val.HasHeight
      p P.numeratorHeight := by
  let S := (coefficientStructurePresheaf R).obj (op V)
  let Q := P.orderNumerator hz hπ hM
  let f := (Q.centralNumerator (hs := hs) (ht := ht)).val
  obtain ⟨A, hA⟩ := P.numerator.2
  let ex : P.representative.kernelSetFunctor ≅ f.kernelSetFunctor :=
    Q.numerator.centralScalarsKernelIso (hs := OrderAction.centralTangent_overAlgebra (hs := hs) S)
      (ht := OrderAction.centralTangent_overAlgebra (hs := ht) S)
  exact ⟨Q.numerator.centralScalarsOverAlgebra_isIsogeny S Q.isIsogeny,
    ⟨{ coordinateAlgebra := A.coordinateAlgebra
       finite := A.finite
       projective := A.projective
       represents := A.represents.ofIso ex }, hA⟩⟩

/-- Rewriting a prime denominator as a uniformizer power changes the numerator by
an integral unit. Use the same actual kernel rank in the central normalization. -/
def centralWithHeight (j : ℕ) (hpK : (p : K) ≠ 0)
    (hcal : (p : C) = (u : C) * π ^ e) (hC : (E.centralModule hs).HasPiHeight π q H)
    (hf : ((P.orderNumerator hz hπ hM).centralNumerator (hs := hs) (ht := ht)).val.HasHeight q j) :
    HeightPresentation π q ((P.orderNumerator hz hπ hM).centralSection (K := K) (hs := hs) (ht := ht)) := by
  let S := (coefficientStructurePresheaf R).obj (op V)
  let n := P.exponent
  let Q := P.orderNumerator hz hπ hM
  let f := (Q.centralNumerator (hs := hs) (ht := ht)).val
  let g := Q.uniformizerNumerator (hs := hs) (ht := ht) u
  let L := (E.centralModule hs).overAlgebra S
  let J := (G.centralModule ht).overAlgebra S
  let v := (u ^ n)⁻¹
  have hg : g.HasHeight q j := by
    apply Hom.hasHeight_of_isoSquare f g (Iso.refl L) (J.scalarUnitIso v) _ hf
    change ((v : C) • f).comp (Hom.id L) = ((v : C) • Hom.id J).comp f
    rw [Hom.comp_id, Hom.smul_comp, Hom.id_comp]
  let hL := hC.map (IsScalarTower.toAlgHom C R S)
  exact ⟨e * n, g, j, e * n * H, hg, hL.scalarPower_height _, Q.represents_uniformizer hpK hcal⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F] in
private theorem denominatorHeight_eq_mul (hp : 1 < p) (hq : q = p ^ l) (x : V)
    (hcal : (p : C) = (u : C) * π ^ e) (hC : (E.centralModule hs).HasPiHeight π q H) :
    P.denominatorHeight = l * (e * P.exponent * H) := by
  let S := (coefficientStructurePresheaf R).obj (op V)
  let n := P.exponent
  let a := ((E.centralModule hs).overAlgebra S).scalarHom (π ^ (e * n))
  let b := (M.overAlgebra S).scalarHom ((p : O) ^ n)
  have ha : a.HasKernelRank (q ^ (e * n * H)) :=
    (hC.map (IsScalarTower.toAlgHom C R S)).scalarPower_rank _
  have hb : b.HasKernelRank (q ^ (e * n * H)) := by
    let hS := OrderAction.centralTangent_overAlgebra (E := E) (hs := hs) S
    have he : b.kernelSetFunctor ≅ a.kernelSetFunctor := by
      refine ((E.overAlgebra S).centralModule_scalarPowerKernelIso hS p n).trans ?_
      have heq : (p : C) ^ n = (↑(u ^ n) : C) * π ^ (e * n) := by
        rw [hcal, mul_pow, ← pow_mul]
        rfl
      change (((E.centralModule hs).overAlgebra S).scalarHom ((p : C) ^ n)).kernelSetFunctor ≅
        a.kernelSetFunctor
      rw [heq]
      exact ((E.centralModule hs).overAlgebra S).scalarKernelIso_unit_mul (u ^ n) (π ^ (e * n)) |>.symm
    obtain ⟨A, hA⟩ := ha
    exact ⟨{ coordinateAlgebra := A.coordinateAlgebra
             finite := A.finite
             projective := A.projective
             represents := A.represents.ofIso he.symm }, hA⟩
  let : Nontrivial ((Spec.structureSheaf R).presheaf.stalk x.val) :=
    (StructureSheaf.stalkIso R x.val).injective.nontrivial
  let : Nontrivial S := ((Spec.structureSheaf R).presheaf.germ V x.val x.property).hom.domain_nontrivial
  let : Nonempty (PrimeSpectrum S) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  let y : PrimeSpectrum S := Classical.arbitrary _
  obtain ⟨A, hA⟩ := P.denominator.2
  have hR : p ^ P.denominatorHeight = q ^ (e * n * H) :=
    (hA y).symm.trans ((Hom.hasKernelRank_iff b A _).mp hb y)
  rw [hq, ← pow_mul] at hR
  exact Nat.pow_right_injective hp hR

variable [IsDomain C] [IsDiscreteValuationRing C] [Finite (IsLocalRing.ResidueField C)]

/-- The same local presentation has central signed index `k` and prime signed index `l * k`,
where the central residue cardinality is `p^l`. -/
theorem exists_centralHeightPresentation (hp : 1 < p) (hpK : (p : K) ≠ 0)
    (hvarpi : Irreducible π) (hcal : (p : C) = (u : C) * π ^ e)
    (hq : Nat.card (IsLocalRing.ResidueField C) = p ^ l) (x : V)
    (hC : (E.centralModule hs).HasPiHeight π (Nat.card (IsLocalRing.ResidueField C)) H)
    (hG : (G.centralModule ht).IsPiDivisible π) :
    ∃ Q : HeightPresentation π (Nat.card (IsLocalRing.ResidueField C))
      ((P.orderNumerator hz hπ hM).centralSection (K := K) (hs := hs) (ht := ht)),
      P.index = (l : ℤ) * Q.index := by
  let S := (coefficientStructurePresheaf R).obj (op V)
  let f := ((P.orderNumerator hz hπ hM).centralNumerator (hs := hs) (ht := ht)).val
  let ψ := IsScalarTower.toAlgHom C R S
  let : Nontrivial ((Spec.structureSheaf R).presheaf.stalk x.val) :=
    (StructureSheaf.stalkIso R x.val).injective.nontrivial
  let : Nontrivial S := ((Spec.structureSheaf R).presheaf.germ V x.val x.property).hom.domain_nontrivial
  have hf := P.centralNumerator_hasHeight (hs := hs) (ht := ht) hz hπ hM
  obtain ⟨j, hj⟩ := Hom.exists_residueCard_power_of_constant_rank hvarpi (hC.map ψ) (hG.map ψ) hf.1 hf.2
  have hf' : f.HasHeight (Nat.card (IsLocalRing.ResidueField C)) j := ⟨hf.1, hj ▸ hf.2⟩
  let Q := P.centralWithHeight hz hπ hM j hpK hcal hC hf'
  refine ⟨Q, ?_⟩
  have hnum : P.numeratorHeight = l * j := by
    rw [hq, ← pow_mul] at hj
    exact Nat.pow_right_injective hp hj
  have hdenom := P.denominatorHeight_eq_mul hp hq x hcal hC
  change (P.numeratorHeight : ℤ) - P.denominatorHeight =
    (l : ℤ) * ((j : ℤ) - (e * P.exponent * H : ℕ))
  rw [hnum, hdenom, Nat.cast_mul, Nat.cast_mul, mul_sub]

end HeightPresentation

variable [IsDomain C] [IsDiscreteValuationRing C] [Finite (IsLocalRing.ResidueField C)]

/-- On the actual central section, signed height is divided by the residue degree.
Each prime-normalized value is a multiple of that positive degree. -/
theorem HasHeightFunction.centralScalarSection_divide (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hpK : (p : K) ≠ 0)
    {k : U → ℤ} (hk : HasHeightFunction (p : O) p z.val k)
    (hp : 1 < p) (hl : 0 < l) (hvarpi : Irreducible π) (hcal : (p : C) = (u : C) * π ^ e)
    (hq : Nat.card (IsLocalRing.ResidueField C) = p ^ l)
    (hC : (E.centralModule hs).HasPiHeight π (Nat.card (IsLocalRing.ResidueField C)) H)
    (hG : (G.centralModule ht).IsPiDivisible π) :
    HasHeightFunction π (Nat.card (IsLocalRing.ResidueField C))
      (centralScalarSection (hs := hs) (ht := ht) z hz hπ hpK) (fun x => k x / (l : ℤ)) ∧
      ∀ x, (l : ℤ) ∣ k x := by
  have hcompare (x : U) : ∃ (V : Opens (PrimeSpectrum R)) (_ : x.val ∈ V) (i : V ⟶ U)
      (Q : HeightPresentation π (Nat.card (IsLocalRing.ResidueField C))
        (RationalSection.restrict i (centralScalarSection (hs := hs) (ht := ht) z hz hπ hpK))),
      ∀ y : V, k ⟨y, leOfHom i y.property⟩ = (l : ℤ) * Q.index := by
    obtain ⟨V, hx, i, P, hP⟩ := hk x
    obtain ⟨Q, hQ⟩ := P.exists_centralHeightPresentation (hs := hs) (ht := ht) hz hπ z.source_divisible
      hp hpK hvarpi hcal hq ⟨x, hx⟩ hC hG
    let Q₀ := P.orderNumerator hz hπ z.source_divisible
    have he := centralScalarSection_isCentralScalarChange (hs := hs) (ht := ht) z hz hπ hpK V i Q₀
    refine ⟨V, hx, i, he.symm ▸ Q, fun y => ?_⟩
    rw [HeightPresentation.index_cast, hP, hQ]
  constructor
  · intro x
    obtain ⟨V, hx, i, Q, hQ⟩ := hcompare x
    refine ⟨V, hx, i, Q, fun y => ?_⟩
    change k ⟨y, leOfHom i y.property⟩ / (l : ℤ) = Q.index
    rw [hQ, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hl.ne')]
  · intro x
    obtain ⟨V, hx, i, Q, hQ⟩ := hcompare x
    exact ⟨Q.index, hQ ⟨x, hx⟩⟩

end RationalSection

end Langlands.FormalGroup.ModuleLaw
