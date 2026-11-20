import Langlands.Geometry.FormalGroup.PolarizedCoefficientCoherence
import Langlands.Geometry.FormalGroup.RationalTorsionSimilitude
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyIsoTransport
import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus

/-! # Coefficient and isometry transport of actual local torsion similitudes -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {π : O} {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}
variable {hM' : M'.IsPiDivisible π} {hN' : N'.IsPiDivisible π}
variable {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}
variable {P' : TorsionPrincipalPolarization hM'} {Q' : TorsionPrincipalPolarization hN'}

namespace Hom.IsTorsionSimilitude

/-- Transport through actual integral isometries leaves the integral multiplier unchanged. -/
theorem transportIso {f : Hom M N} {m : O} (hf : f.IsTorsionSimilitude P Q m)
    (a : Iso M M') (b : Iso N N')
    (ha : a.hom.IsTorsionSimilitude P P' 1) (hb : b.hom.IsTorsionSimilitude Q Q' 1) :
    (b.hom.comp (f.comp a.inv)).IsTorsionSimilitude P' Q' m := by
  simpa only [one_mul, mul_one] using hb.comp (hf.comp ha.inverse_isometry)

set_option maxHeartbeats 800000 in
/-- Coefficient pullback of an integral map on an open preserves the multiplier. -/
theorem openBaseChange {U : Opens (PrimeSpectrum R)} {f : OpenIntegralHom M N U} {m : O}
    (hf : f.IsTorsionSimilitude
      (P.baseChange (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
      (Q.baseChange (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))) m)
    (φ : R →ₐ[O] S) :
    (Hom.openBaseChange φ U f).IsTorsionSimilitude
      ((P.baseChange φ).baseChange (IsScalarTower.toAlgHom O S
        ((coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U)))))
      ((Q.baseChange φ).baseChange (IsScalarTower.toAlgHom O S
        ((coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U))))) m := by
  let α := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))
  let β := coefficientSectionMap φ U
  let δ := IsScalarTower.toAlgHom O S
    ((coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U)))
  let e := coefficientSectionMap_structural φ U
  let a := mapSquareIso M α β φ δ e
  let b := mapSquareIso N α β φ δ e
  exact (hf.baseChange β).transportIso a b
    (mapSquareIso_isometry α β P φ δ e) (mapSquareIso_isometry α β Q φ δ e)

end Hom.IsTorsionSimilitude

namespace RationalSection.HasLocalTorsionSimilitude

variable {C : Type w} [CommRing C] [Algebra C O]
variable {k : Type z} [Field k] [Algebra C k]
variable {p : C} {c : kˣ}
variable {hM₀ : M.IsPiDivisible (algebraMap C O p)} {hN₀ : N.IsPiDivisible (algebraMap C O p)}
variable {hM₁ : M'.IsPiDivisible (algebraMap C O p)} {hN₁ : N'.IsPiDivisible (algebraMap C O p)}
variable {P₀ : TorsionPrincipalPolarization hM₀} {Q₀ : TorsionPrincipalPolarization hN₀}
variable {P₁ : TorsionPrincipalPolarization hM₁} {Q₁ : TorsionPrincipalPolarization hN₁}
variable {U : Opens (PrimeSpectrum R)} {f : RationalSection F M N U}

/-- Actual coefficient pullback retains the same rational multiplier. -/
theorem baseChange (hf : HasLocalTorsionSimilitude p P₀ Q₀ f c) (φ : R →ₐ[O] S) :
    HasLocalTorsionSimilitude p (P₀.baseChange φ) (Q₀.baseChange φ)
      (RationalSection.baseChange φ U f) c := by
  intro x
  obtain ⟨V, hx, i, n, g, m, hg, heq, hm, hpol⟩ :=
    hf ⟨(coefficientSpectrumMap φ) (x : PrimeSpectrum S), x.property⟩
  refine ⟨(coefficientOpenMap φ).obj V, hx, (coefficientOpenMap φ).map i, n,
    Hom.openBaseChange φ V g, m, hg.openBaseChange φ, ?_, hm, hpol.openBaseChange φ⟩
  have h := congrArg (RationalSection.baseChange φ V) heq
  simpa only [map_smul, ← RationalSection.restrict_baseChange, RationalSection.baseChange_ofIntegral]
    using h

/-- Integral isometries of the two polarizations retain the same rational multiplier. -/
theorem transportIso (hf : HasLocalTorsionSimilitude p P₀ Q₀ f c)
    (a : Iso M M') (b : Iso N N')
    (ha : a.hom.IsTorsionSimilitude P₀ P₁ 1) (hb : b.hom.IsTorsionSimilitude Q₀ Q₁ 1) :
    HasLocalTorsionSimilitude p P₁ Q₁ (RationalSection.transportIso a b U f) c := by
  intro x
  obtain ⟨V, hx, i, n, g, m, hg, heq, hm, hpol⟩ := hf x
  let φ := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V))
  let aV := a.map φ
  let bV := b.map φ
  refine ⟨V, hx, i, n, bV.hom.comp (g.comp aV.inv), m, hg.transportIso aV bV, ?_, hm,
    hpol.transportIso aV bV (ha.baseChange φ) (hb.baseChange φ)⟩
  rw [restrict_transportIso]
  change (algebraMap O F (algebraMap C O p)) ^ n • RationalSection.comp
    (RationalSection.ofHom b.hom V)
    (RationalSection.comp (RationalSection.restrict i f) (RationalSection.ofHom a.inv V)) = _
  rw [← comp_smul, ← smul_comp, heq]
  change RationalSection.comp (RationalSection.ofIntegral V bV.hom)
    (RationalSection.comp (RationalSection.ofIntegral V g) (RationalSection.ofIntegral V aV.inv)) = _
  rw [comp_ofIntegral, comp_ofIntegral]

end RationalSection.HasLocalTorsionSimilitude

end Langlands.FormalGroup.ModuleLaw
