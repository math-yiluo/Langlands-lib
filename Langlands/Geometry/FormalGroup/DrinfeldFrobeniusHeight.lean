import Langlands.Geometry.FormalGroup.DrinfeldSignedFrameFrobenius
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderRationalMorphism
import Langlands.Geometry.FormalGroup.GlobalRationalHeight
import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyStatement

/-! # The actual signed height of Drinfeld's relative Frobenius -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open ValuativeRel ModuleLaw CentralSimple

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Integral

variable {κ S : Type u} [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] [CommRing S] [Algebra 𝒪[K] S]
variable {Λ : Type s} [Ring Λ] [Algebra 𝒪[K] Λ]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] κ σ}
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)

/-- The actual nonnegative comparison has rank `q^(n*dim)` after coefficient extension. -/
theorem shiftedFrameFrobeniusHom_height (E : OrderAction Λ M) (n : ℕ)
    (h : RelativeFrobeniusIsogenyStatement M p (f * n)) (ψ : κ →ₐ[𝒪[K]] S) :
    (shiftedFrameFrobeniusHom p hcard E n ψ).val.HasHeight (Nat.card 𝓀[K])
      (n * Nat.card σ) := by
  let θ := (frobenius K κ ^ (n : ℤ)).toAlgHom
  let hθ := frobenius_natCast_toRingHom K κ p hcard n
  let a := shift (n : ℤ) ψ
  let g := ((E.frobeniusHom p (f * n) θ hθ).val).map a
  have hg : g.HasHeight p ((f * n) * Nat.card σ) := (h θ hθ).map a
  have hg' : g.HasHeight (Nat.card 𝓀[K]) (n * Nat.card σ) := by
    exact ⟨hg.1, by simpa only [hcard, pow_mul, ← mul_assoc] using hg.2⟩
  apply Hom.hasHeight_of_isoSquare g _ (Iso.refl _) (frobeniusTargetIso E n ψ).toModuleIso
  · exact Hom.comp_id _
  · exact hg'

/-- The positive Frobenius tensor is presented by its integral map with denominator one. -/
def shiftedFrameFrobeniusHeightPresentation (π : 𝒪[K]) (E : OrderAction Λ M) (n : ℕ)
    (h : RelativeFrobeniusIsogenyStatement M p (f * n)) (ψ : κ →ₐ[𝒪[K]] S) :
    RationalHom.GlobalHeightPresentation π (Nat.card 𝓀[K])
      (OrderAction.RationalHom.ofHom (F := K) (shiftedFrameFrobeniusHom p hcard E n ψ)).val :=
  RationalHom.GlobalHeightPresentation.ofIntegral _ _
    (shiftedFrameFrobeniusHom_height p hcard E n h ψ)

/-- The positive presentation has index the exponent times the dimension of the frame. -/
theorem shiftedFrameFrobeniusHeightPresentation_index (π : 𝒪[K]) (E : OrderAction Λ M) (n : ℕ)
    (h : RelativeFrobeniusIsogenyStatement M p (f * n)) (ψ : κ →ₐ[𝒪[K]] S) (H : ℕ) :
    (shiftedFrameFrobeniusHeightPresentation p hcard π E n h ψ).index H = (n * Nat.card σ : ℕ) :=
  RationalHom.GlobalHeightPresentation.index_ofIntegral (H := H) _ _ _

end Integral

section Signed

variable {D κ S : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] [CommRing S] [Algebra 𝒪[K] S]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))
variable {a b : κ →ₐ[𝒪[K]] S}

include hRank

private theorem signedFrameFrobenius_globalHeight_of_nonneg (n : ℤ) (hn : 0 ≤ n)
    (e : shift n b = a) :
    ∃ P : RationalHom.GlobalHeightPresentation π (Nat.card 𝓀[K])
        (signedFrameFrobenius Φ p hcard hFrob n e).hom.val,
      P.index ((reducedDegree K D) ^ 2) = n * (reducedDegree K D : ℤ) := by
  lift n to ℕ using hn
  subst a
  rw [signedFrameFrobenius_natCast]
  have he := congrArg Subtype.val (shiftedFrameFrobeniusQuasiIsogeny_hom Φ p hcard n (hFrob n) b)
  rw [he]
  refine ⟨shiftedFrameFrobeniusHeightPresentation p hcard π Φ.val.order n (hRank n) b, ?_⟩
  simpa only [Nat.card_fin, Nat.cast_mul] using
    shiftedFrameFrobeniusHeightPresentation_index p hcard π Φ.val.order n (hRank n) b
      (reducedDegree K D ^ 2)

/-- The whole signed relative map has a global actual height presentation of index `n*d`. -/
theorem signedFrameFrobenius_globalHeight (hπ : algebraMap 𝒪[K] K π ≠ 0)
    (n : ℤ) (e : shift n b = a) :
    ∃ P : RationalHom.GlobalHeightPresentation π (Nat.card 𝓀[K])
        (signedFrameFrobenius Φ p hcard hFrob n e).hom.val,
      P.index ((reducedDegree K D) ^ 2) = n * (reducedDegree K D : ℤ) := by
  by_cases hn : 0 ≤ n
  · exact signedFrameFrobenius_globalHeight_of_nonneg Φ p hcard hFrob hRank n hn e
  · let g := signedFrameFrobenius Φ p hcard hFrob (-n) (shift_reverse e)
    obtain ⟨P, hP⟩ := signedFrameFrobenius_globalHeight_of_nonneg Φ p hcard hFrob hRank
      (-n) (by omega) (shift_reverse e)
    obtain ⟨Q, hQ⟩ := P.exists_inverse hπ Nat.card_pos
      (pow_pos (reducedDegree_pos K D) 2) (Φ.property.2.map b) (Φ.property.2.map a)
      g.toModuleQuasiIsogeny rfl
    have he : signedFrameFrobenius Φ p hcard hFrob n e = g.symm := by
      rw [signedFrameFrobenius, dite_eq_right hn]
      unfold g
      rw [signedFrameFrobenius_of_nonneg Φ p hcard hFrob (-n) (by omega)]
    rw [he]
    refine ⟨Q, hQ.trans ?_⟩
    rw [hP, neg_mul, neg_neg]

/-- On each test of the original cover, the actual signed Frobenius has height `n*d`. -/
theorem signedFrameFrobenius_hasConstantChartHeight (hπ : algebraMap 𝒪[K] K π ≠ 0)
    (n : ℤ) (e : shift n b = a) (s : Set S) (hs : Ideal.span s = ⊤) :
    BasicAtlas.RationalHom.HasConstantChartHeight
      (BasicAtlas.ofGlobalOrderQuasiIsogeny (signedFrameFrobenius Φ p hcard hFrob n e) s hs).hom.val
      π (Nat.card 𝓀[K]) (n * (reducedDegree K D : ℤ)) := by
  obtain ⟨P, hP⟩ := signedFrameFrobenius_globalHeight Φ p hcard hFrob hRank hπ n e
  rw [← hP]
  exact BasicAtlas.RationalHom.hasConstantChartHeight_ofGlobal P (Φ.property.2.map a) s hs

end Signed

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue
