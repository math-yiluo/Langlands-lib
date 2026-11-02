import Langlands.Global.Arithmetic.HarrisPlaceFromEmbedding
import Langlands.Global.Arithmetic.CMSubfield

/-!
# Two conjugate place pairs from compatible embeddings

Given compatible embeddings `E → F`, `E' → F'`, `L → F̃` of a tower of CM fields, a compatible
Galois comparison `Gal(L / E) ≃* Gal(F̃ / F)`, an automorphism `t` of the tower commuting with
`Gal(L / E)`, and an extension of complex conjugation to `L`, the embeddings and their twists by
`t` give two Harris place data. Elements `x_a, x_d` of `E` sent into `ℚ_[p]` with
`c x_a = -x_a`, `c x_d = x_d`, `t x_a = x_a` and `t x_d = -x_d` separate the four places
`v, c(v), v_s, c(v_s)`.
-/

noncomputable section

universe uF

namespace Langlands.Global.CMRealization

open NumberField IsDedekindDomain AdelicFunctoriality FieldRealization
open Harris LocalFactor.CommonClosure GeneralPosition

/-- Two `ℚ_[p]`-generating embeddings cutting out `v` and `v'` differ as places when they
send a nonzero element to opposite values, the first one in `ℚ_[p]`. -/
theorem ne_of_neg_place (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [NumberField E]
    {F₀ : Type*} [Field F₀] [Algebra ℚ_[p] F₀] [FiniteDimensional ℚ_[p] F₀] (j j' : E →+* F₀)
    (h : Algebra.adjoin ℚ_[p] (Set.range j) = ⊤) (h' : Algebra.adjoin ℚ_[p] (Set.range j') = ⊤)
    {v v' : HeightOneSpectrum (𝓞 E)}
    (hv : ∀ a : 𝓞 E, a ∈ v.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j a) < 1)
    (hv' : ∀ a : 𝓞 E, a ∈ v'.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j' a) < 1)
    {x : E} (hx0 : x ≠ 0) {r : ℚ_[p]} (hx : j x = algebraMap ℚ_[p] F₀ r)
    (hneg : j' x = -j x) : v ≠ v' := by
  refine ne_of_place_eq p j j' h h' hv hv' hx ?_
  rw [hneg]
  intro heq
  have : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F₀).injective
  have h2 : (2 : F₀) * j x = 0 := by linear_combination -heq
  exact hx0 (by simpa using h2)

theorem pairwise_ne_four {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : List.Pairwise (· ≠ ·) [a, b, c, d] := by
  simp [hab, hac, had, hbc, hbd, hcd]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
  {E E' L : Type*} [Field E] [Field E'] [Field L] [NumberField E] [NumberField E']
  [NumberField L] [IsCMField E] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsScalarTower E E' L] [IsGalois E L]

/-- The two compatible Harris place data and their conjugates, from compatible embeddings
twisted by an automorphism `t` of the tower. -/
theorem pairedPlaces_of_embeddings (jE : E →+* F.Carrier) (jE' : E' →+* F'.field)
    (jL : L →+* (galoisClosure F F').field) (hE : Algebra.adjoin ℚ_[p] (Set.range jE) = ⊤)
    (hE' : Algebra.adjoin F.Carrier (Set.range jE') = ⊤)
    (hL : Algebra.adjoin F.Carrier (Set.range jL) = ⊤)
    (hcE : ∀ x : E,
      jL (algebraMap E L x) = algebraMap F.Carrier (galoisClosure F F').field (jE x))
    (hcE' : ∀ y : E', ((jL (algebraMap E' L y) : (galoisClosure F F').field) :
      AlgebraicClosure F.Carrier) = ((jE' y : F'.field) : AlgebraicClosure F.Carrier))
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field))
    (hθ : ∀ σ x, θ σ (jL x) = jL (σ x))
    (t : E ≃+* E) (t' : E' ≃+* E') (tL : L ≃+* L)
    (ht : ∀ x : E, tL (algebraMap E L x) = algebraMap E L (t x))
    (ht' : ∀ y : E', tL (algebraMap E' L y) = algebraMap E' L (t' y))
    (htσ : ∀ (σ : L ≃ₐ[E] L) (x : L), σ (tL x) = tL (σ x))
    (cL : L ≃+* L)
    (hc : ∀ x : E, cL (algebraMap E L x) = algebraMap E L (IsCMField.complexConj E x))
    {xa xd : E} {ra rd : ℚ_[p]} (hxa : jE xa = algebraMap ℚ_[p] F.Carrier ra)
    (hxd : jE xd = algebraMap ℚ_[p] F.Carrier rd) (hxa0 : xa ≠ 0) (hxd0 : xd ≠ 0)
    (hca : IsCMField.complexConj E xa = -xa) (hcd : IsCMField.complexConj E xd = xd)
    (hta : t xa = xa) (htd : t xd = -xd) :
    letI := F.canonicalTopology
    letI := (fieldData F F').topology
    letI := (fieldData F (galoisClosure F F')).topology
    ∃ (P Ps : PlaceDatum F F' E E' L)
      (φ : FiniteCompletion E' P.v' ≃+* F'.field)
      (φs : FiniteCompletion E' Ps.v' ≃+* F'.field),
      List.Pairwise (· ≠ ·) [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v] ∧
      (∀ v ∈ [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v],
        (p : 𝓞 E) ∈ v.asIdeal ∧ HasUniquePlaceAbove L v) ∧
      (∀ Q ∈ [P, Ps],
        Q.IsCompatible ∧
        Continuous Q.iso ∧ Continuous Q.iso.symm ∧
        Continuous Q.isoTilde ∧ Continuous Q.isoTilde.symm ∧
        ∀ (σ : L ≃ₐ[E] L) (x : L),
          θ σ (Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) x)) =
            Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) (σ x))) ∧
      Continuous φ ∧ Continuous φ.symm ∧
      Continuous φs ∧ Continuous φs.symm ∧
      (∀ x : FiniteCompletion E P.v,
        φ (FiniteExtension.completionMap P.v P.v' x) =
          algebraMap F.Carrier F'.field (P.iso x)) ∧
      (∀ y : FiniteCompletion E' P.v',
        ((φ y : F'.field) : AlgebraicClosure F.Carrier) =
          ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) ∧
      (∀ x : FiniteCompletion E Ps.v,
        φs (FiniteExtension.completionMap Ps.v Ps.v' x) =
          algebraMap F.Carrier F'.field (Ps.iso x)) ∧
      (∀ y : FiniteCompletion E' Ps.v',
        ((φs y : F'.field) : AlgebraicClosure F.Carrier) =
          ((Ps.isoTilde (FiniteExtension.completionMap Ps.v' Ps.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) := by
  -- The first place datum, from the given embeddings.
  obtain ⟨P, φ, hPv, -, hPp, hPu, hPc, hPi, hPis, hPt, hPts, hPθ, hφ, hφs, hφ₁, hφ₂⟩ :=
    exists_harrisPlaceDatum F F' jE jE' jL hE hE' hL hcE hcE' θ hθ
  -- The second place datum, from the embeddings twisted by `t`.
  have hEt : Algebra.adjoin ℚ_[p] (Set.range (jE.comp t.toRingHom)) = ⊤ := by
    rw [range_comp_ringEquiv]; exact hE
  obtain ⟨Ps, φs, hPsv, -, hPsp, hPsu, hPsc, hPsi, hPsis, hPst, hPsts, hPsθ, hφs', hφss',
      hφs₁, hφs₂⟩ :=
    exists_harrisPlaceDatum F F' (jE.comp t.toRingHom) (jE'.comp t'.toRingHom)
      (jL.comp tL.toRingHom) hEt (by rw [range_comp_ringEquiv]; exact hE')
      (by rw [range_comp_ringEquiv]; exact hL)
      (fun x => by
        change jL (tL (algebraMap E L x)) = algebraMap F.Carrier _ (jE (t x))
        rw [ht, hcE])
      (fun y => by
        change ((jL (tL (algebraMap E' L y)) : (galoisClosure F F').field) :
          AlgebraicClosure F.Carrier) = ((jE' (t' y) : F'.field) : AlgebraicClosure F.Carrier)
        rw [ht', hcE'])
      θ (fun σ x => by
        change θ σ (jL (tL x)) = jL (tL (σ x))
        rw [hθ, htσ])
  -- The conjugate places.
  set cE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hcEdef
  have hcEa : cE xa = -xa := hca
  have hcEd : cE xd = xd := hcd
  have hEc : Algebra.adjoin ℚ_[p] (Set.range (jE.comp cE.toRingHom)) = ⊤ := by
    rw [range_comp_ringEquiv]; exact hE
  have hEtc : Algebra.adjoin ℚ_[p] (Set.range ((jE.comp t.toRingHom).comp cE.toRingHom)) = ⊤ := by
    rw [range_comp_ringEquiv]; exact hEt
  have hcPv := mem_finitePlaceEquiv_iff cE jE (spectralNorm ℚ_[p] F.Carrier) hPv
  have hcPsv := mem_finitePlaceEquiv_iff cE (jE.comp t.toRingHom) (spectralNorm ℚ_[p] F.Carrier)
    hPsv
  have hconj (v : FinitePlace E) : conjPlace E v = finitePlaceEquiv cE v := rfl
  have hcL : ∀ x : E, cL (algebraMap E L x) = algebraMap E L (cE x) := hc
  -- The four places are pairwise distinct.
  have h12 : P.v ≠ conjPlace E P.v := by
    rw [hconj]
    exact ne_of_neg_place p jE (jE.comp cE.toRingHom) hE hEc hPv hcPv hxa0 hxa (by
      change jE (cE xa) = -jE xa
      rw [hcEa, map_neg])
  have h13 : P.v ≠ Ps.v :=
    ne_of_neg_place p jE (jE.comp t.toRingHom) hE hEt hPv hPsv hxd0 hxd (by
      change jE (t xd) = -jE xd
      rw [htd, map_neg])
  have h14 : P.v ≠ conjPlace E Ps.v := by
    rw [hconj]
    exact ne_of_neg_place p jE ((jE.comp t.toRingHom).comp cE.toRingHom) hE hEtc hPv hcPsv
      hxd0 hxd (by
        change jE (t (cE xd)) = -jE xd
        rw [hcEd, htd, map_neg])
  have h23 : conjPlace E P.v ≠ Ps.v := by
    rw [hconj]
    exact ne_of_neg_place p (jE.comp cE.toRingHom) (jE.comp t.toRingHom) hEc hEt hcPv hPsv
      (r := rd) hxd0 (by change jE (cE xd) = _; rw [hcEd]; exact hxd) (by
        change jE (t xd) = -jE (cE xd)
        rw [hcEd, htd, map_neg])
  have h24 : conjPlace E P.v ≠ conjPlace E Ps.v := by
    rw [hconj, hconj]
    exact ne_of_neg_place p (jE.comp cE.toRingHom) ((jE.comp t.toRingHom).comp cE.toRingHom)
      hEc hEtc hcPv hcPsv (r := rd) hxd0 (by change jE (cE xd) = _; rw [hcEd]; exact hxd) (by
        change jE (t (cE xd)) = -jE (cE xd)
        rw [hcEd, htd, map_neg])
  have h34 : Ps.v ≠ conjPlace E Ps.v := by
    rw [hconj]
    exact ne_of_neg_place p (jE.comp t.toRingHom) ((jE.comp t.toRingHom).comp cE.toRingHom)
      hEt hEtc hPsv hcPsv (r := ra) hxa0 (by change jE (t xa) = _; rw [hta]; exact hxa) (by
        change jE (t (cE xa)) = -jE (t xa)
        rw [hcEa, map_neg, map_neg])
  refine ⟨P, Ps, φ, φs, pairwise_ne_four h12 h13 h14 h23 h24 h34, ?_, ?_, hφ, hφs, hφs', hφss',
    hφ₁, hφ₂, hφs₁, hφs₂⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨hPp, hPu⟩
    · rw [hconj]
      exact ⟨(natCast_mem_finitePlaceEquiv cE _ p).mpr hPp,
        hasUniquePlaceAbove_finitePlaceEquiv cE cL hcL hPu⟩
    · exact ⟨hPsp, hPsu⟩
    · rw [hconj]
      exact ⟨(natCast_mem_finitePlaceEquiv cE _ p).mpr hPsp,
        hasUniquePlaceAbove_finitePlaceEquiv cE cL hcL hPsu⟩
  · intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact ⟨hPc, hPi, hPis, hPt, hPts, hPθ⟩
    · exact ⟨hPsc, hPsi, hPsis, hPst, hPsts, hPsθ⟩

end Langlands.Global.CMRealization
