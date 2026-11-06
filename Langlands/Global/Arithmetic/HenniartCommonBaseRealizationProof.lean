import Langlands.Global.Arithmetic.HenniartHarrisDatumStatement
import Langlands.Global.Arithmetic.HarrisPairedPlaceRealizationProof

/-! # One CM base field for the paired-place configurations of all intermediate fields -/

noncomputable section

universe uF

namespace Langlands.Global.CMRealization

open NumberField IntermediateField FieldRealization
open Harris LocalFactor.CommonClosure GeneralPosition AdelicFunctoriality

section Embeddings

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
  {E E' L : Type*} [Field E] [Field E'] [Field L] [NumberField E] [NumberField E']
  [NumberField L] [IsCMField E] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsScalarTower E E' L] [IsGalois E L]

/-- `pairedPlaces_of_embeddings`, also recording that `P.v` is the place cut out by `jE` and
that `P.iso` restricts to `jE` on `E`. -/
theorem pairedPlaces_of_embeddings_spec (jE : E →+* F.Carrier) (jE' : E' →+* F'.field)
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
      (∀ a : 𝓞 E, a ∈ P.v.asIdeal ↔ spectralNorm ℚ_[p] F.Carrier (jE a) < 1) ∧
      (∀ x : E, P.iso (algebraMap E _ x) = jE x) ∧
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
  obtain ⟨P, φ, hPv, hPj, hPp, hPu, hPc, hPi, hPis, hPt, hPts, hPθ, hφ, hφs, hφ₁, hφ₂⟩ :=
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
  refine ⟨P, Ps, φ, φs, hPv, hPj, pairwise_ne_four h12 h13 h14 h23 h24 h34, ?_, ?_, hφ, hφs, hφs', hφss',
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

end Embeddings

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)

set_option maxHeartbeats 400000 in
/-- The paired-place configuration of `F' / F` over the model field `E` of `F`, for a CM rational
Galois model `N` of a finite Galois extension `Ω / ℚ_[p]` containing `F̃`. Unlike
`pairedPlaceRealization_of_model`, the `F`-algebra structure of `Ω` is given, so `E`, its
embedding into `F`, the place `P.v` and the restriction of `P.iso` to `E` do not depend on `F'`. -/
theorem pairedPlaceConfiguration_of_model (Ω : Type*) [Field Ω] [CharZero Ω] [Algebra ℚ_[p] Ω]
    [FiniteDimensional ℚ_[p] Ω] [IsGalois ℚ_[p] Ω] [Algebra F.Carrier Ω]
    [IsScalarTower ℚ_[p] F.Carrier Ω] [a₁ : Algebra ℚ_[p] F'.field]
    [a₂ : Algebra ℚ_[p] (galoisClosure F F').field] [t₁ : IsScalarTower ℚ_[p] F.Carrier F'.field]
    [t₂ : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F F').field]
    [aΩ : Algebra (galoisClosure F F').field Ω]
    [tΩ : IsScalarTower F.Carrier (galoisClosure F F').field Ω]
    (N : Type) [Field N] [NumberField N] [IsGalois ℚ N] [IsCMField N] [Algebra N Ω]
    (hι : IntermediateField.adjoin ℚ_[p] (Set.range (algebraMap N Ω)) = ⊤)
    {a d : ℚ} (ha : a < 0) (hd : 0 < d) (haq : IsSquare (algebraMap ℚ ℚ_[p] a))
    {xa xd : N} (hxa : xa ^ 2 = algebraMap ℚ N a) (hxd : xd ^ 2 = algebraMap ℚ N d)
    (hra : ∃ r : ℚ_[p], algebraMap N Ω xa = algebraMap ℚ_[p] Ω r)
    (hrd : ∃ r : ℚ_[p], algebraMap N Ω xd = algebraMap ℚ_[p] Ω r)
    (s : N ≃ₐ[ℚ] N) (hs : ∀ (σ : N ≃ₐ[ℚ] N) (x : N), σ (s x) = s (σ x))
    (hsa : s xa = xa) (hsd : s xd = -xd) [IsCMField (modelField p Ω N F.Carrier)] :
    ∃ (E' L : Type) (_ : Field E') (_ : Field L) (_ : NumberField E') (_ : NumberField L)
      (_ : IsCMField E') (_ : IsCMField L)
      (_ : Algebra (modelField p Ω N F.Carrier) E') (_ : Algebra (modelField p Ω N F.Carrier) L)
      (_ : Algebra E' L)
      (K₀ : IntermediateField ℚ (modelField p Ω N F.Carrier))
      (P Ps : PlaceDatum F F' (modelField p Ω N F.Carrier) E' L)
      (φ : FiniteCompletion E' P.v' ≃+* F'.field)
      (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
      (θ : (L ≃ₐ[modelField p Ω N F.Carrier] L) ≃*
        ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
      IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧
      (∀ b : 𝓞 (modelField p Ω N F.Carrier),
        b ∈ P.v.asIdeal ↔ spectralNorm ℚ_[p] F.Carrier (baseEmbedding p Ω N F.Carrier b) < 1) ∧
      ∀ x : modelField p Ω N F.Carrier,
        P.iso (algebraMap _ (FiniteCompletion _ P.v) x) = baseEmbedding p Ω N F.Carrier x := by
  -- The tower `F ⊆ F' ⊆ F̃ ⊆ Ω`.
  let : Algebra F'.field (galoisClosure F F').field :=
    (IntermediateField.inclusion (le_galoisClosure F F')).toAlgebra
  let : Algebra F'.field Ω :=
    ((algebraMap (galoisClosure F F').field Ω).comp
      (algebraMap F'.field (galoisClosure F F').field)).toAlgebra
  have : IsScalarTower F.Carrier F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F'.field (galoisClosure F F').field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F.Carrier F'.field Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply F.Carrier (galoisClosure F F').field Ω]
      rfl
  have : IsScalarTower ℚ_[p] F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier F'.field,
        IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F F').field]
      rfl
  have : IsScalarTower ℚ_[p] (galoisClosure F F').field Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F F').field,
        ← IsScalarTower.algebraMap_apply F.Carrier (galoisClosure F F').field Ω,
        ← IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier Ω]
  have : IsScalarTower ℚ_[p] F'.field Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (galoisClosure F F').field Ω,
        IsScalarTower.algebraMap_apply ℚ_[p] F'.field (galoisClosure F F').field]
      rfl
  let : Module ℚ_[p] F'.field := Algebra.toModule
  let : Module ℚ_[p] (galoisClosure F F').field := Algebra.toModule
  have : FiniteDimensional ℚ_[p] F'.field := FiniteDimensional.trans ℚ_[p] F.Carrier F'.field
  have : FiniteDimensional ℚ_[p] (galoisClosure F F').field :=
    FiniteDimensional.trans ℚ_[p] F.Carrier (galoisClosure F F').field
  have := Algebra.charZero_of_charZero ℚ_[p] F.Carrier
  have : IsGalois F.Carrier (galoisClosure F F').field :=
    inferInstanceAs (IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier)))
  -- The model tower `E ⊆ E' ⊆ L` inside `N`.
  have hle : topModel p Ω N F.Carrier F'.field ≤
      topModel p Ω N F.Carrier (galoisClosure F F').field := fun y hy =>
    modelField_le p Ω N F'.field (galoisClosure F F').field hy
  let : Algebra (topModel p Ω N F.Carrier F'.field)
      (topModel p Ω N F.Carrier (galoisClosure F F').field) :=
    (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower (modelField p Ω N F.Carrier) (topModel p Ω N F.Carrier F'.field)
      (topModel p Ω N F.Carrier (galoisClosure F F').field) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isGalois_topModel p Ω N F.Carrier (galoisClosure F F').field hι
  -- CM structures and the imaginary quadratic field.
  have hxaE : xa ∈ modelField p Ω N F.Carrier := mem_modelField_of_padic p Ω N F.Carrier hra
  have hxdE : xd ∈ modelField p Ω N F.Carrier := mem_modelField_of_padic p Ω N F.Carrier hrd
  have hxa0 : xa ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hxa
    exact ha.ne hxa
  have hxd0 : xd ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hxd
    exact hd.ne' hxd
  obtain ⟨-, hCM', hCML, hK₀, hsup, hsup', hsupL⟩ :=
    cmQuadratic (M := N) p (E := modelField p Ω N F.Carrier)
      (E' := topModel p Ω N F.Carrier F'.field)
      (L := topModel p Ω N F.Carrier (galoisClosure F F').field)
      (modelField_central p Ω N F.Carrier (conjQ N) conjQ_central)
      (topModel_central p Ω N F.Carrier F'.field (conjQ N) conjQ_central)
      (topModel_central p Ω N F.Carrier (galoisClosure F F').field (conjQ N) conjQ_central)
      ha haq (x := ⟨xa, hxaE⟩) ((algebraMap (modelField p Ω N F.Carrier) N).injective (by
        rw [map_pow, ← IsScalarTower.algebraMap_apply]
        exact hxa))
  -- The embeddings into the local fields.
  set jE := baseEmbedding p Ω N F.Carrier with hjE
  set jE' := topEmbedding p Ω N F.Carrier F'.field with hjE'
  set jL := topEmbedding p Ω N F.Carrier (galoisClosure F F').field with hjL
  have hE := adjoin_range_baseEmbedding p Ω N F.Carrier hι
  have hE' : Algebra.adjoin F.Carrier (Set.range jE') = ⊤ :=
    adjoin_eq_top_of_restrictScalars (R := ℚ_[p])
      (adjoin_range_topEmbedding p Ω N F.Carrier F'.field hι)
  have hL : Algebra.adjoin F.Carrier (Set.range jL) = ⊤ :=
    adjoin_eq_top_of_restrictScalars (R := ℚ_[p])
      (adjoin_range_topEmbedding p Ω N F.Carrier (galoisClosure F F').field hι)
  have hcE : ∀ x : modelField p Ω N F.Carrier,
      jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap F.Carrier (galoisClosure F F').field (jE x) :=
    topEmbedding_algebraMap p Ω N F.Carrier (galoisClosure F F').field
  have hcE' : ∀ y : topModel p Ω N F.Carrier F'.field,
      ((jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) :
        (galoisClosure F F').field) : AlgebraicClosure F.Carrier) =
        ((jE' y : F'.field) : AlgebraicClosure F.Carrier) := by
    intro y
    have h : jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) =
        algebraMap F'.field (galoisClosure F F').field (jE' y) := by
      apply (algebraMap (galoisClosure F F').field Ω).injective
      rw [hjL, algebraMap_topEmbedding]
      exact (algebraMap_topEmbedding p Ω N F.Carrier F'.field y).symm
    rw [h]
    rfl
  obtain ⟨θ, hθ⟩ := exists_galoisEquiv p Ω N F.Carrier (galoisClosure F F').field hι
  -- The twisting automorphisms, restricted from `s`.
  obtain ⟨t, ht⟩ := exists_restrict s (modelField_central p Ω N F.Carrier s hs)
  obtain ⟨t', ht'⟩ := exists_restrict s (topModel_central p Ω N F.Carrier F'.field s hs)
  obtain ⟨tL, htL⟩ :=
    exists_restrict s (topModel_central p Ω N F.Carrier (galoisClosure F F').field s hs)
  have injL := (algebraMap (topModel p Ω N F.Carrier (galoisClosure F F').field) N).injective
  have injE := (algebraMap (modelField p Ω N F.Carrier) N).injective
  have hsE : ∀ x : modelField p Ω N F.Carrier,
      tL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) (t x) :=
    fun x => injL (by rw [htL]; exact (ht x).symm)
  have hsE' : ∀ y : topModel p Ω N F.Carrier F'.field,
      tL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) (t' y) :=
    fun y => injL (by rw [htL]; exact (ht' y).symm)
  have hsσ : ∀ (σ : topModel p Ω N F.Carrier (galoisClosure F F').field ≃ₐ[modelField p Ω N F.Carrier]
      topModel p Ω N F.Carrier (galoisClosure F F').field) (x), σ (tL x) = tL (σ x) := by
    intro σ x
    apply injL
    rw [← AlgEquiv.liftNormal_commutes σ N, htL, htL, ← AlgEquiv.liftNormal_commutes σ N]
    exact hs ((σ.liftNormal N).restrictScalars ℚ) _
  -- Complex conjugation on `L`.
  have hc : ∀ x : modelField p Ω N F.Carrier,
      (IsCMField.complexConj (topModel p Ω N F.Carrier (galoisClosure F F').field)).toRingEquiv
        (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field)
          (IsCMField.complexConj (modelField p Ω N F.Carrier) x) := by
    intro x
    apply injL
    change algebraMap _ N (IsCMField.complexConj _ _) = _
    rw [algebraMap_complexConj]
    exact (algebraMap_complexConj (M := N) x).symm
  -- The two separating elements.
  obtain ⟨ra, hra'⟩ := hra
  obtain ⟨rd, hrd'⟩ := hrd
  have hjxa : jE ⟨xa, hxaE⟩ = algebraMap ℚ_[p] F.Carrier ra := by
    apply (algebraMap F.Carrier Ω).injective
    rw [hjE, algebraMap_baseEmbedding, ← IsScalarTower.algebraMap_apply]
    exact hra'
  have hjxd : jE ⟨xd, hxdE⟩ = algebraMap ℚ_[p] F.Carrier rd := by
    apply (algebraMap F.Carrier Ω).injective
    rw [hjE, algebraMap_baseEmbedding, ← IsScalarTower.algebraMap_apply]
    exact hrd'
  have hca : IsCMField.complexConj (modelField p Ω N F.Carrier) ⟨xa, hxaE⟩ = -⟨xa, hxaE⟩ := by
    apply injE
    rw [algebraMap_complexConj (M := N), map_neg]
    exact conjQ_of_sq_neg ha hxa
  have hcd : IsCMField.complexConj (modelField p Ω N F.Carrier) ⟨xd, hxdE⟩ = ⟨xd, hxdE⟩ := by
    apply injE
    rw [algebraMap_complexConj (M := N)]
    exact (conjQ_eq_self_iff xd).mpr (mem_maximalRealSubfield_of_sq_pos hd hxd)
  have hta : t ⟨xa, hxaE⟩ = ⟨xa, hxaE⟩ := injE (by rw [ht]; exact hsa)
  have htd : t ⟨xd, hxdE⟩ = -⟨xd, hxdE⟩ := injE (by rw [ht, map_neg]; exact hsd)
  -- Degrees and the four places.
  obtain ⟨hdeg, hdegL, hNC⟩ := harrisDegrees F F' jE' jL hE' hcE' θ hθ
  obtain ⟨P, Ps, φ, φs, hPv, hPj, hrest⟩ :=
    pairedPlaces_of_embeddings_spec F F' jE jE' jL hE hE' hL hcE hcE' θ hθ t t' tL hsE hsE' hsσ
      (IsCMField.complexConj (topModel p Ω N F.Carrier (galoisClosure F F').field)).toRingEquiv
      hc hjxa hjxd (fun h => hxa0 (congrArg Subtype.val h))
      (fun h => hxd0 (congrArg Subtype.val h)) hca hcd hta htd
  have hconf : IsPairedPlaceConfiguration
      ℚ⟮(⟨xa, hxaE⟩ : modelField p Ω N F.Carrier)⟯ P Ps φ φs θ := by
    unfold IsPairedPlaceConfiguration
    exact ⟨inferInstance, hNC, hK₀, hsup, hsup', hsupL, hdeg, hdegL, hrest⟩
  exact ⟨topModel p Ω N F.Carrier F'.field,
    topModel p Ω N F.Carrier (galoisClosure F F').field, inferInstance, inferInstance,
    inferInstance, inferInstance, hCM', hCML, inferInstance, inferInstance, inferInstance,
    _, P, Ps, φ, φs, θ, hconf, hPv, hPj⟩

/-- `pairedPlaceConfiguration_of_model` for every intermediate field `F'` of `M / F`, once a
finite Galois extension `Ω / ℚ_[p]` contains the normal closure `M̃` of `M / F`. The field `E`,
its embedding and the `F`-algebra structure of `Ω` are fixed in advance. -/
theorem pairedPlaceConfiguration_of_le (M : Extension F) (Ω : Type*) [Field Ω] [CharZero Ω]
    [Algebra ℚ_[p] Ω] [FiniteDimensional ℚ_[p] Ω] [IsGalois ℚ_[p] Ω] [Algebra F.Carrier Ω]
    [IsScalarTower ℚ_[p] F.Carrier Ω] [aM : Algebra (galoisClosure F M).field Ω]
    [tM : IsScalarTower F.Carrier (galoisClosure F M).field Ω]
    (N : Type) [Field N] [NumberField N] [IsGalois ℚ N] [IsCMField N] [Algebra N Ω]
    (hι : IntermediateField.adjoin ℚ_[p] (Set.range (algebraMap N Ω)) = ⊤)
    {a d : ℚ} (ha : a < 0) (hd : 0 < d) (haq : IsSquare (algebraMap ℚ ℚ_[p] a))
    {xa xd : N} (hxa : xa ^ 2 = algebraMap ℚ N a) (hxd : xd ^ 2 = algebraMap ℚ N d)
    (hra : ∃ r : ℚ_[p], algebraMap N Ω xa = algebraMap ℚ_[p] Ω r)
    (hrd : ∃ r : ℚ_[p], algebraMap N Ω xd = algebraMap ℚ_[p] Ω r)
    (s : N ≃ₐ[ℚ] N) (hs : ∀ (σ : N ≃ₐ[ℚ] N) (x : N), σ (s x) = s (σ x))
    (hsa : s xa = xa) (hsd : s xd = -xd) [IsCMField (modelField p Ω N F.Carrier)]
    (F' : Extension F) (hF' : F'.field ≤ M.field) :
    ∃ (E' L : Type) (_ : Field E') (_ : Field L) (_ : NumberField E') (_ : NumberField L)
      (_ : IsCMField E') (_ : IsCMField L)
      (_ : Algebra (modelField p Ω N F.Carrier) E') (_ : Algebra (modelField p Ω N F.Carrier) L)
      (_ : Algebra E' L)
      (K₀ : IntermediateField ℚ (modelField p Ω N F.Carrier))
      (P Ps : PlaceDatum F F' (modelField p Ω N F.Carrier) E' L)
      (φ : FiniteCompletion E' P.v' ≃+* F'.field)
      (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
      (θ : (L ≃ₐ[modelField p Ω N F.Carrier] L) ≃*
        ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
      IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧
      (∀ b : 𝓞 (modelField p Ω N F.Carrier),
        b ∈ P.v.asIdeal ↔ spectralNorm ℚ_[p] F.Carrier (baseEmbedding p Ω N F.Carrier b) < 1) ∧
      ∀ x : modelField p Ω N F.Carrier,
        P.iso (algebraMap _ (FiniteCompletion _ P.v) x) = baseEmbedding p Ω N F.Carrier x := by
  let _ : Algebra ℚ_[p] F'.field := (F'.asPadicField (p := p)).algebra
  let _ : Algebra ℚ_[p] (galoisClosure F F').field :=
    ((galoisClosure F F').asPadicField (p := p)).algebra
  have : IsScalarTower ℚ_[p] F.Carrier F'.field := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hle : (galoisClosure F F').field ≤ (galoisClosure F M).field :=
    IntermediateField.normalClosure_mono F'.field M.field hF'
  let _ : Algebra (galoisClosure F F').field Ω :=
    ((algebraMap (galoisClosure F M).field Ω).comp
      (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have : IsScalarTower F.Carrier (galoisClosure F F').field Ω :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply F.Carrier (galoisClosure F M).field Ω]
      rfl
  exact pairedPlaceConfiguration_of_model F F' Ω N hι ha hd haq hxa hxd hra hrd s hs hsa hsd

end Langlands.Global.CMRealization

namespace Langlands.Global

open NumberField CMRealization FieldRealization LocalFactor.CommonClosure GeneralPosition Harris

/-- Henniart's common base: one CM model field `E` of `F`, with the place `v₀` and the
completion isomorphism `ι₀` cut out by its embedding into `F`, carries a paired-place
configuration of every intermediate field of `M / F`. -/
theorem henniartCommonBaseRealization : HenniartCommonBaseRealizationStatement.{uF} := by
  intro p hp F M
  let _ := F.canonicalTopology
  -- A finite Galois extension `Ω / ℚ_[p]` containing `M̃`.
  obtain ⟨Ω, _, _, _, _, _, aΩ, tΩ⟩ :=
    exists_galois_extension ((galoisClosure F M).asPadicField (p := p))
  let _ : Algebra ℚ_[p] (galoisClosure F M).field :=
    ((galoisClosure F M).asPadicField (p := p)).algebra
  have : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F M).field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra F.Carrier Ω :=
    ((algebraMap (galoisClosure F M).field Ω).comp
      (algebraMap F.Carrier (galoisClosure F M).field)).toAlgebra
  have : IsScalarTower F.Carrier (galoisClosure F M).field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F.Carrier Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (galoisClosure F M).field Ω,
        IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F M).field]
      rfl
  -- The CM rational Galois model of `Ω` and the CM base field `E`.
  let _ : Algebra (cmModel p Ω) Ω := (cmModelEmbedding p Ω).toRingHom.toAlgebra
  have hxaE : sqrtNeg p Ω ∈ modelField p Ω (cmModel p Ω) F.Carrier :=
    mem_modelField_of_padic p Ω (cmModel p Ω) F.Carrier (cmModelEmbedding_sqrtNeg p Ω)
  have : IsCMField (modelField p Ω (cmModel p Ω) F.Carrier) :=
    isCMField_of_sq_neg (M := cmModel p Ω)
      (modelField_central p Ω (cmModel p Ω) F.Carrier (conjQ (cmModel p Ω)) conjQ_central)
      (negSq_neg p) (x := ⟨sqrtNeg p Ω, hxaE⟩)
      ((algebraMap (modelField p Ω (cmModel p Ω) F.Carrier) (cmModel p Ω)).injective (by
        rw [map_pow, ← IsScalarTower.algebraMap_apply]
        exact sqrtNeg_sq p Ω))
  have key := pairedPlaceConfiguration_of_le F M Ω (cmModel p Ω) (cmModelEmbedding_adjoin p Ω)
    (negSq_neg p) (posSq_pos p Ω) (negSq_isSquare p) (sqrtNeg_sq p Ω) (sqrtPos_sq p Ω)
    (cmModelEmbedding_sqrtNeg p Ω) (cmModelEmbedding_sqrtPos p Ω) (flipPos p Ω)
    (flipPos_central p Ω) (flipPos_sqrtNeg p Ω) (flipPos_sqrtPos p Ω)
  -- The common place and completion isomorphism, read off at `F' = M`.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, P₀, _, _, _, _, hconf₀, hv₀, hj₀⟩ :=
    key M le_rfl
  have hiso₀ : Continuous P₀.iso ∧ Continuous P₀.iso.symm := by
    unfold IsPairedPlaceConfiguration at hconf₀
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, -⟩ := hconf₀
    exact ⟨(hQ P₀ (by simp)).2.1, (hQ P₀ (by simp)).2.2.1⟩
  refine ⟨modelField p Ω (cmModel p Ω) F.Carrier, inferInstance, inferInstance, inferInstance,
    P₀.v, P₀.iso, hiso₀.1, hiso₀.2, fun F' hF' => ?_⟩
  obtain ⟨E', L, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉, K₀, P, Ps, φ, φs, θ, hconf, hv, hj⟩ :=
    key F' hF'
  refine ⟨E', L, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉, K₀, P, Ps, φ, φs, θ, hconf, ?_, ?_⟩
  · exact IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun b => (hv b).trans (hv₀ b).symm)
  · intro x
    rw [hj, hj₀]

end Langlands.Global
