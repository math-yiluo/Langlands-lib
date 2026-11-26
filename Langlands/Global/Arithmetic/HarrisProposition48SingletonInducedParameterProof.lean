import Langlands.Global.Arithmetic.HarrisProposition48SingletonDescentStatement
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTransport

/-! # Complex-place parameters in the singleton Mackey case -/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField NumberField.InfinitePlace.Completion
open Langlands.Automorphic.Unramified Langlands.LocalFactor.Archimedean AdelicFunctoriality
open scoped NumberField.LiesOver

section Places

variable {K D A M : Type*} [Field K] [Field D] [Field A] [Field M]

private theorem liesOver_of_comap_eq [Algebra K M] {v : InfinitePlace K} {u : InfinitePlace M}
    (h : u.comap (algebraMap K M) = v) : u.LiesOver v :=
  ⟨by ext x; exact InfinitePlace.comp_of_comap_eq h x⟩

private theorem exists_embedding_over [Algebra K M] [NumberField M] {v : InfinitePlace K}
    (u : InfinitePlacesAbove M v) :
    ∃ φ : M →+* ℂ, InfinitePlace.mk φ = u.1 ∧ φ.comp (algebraMap K M) = v.embedding := by
  rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq u.1 v with h | h
  · exact ⟨u.1.embedding, u.1.mk_embedding, h⟩
  · exact ⟨ComplexEmbedding.conjugate u.1.embedding,
      (InfinitePlace.mk_conjugate_eq _).trans u.1.mk_embedding, h⟩

private theorem embedding_eq_of_mk_eq_of_comp_eq (f : K →+* M) {φ ψ : M →+* ℂ}
    (hc : ¬ComplexEmbedding.IsReal (φ.comp f)) (hm : InfinitePlace.mk φ = InfinitePlace.mk ψ)
    (he : φ.comp f = ψ.comp f) : φ = ψ := by
  rcases InfinitePlace.mk_eq_iff.mp hm with h | h
  · exact h
  · exfalso
    apply hc (ComplexEmbedding.isReal_iff.mpr ?_)
    rw [← ComplexEmbedding.conjugate_comp, h, he]

variable [NumberField D] [NumberField A] [NumberField M]
variable [Algebra K D] [Algebra K A] [Algebra K M] [Algebra D M] [Algebra A M]
variable [IsScalarTower K D M] [IsScalarTower K A M]

/-- Restrict a place over `w` to the other intermediate field of the compositum. -/
private def restrictPlace (v : InfinitePlace K) (w : InfinitePlacesAbove D v)
    (u : InfinitePlacesAbove M w.1) : InfinitePlacesAbove A v :=
  ⟨u.1.comap (algebraMap A M), liesOver_of_comap_eq (by
    rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq K A M,
      IsScalarTower.algebraMap_eq K D M, InfinitePlace.comap_comp,
      InfinitePlace.LiesOver.comap_eq u.1 w.1, InfinitePlace.LiesOver.comap_eq w.1 v])⟩

end Places

set_option maxHeartbeats 600000 in
/-- A single double coset lets two embeddings with the same restriction to the base
extend to the compositum. For complex places, fixing the coordinate at the base gives
uniqueness of the orientation on both factors. -/
private theorem restrictPlace_bijective {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (D A : IntermediateField K L)
    (h : Nat.card (DoubleCoset.Quotient (D.fixingSubgroup : Set (L ≃ₐ[K] L))
      (A.fixingSubgroup : Set (L ≃ₐ[K] L))) = 1)
    (v : {v : InfinitePlace K // v.IsComplex}) (w : InfinitePlacesAbove D v.1) :
    letI : Algebra D (D ⊔ A : IntermediateField K L) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    letI : Algebra A (D ⊔ A : IntermediateField K L) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    letI : IsScalarTower K D (D ⊔ A : IntermediateField K L) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower K A (D ⊔ A : IntermediateField K L) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Function.Bijective (restrictPlace (M := (D ⊔ A : IntermediateField K L)) (A := A) v.1 w) := by
  let M : IntermediateField K L := D ⊔ A
  let : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  let : Algebra A M := (IntermediateField.inclusion (show A ≤ M from le_sup_right)).toAlgebra
  let : IsScalarTower K D M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K A M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Function.Bijective (restrictPlace (M := M) (A := A) v.1 w)
  constructor
  · intro u₁ u₂ hu
    obtain ⟨φ, hφ, hφD⟩ := exists_embedding_over u₁
    obtain ⟨ψ, hψ, hψD⟩ := exists_embedding_over u₂
    let base := w.1.embedding.comp (algebraMap K D)
    have comp_base (θ : M →+* ℂ) (hθ : θ.comp (algebraMap D M) = w.1.embedding) :
        θ.comp (algebraMap K M) = base := by
      rw [IsScalarTower.algebraMap_eq K D M, ← RingHom.comp_assoc, hθ]
    have hA : φ.comp (algebraMap A M) = ψ.comp (algebraMap A M) := by
      apply embedding_eq_of_mk_eq_of_comp_eq (algebraMap K A)
      · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K A M, comp_base φ hφD]
        apply InfinitePlace.not_isReal_of_mk_isComplex
        exact (InfinitePlace.LiesOver.mk_embedding_comp w.1 v.1).symm ▸ v.2
      · simp only [← InfinitePlace.comap_mk, hφ, hψ]
        exact congrArg Subtype.val hu
      · simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K A M,
          comp_base φ hφD, comp_base ψ hψD]
    let : Algebra K ℂ := base.toAlgebra
    let φ' : M →ₐ[K] ℂ := { φ with commutes' := RingHom.congr_fun (comp_base φ hφD) }
    let ψ' : M →ₐ[K] ℂ := { ψ with commutes' := RingHom.congr_fun (comp_base ψ hψD) }
    have he : φ' = ψ' := by
      apply IntermediateField.algHom_ext_of_eq_adjoin K (IntermediateField.sup_def D A)
      rintro x (hx | hx)
      · exact RingHom.congr_fun (hφD.trans hψD.symm) (⟨x, hx⟩ : D)
      · exact RingHom.congr_fun hA (⟨x, hx⟩ : A)
    exact Subtype.ext (hφ.symm.trans ((congrArg (fun f : M →ₐ[K] ℂ =>
      InfinitePlace.mk f.toRingHom) he).trans hψ))
  · intro z
    obtain ⟨φ, hφ, hφK⟩ := exists_embedding_over w
    obtain ⟨ψ, hψ, hψK⟩ := exists_embedding_over z
    let α := ComplexEmbedding.lift L φ
    let β := ComplexEmbedding.lift L ψ
    have hbase : α.comp (algebraMap K L) = β.comp (algebraMap K L) := by
      calc
        α.comp (algebraMap K L) = v.1.embedding := by
          rw [IsScalarTower.algebraMap_eq K D L, ← RingHom.comp_assoc,
            ComplexEmbedding.lift_comp_algebraMap, hφK]
        _ = β.comp (algebraMap K L) := by
          rw [IsScalarTower.algebraMap_eq K A L, ← RingHom.comp_assoc,
            ComplexEmbedding.lift_comp_algebraMap, hψK]
    obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq α β hbase
    let : Subsingleton (DoubleCoset.Quotient (D.fixingSubgroup : Set (L ≃ₐ[K] L))
        (A.fixingSubgroup : Set (L ≃ₐ[K] L))) := (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨p, hp, q, hq, hpq⟩ := DoubleCoset.eq.mp
      (Subsingleton.elim (DoubleCoset.mk D.fixingSubgroup A.fixingSubgroup 1)
        (DoubleCoset.mk D.fixingSubgroup A.fixingSubgroup g.symm))
    have hfactor : g.symm = p * q := by simpa only [mul_one] using hpq
    let γ := (α.comp p.toRingEquiv.toRingHom).comp (algebraMap M L)
    have hγD : γ.comp (algebraMap D M) = φ := by
      ext1 x
      change α (p (x : L)) = φ x
      rw [(IntermediateField.mem_fixingSubgroup_iff D p).mp hp _ x.2]
      exact ComplexEmbedding.lift_algebraMap_apply L φ x
    have hγA : γ.comp (algebraMap A M) = ψ := by
      ext1 x
      have hx := RingHom.congr_fun hg (x : L)
      change α (g.symm (x : L)) = β (x : L) at hx
      rw [hfactor] at hx
      change α (p (q (x : L))) = β (x : L) at hx
      rw [(IntermediateField.mem_fixingSubgroup_iff A q).mp hq _ x.2] at hx
      exact hx.trans (ComplexEmbedding.lift_algebraMap_apply L ψ x)
    refine ⟨⟨InfinitePlace.mk γ, liesOver_of_comap_eq ?_⟩, Subtype.ext ?_⟩
    · rw [InfinitePlace.comap_mk, hγD, hφ]
    · change (InfinitePlace.mk γ).comap (algebraMap A M) = z.1
      rw [InfinitePlace.comap_mk, hγA, hψ]

section Parameters

variable {K D M : Type*} [Field K] [Field D] [Field M]
variable [NumberField K] [NumberField D] [NumberField M]

variable [Algebra K M]

/-- Recover the parameter below a complex place by evaluating at the completion inclusion,
which is a right inverse to the local norm. -/
private theorem parameter_of_norm_pullback (μ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (u : InfinitePlacesAbove M v.1)
    (a : ComplexCharacterData)
    (h : HeckeCharacter.HasComplexPlaceParameter (μ.comp (ideleClassNorm (K := K) (L := M)))
      (complexPlaceAbove v u) a) : μ.HasComplexPlaceParameter v (normParameter v u a) := by
  classical
  intro x
  let y := Units.map (NumberField.LiesOver.completionMap v.1 u.1).toMonoidHom x
  have hy : InfiniteExtension.localUnitNorm v.1 u.1 y = x := by
    apply Units.ext
    change InfiniteExtension.localNorm v.1 u.1
      (NumberField.LiesOver.completionMap v.1 u.1 x.val) = x.val
    rw [InfiniteExtension.localNorm_algebraMap,
      (isUnramified_of_isComplex v.1 v.2 u).finrank_eq_one v.1, pow_one]
  have hx := h y
  change μ (ideleClassNorm (K := K) (QuotientGroup.mk (infiniteIdeleInclusion M u.1 y))) = _ at hx
  rw [ideleClassNorm_mk, ideleNorm_infiniteIdeleInclusion v.1 u y, hy] at hx
  change μ.infiniteComponent v.1 x = _ at hx
  rw [hx]
  unfold normParameter
  split_ifs with he
  · apply congrArg a.character
    apply Units.ext
    exact extensionEmbedding_completionMap_of_comp_eq v.1 u he x.val
  · change _ = a.character (complexConjugation _)
    apply congrArg a.character
    apply Units.ext
    exact extensionEmbedding_completionMap_of_comp_ne v.1 u he x.val

private theorem transport_eq_map (v : {v : InfinitePlace K // v.IsComplex})
    (u : InfinitePlacesAbove M v.1) (ds : List ComplexCharacterData) :
    complexPlaceParameterTransport v u ds = ds.map (normParameter v u) := by
  classical
  change _ = ds.map (fun a => normParameter v u a)
  by_cases h : u.1.embedding.comp (algebraMap K M) = v.1.embedding
  · simp [complexPlaceParameterTransport, normParameter, h]
  · simp [complexPlaceParameterTransport, normParameter, h]

omit [NumberField K] in
private theorem embedding_comp_eq_or_eq_conj {v : InfinitePlace K} (u : InfinitePlacesAbove M v) :
    u.1.embedding.comp (algebraMap K M) = v.embedding ∨
      u.1.embedding.comp (algebraMap K M) = ComplexEmbedding.conjugate v.embedding :=
  (InfinitePlace.mk_eq_iff.mp
    (v.mk_embedding.trans (InfinitePlace.LiesOver.mk_embedding_comp u.1 v).symm)).imp
      Eq.symm Eq.symm

/-- The two changes of selected coordinates read a block as direct restriction does. -/
private theorem normParameter_in_stages [Algebra K D] [Algebra D M] [IsScalarTower K D M]
    (v : {v : InfinitePlace K // v.IsComplex}) (w : InfinitePlacesAbove D v.1)
    (u : InfinitePlacesAbove M w.1) (t : InfinitePlacesAbove M v.1)
    (ht : t.1 = u.1) (a : ComplexCharacterData) :
    normParameter v w (normParameter (complexPlaceAbove v w) u a) = normParameter v t a := by
  classical
  have hv : ComplexEmbedding.conjugate v.1.embedding ≠ v.1.embedding :=
    fun h => (InfinitePlace.isComplex_iff.mp v.2) (ComplexEmbedding.isReal_iff.mpr h)
  have hw : ComplexEmbedding.conjugate w.1.embedding ≠ w.1.embedding :=
    fun h => (InfinitePlace.isComplex_iff.mp (complexPlaceAbove v w).2)
      (ComplexEmbedding.isReal_iff.mpr h)
  have hc : t.1.embedding.comp (algebraMap K M) =
      (u.1.embedding.comp (algebraMap D M)).comp (algebraMap K D) := by
    rw [ht, IsScalarTower.algebraMap_eq K D M, RingHom.comp_assoc]
  rcases embedding_comp_eq_or_eq_conj w with h₁ | h₁ <;>
    rcases embedding_comp_eq_or_eq_conj u with h₂ | h₂
  · simp only [normParameter, complexPlaceAbove, hc, h₁, h₂, ite_true]
  · have he : t.1.embedding.comp (algebraMap K M) = ComplexEmbedding.conjugate v.1.embedding := by
      rw [hc, h₂, ComplexEmbedding.conjugate_comp, h₁]
    simp only [normParameter, complexPlaceAbove, h₁, h₂, he, hw, hv, ite_true, ite_false]
  · simp only [normParameter, complexPlaceAbove, hc, h₁, h₂, hv, ite_true, ite_false]
  · have he : t.1.embedding.comp (algebraMap K M) = v.1.embedding := by
      rw [hc, h₂, ComplexEmbedding.conjugate_comp, h₁,
        ComplexEmbedding.involutive_conjugate K v.1.embedding]
    simp only [normParameter, complexPlaceAbove, h₁, h₂, he, hw, hv, ite_true, ite_false,
      ComplexCharacterDataLemmas.conj_conj]

end Parameters

set_option maxHeartbeats 800000 in
/-- In the singleton case, the Mackey parameter list over any complex place of `D`
reads as the list induced from the original Hecke character over the base place. -/
theorem proposition48SingletonInducedParameter :
    Proposition48SingletonInducedParameterStatement.{uF} := by
  classical
  intro Q D hL hcard
  let : IsNormalClosure Q.E Q.E' Q.L := hL
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  let : IsGalois Q.E Q.L := ⟨⟩
  let A := Q.conjugateField 1
  let M := Q.mackeyField D 1
  let : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  let : Algebra A M := (IntermediateField.inclusion (show A ≤ M from le_sup_right)).toAlgebra
  let : IsScalarTower Q.E D M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Q.E A M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : Q.E' ≃ₐ[Q.E] A := (Q.conjugateEmbedding 1).equivFieldRange
  let j : Q.E' →ₐ[Q.E] M :=
    (IntermediateField.inclusion (show A ≤ M from le_sup_right)).comp f.toAlgHom
  let : Algebra Q.E' M := j.toRingHom.toAlgebra
  let : IsScalarTower Q.E Q.E' M := IsScalarTower.of_algHom j
  intro v w ds d e a ha hperm
  have hχ : Q.mackeyCharacter D 1 = Q.ξ.comp (ideleClassNorm (K := Q.E') (L := M)) := by
    apply ContinuousMonoidHom.ext
    intro x
    change (HeckeCharacter.comap f.toRingEquiv.symm Q.ξ) (ideleClassNorm (K := A) x) = _
    have hx := ideleClassNorm_equiv f.toRingEquiv (RingEquiv.refl M) (fun _ => rfl) x
    rw [ideleClassEquiv_refl, ContinuousMulEquiv.refl_apply] at hx
    rw [hx]
    exact DFunLike.congr_fun (HeckeCharacter.comap_comap_symm f.toRingEquiv Q.ξ)
      (ideleClassNorm (K := Q.E') x)
  let φA : InfinitePlacesAbove M w.1 ≃ InfinitePlacesAbove A v.1 :=
    Equiv.ofBijective (restrictPlace v.1 w) (restrictPlace_bijective D A hcard v w)
  let φE : InfinitePlacesAbove A v.1 ≃ InfinitePlacesAbove Q.E' v.1 :=
    (infinitePlaceEquiv f.toRingEquiv).subtypeEquiv (fun z => by
      have hf : f.toRingEquiv.toRingHom.comp (algebraMap Q.E Q.E') = algebraMap Q.E A :=
        RingHom.ext f.commutes
      have iff_liesOver {T : Type} [Field T] [Algebra Q.E T] (p : InfinitePlace T) :
          p.LiesOver v.1 ↔ p.comap (algebraMap Q.E T) = v.1 :=
        ⟨fun h => let := h; InfinitePlace.LiesOver.comap_eq p v.1, liesOver_of_comap_eq⟩
      rw [iff_liesOver, iff_liesOver]
      change _ ↔ (z.comap f.toRingEquiv.toRingHom).comap (algebraMap Q.E Q.E') = v.1
      rw [← InfinitePlace.comap_comp, hf])
  let φ := φA.trans φE
  let overE' (u : InfinitePlacesAbove M w.1) : InfinitePlacesAbove M (φ u).1 :=
    ⟨u.1, liesOver_of_comap_eq rfl⟩
  let overE (u : InfinitePlacesAbove M w.1) : InfinitePlacesAbove M v.1 :=
    ⟨u.1, liesOver_of_comap_eq (by
      rw [IsScalarTower.algebraMap_eq Q.E D M, InfinitePlace.comap_comp,
        InfinitePlace.LiesOver.comap_eq u.1 w.1, InfinitePlace.LiesOver.comap_eq w.1 v.1])⟩
  let a' (u : InfinitePlacesAbove M w.1) :=
    normParameter (complexPlaceAbove v (φ u)) (overE' u) (a u)
  let dξ (z : InfinitePlacesAbove Q.E' v.1) := a' (φ.symm z)
  have hdξ (u : InfinitePlacesAbove M w.1) : dξ (φ u) = a' u :=
    congrArg a' (φ.symm_apply_apply u)
  refine ⟨d, e.trans φ, dξ, ?_, ?_⟩
  · intro z
    obtain ⟨u, rfl⟩ := φ.surjective z
    rw [hdξ u]
    have hu := ha u
    rw [hχ] at hu
    exact parameter_of_norm_pullback Q.ξ (complexPlaceAbove v (φ u)) (overE' u) (a u) hu
  · rw [transport_eq_map]
    refine (hperm.map (normParameter v w)).trans (List.Perm.of_eq ?_)
    simp only [complexPlaceLanglandsSum, transport_eq_map, List.map_flatten, List.map_ofFn,
      Function.comp_def, List.map_cons, List.map_nil]
    apply congrArg (fun blocks : Fin d → List ComplexCharacterData => (List.ofFn blocks).flatten)
    funext i
    apply congrArg (fun b : ComplexCharacterData => [b])
    change _ = normParameter v (φ (e i)) (dξ (φ (e i)))
    calc
      _ = normParameter v (overE (e i)) (a (e i)) :=
        normParameter_in_stages v w (e i) (overE (e i)) rfl (a (e i))
      _ = normParameter v (φ (e i)) (a' (e i)) :=
        (normParameter_in_stages v (φ (e i)) (overE' (e i)) (overE (e i)) rfl (a (e i))).symm
      _ = _ := congrArg (normParameter v (φ (e i))) (hdξ (e i)).symm

end Langlands.Global.Harris
