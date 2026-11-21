import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48IdentityMackey
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm
import Mathlib.Data.List.FinRange

/-! # Complex-place induction in stages for the identity Mackey constituent -/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField NumberField.InfinitePlace.Completion AdelicFunctoriality
open Langlands.Automorphic.Unramified Langlands.LocalFactor.Archimedean
open scoped NumberField.LiesOver

section Coordinates

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Read one block in the selected coordinate of the restricted place. -/
private def readBlock (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (a : ComplexCharacterData) : ComplexCharacterData :=
  open Classical in
  if w.embedding.comp f = v.embedding then a else a.conj

private theorem embedding_over (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (h : w.comap f = v) :
    w.embedding.comp f = v.embedding ∨ w.embedding.comp f = ComplexEmbedding.conjugate v.embedding := by
  have hm : InfinitePlace.mk v.embedding = InfinitePlace.mk (w.embedding.comp f) := by
    simp only [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, h]
  exact (InfinitePlace.mk_eq_iff.mp hm).imp Eq.symm Eq.symm

private theorem conjugate_embedding_ne {v : InfinitePlace K} (hv : v.IsComplex) :
    ComplexEmbedding.conjugate v.embedding ≠ v.embedding :=
  fun h => (InfinitePlace.isComplex_iff.mp hv) (ComplexEmbedding.isReal_iff.mpr h)

private theorem readBlock_comp (f : K →+* L) (g : L →+* M)
    (v : InfinitePlace K) (w : InfinitePlace L) (u : InfinitePlace M)
    (hv : v.IsComplex) (hw : w.IsComplex) (hf : w.comap f = v) (hg : u.comap g = w)
    (a : ComplexCharacterData) :
    readBlock f v w (readBlock g w u a) = readBlock (g.comp f) v u a := by
  classical
  rcases embedding_over f v w hf with h₁ | h₁ <;> rcases embedding_over g w u hg with h₂ | h₂
  · have h : u.embedding.comp (g.comp f) = v.embedding := by
      rw [← RingHom.comp_assoc, h₂, h₁]
    simp only [readBlock, h₁, h₂, h, ite_true]
  · have h : u.embedding.comp (g.comp f) = ComplexEmbedding.conjugate v.embedding := by
      rw [← RingHom.comp_assoc, h₂, ComplexEmbedding.conjugate_comp, h₁]
    simp only [readBlock, h₁, ite_true, (h₂.trans_ne (conjugate_embedding_ne hw)),
      (h.trans_ne (conjugate_embedding_ne hv)), ite_false]
  · have h : u.embedding.comp (g.comp f) = ComplexEmbedding.conjugate v.embedding := by
      rw [← RingHom.comp_assoc, h₂, h₁]
    simp only [readBlock, h₂, ite_true, (h₁.trans_ne (conjugate_embedding_ne hv)),
      (h.trans_ne (conjugate_embedding_ne hv)), ite_false]
  · have h : u.embedding.comp (g.comp f) = v.embedding := by
      rw [← RingHom.comp_assoc, h₂, ComplexEmbedding.conjugate_comp, h₁,
        ComplexEmbedding.involutive_conjugate K v.embedding]
    simp only [readBlock, (h₁.trans_ne (conjugate_embedding_ne hv)),
      (h₂.trans_ne (conjugate_embedding_ne hw)), ite_false, h, ite_true,
      ComplexCharacterDataLemmas.conj_conj]

/-- A coordinate identity on field elements extends to the completions. -/
private theorem extensionEmbedding_map_eq (f : K →+* L) (w : InfinitePlace L)
    (c : (w.comap f).Completion →+* ℂ) (hc : Continuous c)
    (h : ∀ a : K, w.embedding (f a) = c (algebraMap K (w.comap f).Completion a))
    (x : (w.comap f).Completion) :
    extensionEmbedding w (infiniteCompletionMap f w x) = c x := by
  have heq : (fun y : (w.comap f).Completion =>
      extensionEmbedding w (infiniteCompletionMap f w y)) = c := by
    apply (denseRange_coe (w.comap f)).equalizer
      ((isometry_extensionEmbedding w).continuous.comp (continuous_infiniteCompletionMap f w)) hc
    funext z
    let a := WithAbs.equiv (w.comap f).1 z
    change extensionEmbedding w (infiniteCompletionMap f w
      (algebraMap K (w.comap f).Completion a)) = c (algebraMap K (w.comap f).Completion a)
    rw [infiniteCompletionMap_coe]
    exact (extensionEmbedding_coe w (WithAbs.toAbs w.1 (f a))).trans (h a)
  exact congrFun heq x

variable [NumberField K] [NumberField L]

private theorem hasComplexPlaceParameter_comap (e : K ≃+* L) (χ : HeckeCharacter L)
    (v : {v : InfinitePlace K // v.IsComplex}) (w : {w : InfinitePlace L // w.IsComplex})
    (hw : w.1.comap e.toRingHom = v.1) (a : ComplexCharacterData)
    (ha : χ.HasComplexPlaceParameter w a) :
    (HeckeCharacter.comap e χ).HasComplexPlaceParameter v
      (readBlock e.toRingHom v.1 w.1 a) := by
  classical
  rcases v with ⟨v, hv⟩
  change w.1.comap e.toRingHom = v at hw
  subst v
  let v := w.1.comap e.toRingHom
  intro x
  let y := Units.mapEquiv (infiniteCompletionEquiv e w.1).toMulEquiv x
  refine (HeckeCharacter.comap_infiniteComponent e χ w.1 x).trans ((ha y).trans ?_)
  by_cases he : w.1.embedding.comp e.toRingHom = v.embedding
  · have hread : readBlock e.toRingHom v w.1 a = a := ite_eq_left he
    change a.character _ = (readBlock e.toRingHom v w.1 a).character _
    rw [hread]
    apply congrArg a.character
    apply Units.ext
    change extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 x.val) =
      extensionEmbedding v x.val
    apply extensionEmbedding_map_eq e.toRingHom w.1 (extensionEmbedding v)
      (isometry_extensionEmbedding v).continuous
    intro y
    exact (RingHom.congr_fun he y).trans (extensionEmbedding_coe v (WithAbs.toAbs v.1 y)).symm
  · have hconj := (embedding_over e.toRingHom v w.1 rfl).resolve_left he
    have hread : readBlock e.toRingHom v w.1 a = a.conj := ite_eq_right he
    change a.character _ = (readBlock e.toRingHom v w.1 a).character _
    rw [hread]
    change a.character _ = a.character (complexConjugation _)
    apply congrArg a.character
    apply Units.ext
    change extensionEmbedding w.1 (infiniteCompletionMap e.toRingHom w.1 x.val) =
      star (extensionEmbedding v x.val)
    apply extensionEmbedding_map_eq e.toRingHom w.1 (ComplexEmbedding.conjugate (extensionEmbedding v))
      (continuous_star.comp (isometry_extensionEmbedding v).continuous)
    intro y
    exact (RingHom.congr_fun hconj y).trans
      (congrArg star (extensionEmbedding_coe v (WithAbs.toAbs v.1 y))).symm

end Coordinates

section Places

variable {K L M : Type*} [Field K] [Field L] [Field M]

private theorem liesOver_of_comap_eq [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap K L) = v) : w.LiesOver v :=
  ⟨by ext x; exact InfinitePlace.comp_of_comap_eq h x⟩

private theorem liesOver_iff_comap_eq [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L) :
    w.LiesOver v ↔ w.comap (algebraMap K L) = v :=
  ⟨fun h => let : w.LiesOver v := h; InfinitePlace.LiesOver.comap_eq w v, liesOver_of_comap_eq⟩

variable [NumberField L] [NumberField M]

/-- The infinite places in a tower, indexed either in stages or directly. -/
private def infinitePlacesTower [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (v : InfinitePlace K) :
    (Σ w : InfinitePlacesAbove L v, InfinitePlacesAbove M w.1) ≃ InfinitePlacesAbove M v := by
  let proj (p : Σ w : InfinitePlacesAbove L v, InfinitePlacesAbove M w.1) : InfinitePlacesAbove M v :=
    ⟨p.2.1, liesOver_of_comap_eq (by
      rw [IsScalarTower.algebraMap_eq K L M, InfinitePlace.comap_comp,
        InfinitePlace.LiesOver.comap_eq p.2.1 p.1.1, InfinitePlace.LiesOver.comap_eq p.1.1 v])⟩
  refine Equiv.ofBijective proj ⟨?_, ?_⟩
  · intro p q h
    have hu : p.2.1 = q.2.1 := congrArg Subtype.val h
    have hw : p.1 = q.1 := by
      apply Subtype.ext
      rw [← InfinitePlace.LiesOver.comap_eq p.2.1 p.1.1,
        ← InfinitePlace.LiesOver.comap_eq q.2.1 q.1.1, hu]
    rcases p with ⟨w, u⟩
    rcases q with ⟨w', u'⟩
    change w = w' at hw
    subst w'
    exact congrArg (Sigma.mk w) (Subtype.ext hu)
  · intro u
    let w : InfinitePlacesAbove L v := ⟨u.1.comap (algebraMap L M), liesOver_of_comap_eq (by
      rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq K L M]
      exact InfinitePlace.LiesOver.comap_eq u.1 v)⟩
    exact ⟨⟨w, ⟨u.1, liesOver_of_comap_eq rfl⟩⟩, Subtype.ext rfl⟩

private theorem infinitePlacesTower_val [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (v : InfinitePlace K) (p : Σ w : InfinitePlacesAbove L v, InfinitePlacesAbove M w.1) :
    (infinitePlacesTower v p).1 = p.2.1 := rfl

/-- Pullback along a base-linear isomorphism preserves the fibre over the base place. -/
private def infinitePlacesComap [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M)
    (v : InfinitePlace K) : InfinitePlacesAbove M v ≃ InfinitePlacesAbove L v :=
  (infinitePlaceEquiv e.toRingEquiv).subtypeEquiv fun u => by
    rw [liesOver_iff_comap_eq, liesOver_iff_comap_eq]
    change _ ↔ (u.comap e.toRingEquiv.toRingHom).comap (algebraMap K L) = v
    have he : e.toRingEquiv.toRingHom.comp (algebraMap K L) = algebraMap K M :=
      RingHom.ext e.commutes
    rw [← InfinitePlace.comap_comp, he]

private theorem infinitePlacesComap_val [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M)
    (v : InfinitePlace K) (u : InfinitePlacesAbove M v) :
    (infinitePlacesComap e v u).1 = u.1.comap e.toRingEquiv.toRingHom := rfl

end Places

section Lists

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private theorem transport_eq_map (v : {v : InfinitePlace K // v.IsComplex})
    (w : InfinitePlacesAbove L v.1) (ds : List ComplexCharacterData) :
    complexPlaceParameterTransport v w ds = ds.map (readBlock (algebraMap K L) v.1 w.1) := by
  classical
  change _ = ds.map (fun a => readBlock (algebraMap K L) v.1 w.1 a)
  by_cases h : w.1.embedding.comp (algebraMap K L) = v.1.embedding
  · simp [complexPlaceParameterTransport, readBlock, h]
  · simp only [complexPlaceParameterTransport, readBlock, h, ite_false]

private theorem langlandsSum_singletons (v : {v : InfinitePlace K // v.IsComplex}) {n : ℕ}
    (en : Fin n ≃ InfinitePlacesAbove L v.1) (a : InfinitePlacesAbove L v.1 → ComplexCharacterData) :
    complexPlaceLanglandsSum v en (fun w => [a w]) =
      List.ofFn (fun i => readBlock (algebraMap K L) v.1 (en i).1 (a (en i))) := by
  simp only [complexPlaceLanglandsSum, transport_eq_map, List.map_cons, List.map_nil]
  let l := List.ofFn (fun i => readBlock (algebraMap K L) v.1 (en i).1 (a (en i)))
  have h : l.flatMap (fun x => [x]) = l := by simp
  simpa only [l, List.flatMap, List.map_ofFn, Function.comp_def] using h

private theorem flatten_ofFn_perm {n : ℕ} {T : Type*} {f g : Fin n → List T}
    (h : ∀ i, (f i).Perm (g i)) : (List.ofFn f).flatten.Perm (List.ofFn g).flatten := by
  simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
    List.Perm.flatMap_left (List.ofFn (fun i : Fin n => i)) (fun i _ => h i)

/-- Reindex a concatenation by the dependent sum of its row indices. -/
private theorem ofFn_sigma_perm {n k : ℕ} (m : Fin n → ℕ)
    (en : Fin k ≃ Σ i : Fin n, Fin (m i)) {T : Type*} (f : (Σ i : Fin n, Fin (m i)) → T) :
    ((List.ofFn fun i => List.ofFn fun j => f ⟨i, j⟩).flatten).Perm (List.ofFn fun i => f (en i)) := by
  let row (i : Fin n) := List.ofFn fun j : Fin (m i) => (⟨i, j⟩ : Σ i : Fin n, Fin (m i))
  let l := (List.ofFn row).flatten
  have hn : l.Nodup := by
    refine List.nodup_flatten.mpr ⟨?_, ?_⟩
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact List.nodup_ofFn.mpr (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      apply List.disjoint_left.mpr
      intro p hi hj
      have hi' : p.1 = i := by obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hi; rfl
      have hj' : p.1 = j := by obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hj; rfl
      exact (ne_of_lt hij) (hi'.symm.trans hj')
  have hmem (p : Σ i : Fin n, Fin (m i)) : p ∈ l :=
    List.mem_flatten.mpr ⟨row p.1, List.mem_ofFn.mpr ⟨p.1, rfl⟩, List.mem_ofFn.mpr ⟨p.2, rfl⟩⟩
  have hp : l.Perm (List.ofFn en) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_ofFn.mpr en.injective)).mpr
    intro p
    exact iff_of_true (hmem p) (List.mem_ofFn.mpr ⟨en.symm p, en.apply_symm_apply p⟩)
  simpa only [l, row, List.map_flatten, List.map_ofFn, Function.comp_def] using hp.map f

end Lists

set_option maxHeartbeats 800000 in
/-- The complex-place parameter of the identity Mackey constituent induces in stages. -/
theorem proposition48PrimeInducedParameterStages :
    Proposition48PrimeInducedParameterStagesStatement.{uF} := by
  classical
  intro Q D hD
  let M := Q.mackeyField D 1
  let : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  let : IsScalarTower Q.E D M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro v d en ds hds
  choose n inner a ha hperm using hds
  let e := Q.identityMackeyEquiv D hD
  let k : Fin d → ℕ := fun i => n (en i)
  let I := Σ i : Fin d, Fin (k i)
  let w (i : I) := en i.1
  let u (i : I) : InfinitePlacesAbove M (w i).1 := inner (w i) i.2
  let aTop (i : I) := a (w i) (u i)
  let φ : I ≃ InfinitePlacesAbove Q.E' v.1 :=
    ((Equiv.sigmaCongr en (fun i => inner (en i))).trans
      (infinitePlacesTower (M := M) v.1)).trans (infinitePlacesComap e v.1)
  have hφ (i : I) : (φ i).1 = (u i).1.comap e.toRingEquiv.toRingHom := rfl
  let a' (i : I) := readBlock e.toRingEquiv.toRingHom (φ i).1 (u i).1 (aTop i)
  let dξ (z : InfinitePlacesAbove Q.E' v.1) := a' (φ.symm z)
  have dξ_eq (i : I) : dξ (φ i) = a' i := congrArg a' (φ.symm_apply_apply i)
  have hξ (z : InfinitePlacesAbove Q.E' v.1) :
      Q.ξ.HasComplexPlaceParameter (complexPlaceAbove v z) (dξ z) := by
    obtain ⟨i, rfl⟩ := φ.surjective z
    rw [dξ_eq i]
    have h := hasComplexPlaceParameter_comap e.toRingEquiv (Q.mackeyCharacter D 1)
      (complexPlaceAbove v (φ i)) (complexPlaceAbove (complexPlaceAbove v (w i)) (u i))
      (hφ i).symm (aTop i) (ha (w i) (u i))
    change (HeckeCharacter.comap (Q.identityMackeyEquiv D hD).toRingEquiv
      (Q.mackeyCharacter D 1)).HasComplexPlaceParameter (complexPlaceAbove v (φ i)) (a' i) at h
    rw [Q.identityMackeyEquiv_comap D hD] at h
    exact h
  let staged (i : I) := readBlock (algebraMap Q.E D) v.1 (w i).1
    (readBlock (algebraMap D M) (w i).1 (u i).1 (aTop i))
  have he : e.toRingEquiv.toRingHom.comp (algebraMap Q.E Q.E') = algebraMap Q.E M :=
    RingHom.ext e.commutes
  have compare (i : I) : staged i =
      readBlock (algebraMap Q.E Q.E') v.1 (φ i).1 (dξ (φ i)) := by
    rw [dξ_eq i]
    have hs := readBlock_comp (algebraMap Q.E D) (algebraMap D M) v.1 (w i).1 (u i).1
      v.2 (complexPlaceAbove v (w i)).2 (InfinitePlace.LiesOver.comap_eq (w i).1 v.1)
      (InfinitePlace.LiesOver.comap_eq (u i).1 (w i).1) (aTop i)
    have ht := readBlock_comp (algebraMap Q.E Q.E') e.toRingEquiv.toRingHom v.1 (φ i).1 (u i).1
      v.2 (complexPlaceAbove v (φ i)).2 (InfinitePlace.LiesOver.comap_eq (φ i).1 v.1)
      (hφ i).symm (aTop i)
    rw [← IsScalarTower.algebraMap_eq Q.E D M] at hs
    rw [he] at ht
    exact hs.trans ht.symm
  have hstage : (complexPlaceLanglandsSum v en ds).Perm
      (List.ofFn (fun i : Fin d => List.ofFn fun j : Fin (k i) => staged ⟨i, j⟩)).flatten := by
    unfold complexPlaceLanglandsSum
    apply flatten_ofFn_perm
    intro i
    rw [transport_eq_map]
    have h := (hperm (en i)).map (readBlock (algebraMap Q.E D) v.1 (en i).1)
    rw [langlandsSum_singletons, List.map_ofFn] at h
    exact h
  let enum := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, enum.trans φ, dξ, hξ, hstage.trans ?_⟩
  refine (ofFn_sigma_perm k enum staged).trans ?_
  rw [langlandsSum_singletons]
  apply List.Perm.of_eq
  exact congrArg List.ofFn (funext fun i => compare (enum i))

end Langlands.Global.Harris
