import Langlands.Algebra.BrauerCorestriction.CentralSimple

/-!
# Independence of the Galois closure

A `K`-embedding `ι : N → N'` of finite Galois extensions with the same number of embeddings of
`L` induces a Galois-equivariant semilinear comparison map of the tensor products of conjugates,
hence a `K`-algebra isomorphism of the descended algebras. Every finite Galois `N` admitting
`[L : K]` embeddings of `L` receives an embedding of the canonical closure, so the descended
algebra does not depend on the closure up to `K`-algebra isomorphism.
-/

universe u₁ u₂ u₃ u₄ u₅

open TensorProduct PiTensorProduct Module IntermediateField
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section EmbMap

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} {N' : Type u₅} [Field K] [Field L]
  [Field N] [Field N'] [Algebra K L] [Algebra K N] [Algebra K N']
variable (A : Type u₄) [Ring A] [Algebra L A]

/-- A `K`-embedding `F : N → N'` with `F ∘ σ = τ`, as an `L`-algebra map of twists. -/
def twistEmb (F : N →ₐ[K] N') (σ : L →ₐ[K] N) (τ : L →ₐ[K] N') (h : ∀ l, F (σ l) = τ l) :
    Twist σ →ₐ[L] Twist τ :=
  { (F : N →+* N') with commutes' := h }

/-- The map `A^σ → A^τ`, `x ⊗ a ↦ F x ⊗ a`, semilinear over the embedding `F`. -/
noncomputable def embMap (F : N →ₐ[K] N') (σ : L →ₐ[K] N) (τ : L →ₐ[K] N')
    (h : ∀ l, F (σ l) = τ l) : Conj A σ →ₛₗ[(F : N →+* N')] Conj A τ where
  toFun := Algebra.TensorProduct.map (twistEmb F σ τ h) (AlgHom.id L A)
  map_add' := map_add _
  map_smul' n c := by
    induction c using TensorProduct.inductionOn with
    | tmul x a =>
      rw [smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        smul_tmul']
      congr 1
      exact map_mul F n x
    | add c₁ c₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]

variable {A}

@[simp]
theorem embMap_tmul (F : N →ₐ[K] N') (σ : L →ₐ[K] N) (τ : L →ₐ[K] N')
    (h : ∀ l, F (σ l) = τ l) (x : Twist σ) (a : A) :
    embMap A F σ τ h (x ⊗ₜ a) = twistEmb F σ τ h x ⊗ₜ a := rfl

theorem embMap_one (F : N →ₐ[K] N') (σ : L →ₐ[K] N) (τ : L →ₐ[K] N')
    (h : ∀ l, F (σ l) = τ l) : embMap A F σ τ h 1 = 1 :=
  map_one (Algebra.TensorProduct.map (twistEmb F σ τ h) (AlgHom.id L A))

theorem embMap_mul (F : N →ₐ[K] N') (σ : L →ₐ[K] N) (τ : L →ₐ[K] N')
    (h : ∀ l, F (σ l) = τ l) (x y : Conj A σ) :
    embMap A F σ τ h (x * y) = embMap A F σ τ h x * embMap A F σ τ h y :=
  map_mul (Algebra.TensorProduct.map (twistEmb F σ τ h) (AlgHom.id L A)) x y

theorem embMap_conjMap (F : N →ₐ[K] N') (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N)
    (ρ : L →ₐ[K] N') (hg : ∀ l, g (σ l) = τ l) (hF : ∀ l, F (τ l) = ρ l) (c : Conj A σ) :
    embMap A F τ ρ hF (conjMap A g σ τ hg c) =
      embMap A (F.comp (g : N →ₐ[K] N)) σ ρ (fun l => (congrArg F (hg l)).trans (hF l)) c := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]

theorem conjMap_embMap (g' : N' ≃ₐ[K] N') (F : N →ₐ[K] N') (σ : L →ₐ[K] N)
    (τ ρ : L →ₐ[K] N') (hF : ∀ l, F (σ l) = τ l) (hg : ∀ l, g' (τ l) = ρ l) (c : Conj A σ) :
    conjMap A g' τ ρ hg (embMap A F σ τ hF c) =
      embMap A ((g' : N' →ₐ[K] N').comp F) σ ρ
        (fun l => (congrArg g' (hF l)).trans (hg l)) c := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]

/-- Pure tensors of embedded factors depend only on the embedding and on the source-index
function. -/
theorem tprod_embMap_congr {F₁ F₂ : N →ₐ[K] N'} (hF : F₁ = F₂)
    {k₁ k₂ : (L →ₐ[K] N') → (L →ₐ[K] N)} (hk : k₁ = k₂)
    (h₁ : ∀ ρ l, F₁ (k₁ ρ l) = ρ l) (h₂ : ∀ ρ l, F₂ (k₂ ρ l) = ρ l)
    (x : ∀ σ : L →ₐ[K] N, Conj A σ) :
    PiTensorProduct.tprod N' (fun ρ => embMap A F₁ (k₁ ρ) ρ (h₁ ρ) (x (k₁ ρ))) =
      PiTensorProduct.tprod N' (fun ρ => embMap A F₂ (k₂ ρ) ρ (h₂ ρ) (x (k₂ ρ))) := by
  subst hF
  subst hk
  rfl

end EmbMap

section Compare

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} {N' : Type u₅} [Field K] [Field L]
  [Field N] [Field N'] [Algebra K L] [Algebra K N] [Algebra K N']
variable (A : Type u₄) [Ring A] [Algebra L A]
variable (ι : N →ₐ[K] N') (e : (L →ₐ[K] N) ≃ (L →ₐ[K] N')) (he : ∀ σ, e σ = ι.comp σ)

include he in
theorem apply_symm_emb (τ : L →ₐ[K] N') (l : L) : ι (e.symm τ l) = τ l :=
  (DFunLike.congr_fun ((e.apply_symm_apply τ).symm.trans (he (e.symm τ))) l).symm

/-- The comparison map `⨂_N σ, A^σ → ⨂_{N'} τ, A^τ`, semilinear over `ι`: reindex along `e`
and apply `x ⊗ a ↦ ι x ⊗ a` in each factor. -/
noncomputable def compareMap :
    ConjTensor K L N A →ₛₗ[(ι : N →+* N')] ConjTensor K L N' A :=
  (piTensorSemilinear (ι : N →+* N')
      (fun τ => embMap A ι (e.symm τ) τ (apply_symm_emb ι e he τ))).comp
    (reindex N (fun σ => Conj A σ) e).toLinearMap

variable {A}

theorem compareMap_tprod (x : ∀ σ : L →ₐ[K] N, Conj A σ) :
    compareMap A ι e he (PiTensorProduct.tprod N x) = PiTensorProduct.tprod N' (fun τ =>
      embMap A ι (e.symm τ) τ (apply_symm_emb ι e he τ) (x (e.symm τ))) := by
  simp only [compareMap, LinearMap.comp_apply, LinearEquiv.coe_coe, reindex_tprod,
    piTensorSemilinear_tprod]

theorem compareMap_one : compareMap A ι e he 1 = 1 := by
  simp only [compareMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [reindex_one, piTensorSemilinear_one _ (fun τ => embMap_one ι _ τ _)]

theorem compareMap_mul (x y : ConjTensor K L N A) :
    compareMap A ι e he (x * y) = compareMap A ι e he x * compareMap A ι e he y := by
  simp only [compareMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [reindex_mul, piTensorSemilinear_mul _ (fun τ => embMap_mul ι _ τ _)]

theorem compareMap_smul (k : K) (v : ConjTensor K L N A) :
    compareMap A ι e he (k • v) = k • compareMap A ι e he v := by
  rw [← algebraMap_smul N k v, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes, algebraMap_smul]

/-- The comparison map intertwines the Galois actions along compatible automorphisms. -/
theorem compareMap_actMap (g : N ≃ₐ[K] N) (g' : N' ≃ₐ[K] N') (hg : ∀ x, ι (g x) = g' (ι x))
    (v : ConjTensor K L N A) :
    actMap A g' (compareMap A ι e he v) = compareMap A ι e he (actMap A g v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, compareMap_tprod, actMap_tprod,
      actMap_tprod, compareMap_tprod]
    refine congrArg₂ (· • ·) (by simp [hg]) ?_
    simp only [conjMap_embMap, embMap_conjMap]
    have hsymm : ∀ y, ι (g.symm y) = g'.symm (ι y) := fun y => by
      apply g'.injective
      rw [← hg, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    refine tprod_embMap_congr (AlgHom.ext fun y => (hg y).symm) ?_ _ _ x
    funext ρ
    apply e.injective
    rw [Equiv.apply_symm_apply, he]
    ext l
    simp only [galPerm_symm_apply_apply, AlgHom.comp_apply]
    rw [hsymm, apply_symm_emb ι e he]
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]

theorem compareMap_mem_corAlg
    (hN : ∀ g' : N' ≃ₐ[K] N', ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x))
    {v : ConjTensor K L N A} (hv : v ∈ corAlg K L N A) :
    compareMap A ι e he v ∈ corAlg K L N' A := by
  rw [mem_corAlg] at hv ⊢
  intro g'
  obtain ⟨g, hg⟩ := hN g'
  rw [compareMap_actMap ι e he g g' hg, hv g]

variable (A)

/-- The `K`-algebra map of descended algebras induced by the comparison map. -/
noncomputable def corAlgHom
    (hN : ∀ g' : N' ≃ₐ[K] N', ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x)) :
    corAlg K L N A →ₐ[K] corAlg K L N' A where
  toFun v := ⟨compareMap A ι e he v, compareMap_mem_corAlg ι e he hN v.2⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    exact compareMap_one ι e he
  map_mul' x y := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    exact compareMap_mul ι e he (x : ConjTensor K L N A) (y : ConjTensor K L N A)
  map_zero' := by
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add]
    exact map_add _ (x : ConjTensor K L N A) (y : ConjTensor K L N A)
  commutes' k := Subtype.ext (by
    change compareMap A ι e he (algebraMap K _ k) = algebraMap K _ k
    rw [Algebra.algebraMap_eq_smul_one, compareMap_smul, compareMap_one,
      Algebra.algebraMap_eq_smul_one])

@[simp]
theorem corAlgHom_apply
    (hN : ∀ g' : N' ≃ₐ[K] N', ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x))
    (v : corAlg K L N A) :
    (corAlgHom A ι e he hN v : ConjTensor K L N' A) = compareMap A ι e he v := rfl

variable [FiniteDimensional K L] [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A]
  [FiniteDimensional K N] [IsGalois K N] [FiniteDimensional K N'] [IsGalois K N']

theorem corAlgHom_bijective
    (hN : ∀ g' : N' ≃ₐ[K] N', ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x)) :
    Function.Bijective (corAlgHom A ι e he hN) := by
  have : IsSimpleRing (corAlg K L N A) := isSimpleRing_corAlg K L N A
  have : IsSimpleRing (corAlg K L N' A) := isSimpleRing_corAlg K L N' A
  have : FiniteDimensional K (corAlg K L N A) := finiteDimensional_corAlg K L N A
  have : FiniteDimensional K (corAlg K L N' A) := finiteDimensional_corAlg K L N' A
  have hinj : Function.Injective (corAlgHom A ι e he hN) := by
    rcases IsSimpleRing.injective_ringHom_or_subsingleton_codomain (R := corAlg K L N A)
      (S := corAlg K L N' A) (corAlgHom A ι e he hN).toRingHom with h | h
    · exact h
    · have : Nontrivial (corAlg K L N' A) := IsSimpleRing.instNontrivial
      exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hdim : finrank K (corAlg K L N A) = finrank K (corAlg K L N' A) := by
    rw [finrank_corAlg_eq_pow, finrank_corAlg_eq_pow, Nat.card_congr e]
  let f : corAlg K L N A →ₗ[K] corAlg K L N' A :=
    { toFun := corAlgHom A ι e he hN
      map_add' := map_add _
      map_smul' := fun c x => map_smul (corAlgHom A ι e he hN) c x }
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := K)
    (V := corAlg K L N A) (V₂ := corAlg K L N' A) (f := f) hdim
  exact key.mp hinj

/-- The descended algebras over `N` and `N'` are isomorphic `K`-algebras. -/
noncomputable def corAlgEquivOfEmb
    (hN : ∀ g' : N' ≃ₐ[K] N', ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x)) :
    corAlg K L N A ≃ₐ[K] corAlg K L N' A :=
  AlgEquiv.ofBijective (corAlgHom A ι e he hN) (corAlgHom_bijective A ι e he hN)

end Compare

section Canonical

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} {N' : Type u₅} [Field K] [Field L]
  [Field N] [Field N'] [Algebra K L] [Algebra K N] [Algebra K N']

/-- Every automorphism of `N'` restricts along a `K`-embedding of a normal extension `N`. -/
theorem exists_restrict [Normal K N] (ι : N →ₐ[K] N') (g' : N' ≃ₐ[K] N') :
    ∃ g : N ≃ₐ[K] N, ∀ x, ι (g x) = g' (ι x) := by
  let : Algebra N N' := ι.toRingHom.toAlgebra
  have : IsScalarTower K N N' := IsScalarTower.of_algebraMap_eq fun k => (ι.commutes k).symm
  exact ⟨g'.restrictNormal N, fun x => g'.restrictNormal_commutes N x⟩

/-- Composition with an embedding `ι : N → N'` is a bijection of `K`-embeddings of `L` when
both sides have the same finite number of elements. -/
theorem bijective_comp_of_natCard [FiniteDimensional K L] (ι : N →ₐ[K] N')
    (hcard : Nat.card (L →ₐ[K] N') = Nat.card (L →ₐ[K] N)) :
    Function.Bijective (fun σ : L →ₐ[K] N => ι.comp σ) :=
  Function.Injective.bijective_of_nat_card_le
    (fun _ _ h => AlgHom.ext fun l => ι.injective (DFunLike.congr_fun h l)) hcard.le

variable (K L)

/-- The canonical closure embeds into every normal extension admitting an embedding of `L`. -/
theorem nonempty_algHom_canonicalClosure [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Normal K N] (σ₀ : L →ₐ[K] N) : Nonempty (canonicalClosure K L →ₐ[K] N) := by
  have hpos : 0 < Nat.card (L →ₐ[K] SeparableClosure K) := by
    rw [← Nat.card_congr (normalClosure.algHomEquiv K L (SeparableClosure K)),
      natCard_algHom_canonicalClosure]
    exact Module.finrank_pos
  have : Nonempty (L →ₐ[K] SeparableClosure K) := Nat.card_pos_iff.mp hpos |>.1
  refine ⟨IsNormalClosure.lift (F := K) (K := L) (L := canonicalClosure K L) fun x => ?_⟩
  rw [← minpoly.algHom_eq σ₀ σ₀.injective x]
  exact Normal.splits inferInstance (σ₀ x)

variable (A : Type u₄) [Ring A] [Algebra L A]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A]

/-- Independence of the closure: for every finite Galois `N/K` admitting `[L : K]` embeddings
of `L`, the descended algebra over `N` is isomorphic to the one over the canonical closure. -/
theorem nonempty_corAlgEquiv_canonical [FiniteDimensional K N] [IsGalois K N]
    (hN : Nat.card (L →ₐ[K] N) = finrank K L) :
    Nonempty (corAlg K L (canonicalClosure K L) A ≃ₐ[K] corAlg K L N A) := by
  have hpos : 0 < Nat.card (L →ₐ[K] N) := hN ▸ Module.finrank_pos
  obtain ⟨σ₀⟩ : Nonempty (L →ₐ[K] N) := Nat.card_pos_iff.mp hpos |>.1
  obtain ⟨ι⟩ := nonempty_algHom_canonicalClosure K L σ₀
  have hbij := bijective_comp_of_natCard ι
    (hN.trans (natCard_algHom_canonicalClosure K L).symm)
  let e := Equiv.ofBijective _ hbij
  exact ⟨corAlgEquivOfEmb A ι e (fun σ => rfl) (exists_restrict ι)⟩

/-- Any two admissible finite Galois closures give isomorphic descended algebras. -/
theorem nonempty_corAlgEquiv [FiniteDimensional K N] [IsGalois K N] [FiniteDimensional K N']
    [IsGalois K N'] (hN : Nat.card (L →ₐ[K] N) = finrank K L)
    (hN' : Nat.card (L →ₐ[K] N') = finrank K L) :
    Nonempty (corAlg K L N A ≃ₐ[K] corAlg K L N' A) := by
  obtain ⟨f⟩ := nonempty_corAlgEquiv_canonical K L A hN
  obtain ⟨f'⟩ := nonempty_corAlgEquiv_canonical K L A hN'
  exact ⟨f.symm.trans f'⟩

end Canonical

end Langlands.BrauerCorestriction
