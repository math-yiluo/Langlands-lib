import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.Global.AdelicFunctoriality.CompletedLocalDegreeProof
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Weil.Local.AssemblyProof
import Langlands.WeilDeligne.InductionAlong

/-!
# Double cosets of a local map and the places of an intermediate field

For `F ⊆ K ⊆ E` with `E / F` Galois, a finite place `z` of `F`, a place `w` of `E`
above `z` and a homomorphism `ι : W_{F_z} → W_{E/F}` compatible with the embedding
`E → E_w → \bar{F_z}`, the double cosets `W_{E/K} \ W_{E/F} / ι(W_{F_z})` are indexed
by the places `u` of `K` above `z` (compare Tate (1979), (2.3.5)). Each `g ∈ W_{E/F}`
gives the `F`-embedding `k ↦ j_w((projection g)⁻¹ k)` of `K` into `\bar{F_z}`; two
elements lie in the same right coset of `W_{E/K}` exactly when these embeddings agree,
and right multiplication by `ι ℓ` composes with the Galois image of `ℓ⁻¹`. The
`F`-embeddings of `K` up to `G_{F_z}` correspond to the places above `z`, by the
bijectivity of `F_z ⊗_F K → ∏_u K_u`. The file constructs representatives of the
double cosets and the conjugated local maps `W_{K_u} → W_{E/K}`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

section Places

variable {F K : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (z : Langlands.Global.FinitePlace F)

/-- The embedding `K → K_u → \bar{F_z}` at a place `u` of `K` above `z`. -/
def placeEmbedding (u : FinitePlacesAbove K z) :
    K →+* AlgebraicClosure (z.adicCompletion F) :=
  (completionClosureEmbedding z u.1).comp (algebraMap K (u.1.adicCompletion K))

/-- The embedding `K_u → \bar{F_z}` along which `completionWeilMap z u` is formed, as a
homomorphism of `F_z`-algebras. -/
def placeClosureAlgHom (u : FinitePlacesAbove K z) :
    u.1.adicCompletion K →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) where
  toRingHom := completionClosureEmbedding z u.1
  commutes' := completionClosureEmbedding_algebraMap z u.1

theorem placeClosureAlgHom_algebraMap (u : FinitePlacesAbove K z) (k : K) :
    placeClosureAlgHom z u (algebraMap K (u.1.adicCompletion K) k) = placeEmbedding z u k :=
  rfl

/-- An automorphism of `\bar{F_z}` fixes the image of `K` under the place embedding at `u`
exactly when it lies in the image of the absolute Galois group of `K_u`. -/
theorem placeEmbedding_fixed_iff (u : FinitePlacesAbove K z)
    (τ : Field.absoluteGaloisGroup (padicField z).Carrier) :
    (∀ k : K, AlgEquiv.toAlgHom τ (placeEmbedding z u k) = placeEmbedding z u k) ↔
      τ ∈ (Weil.Local.extensionGaloisMap (padicField z) (towerPadicField z u.1)
        (completionPadicAlgHom z u.1)).toMonoidHom.range := by
  rw [Weil.Local.extensionGaloisMap_range]
  refine Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff
    (K := Weil.Local.extensionIntermediateField (padicField z) (towerPadicField z u.1)
      (completionPadicAlgHom z u.1)) τ).symm
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (Weil.Local.mem_extensionIntermediateField _ _ _ y).mp hy
    let f : u.1.adicCompletion K →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) :=
      (AlgEquiv.toAlgHom τ).comp (placeClosureAlgHom z u)
    have hS := subalgebra_eq_top_of_algebraMap_mem z u.1
      (AlgHom.equalizer f (placeClosureAlgHom z u)) (fun k => h k)
    have hx : x ∈ AlgHom.equalizer f (placeClosureAlgHom z u) := hS ▸ Algebra.mem_top
    exact hx
  · intro h k
    exact h _ ((Weil.Local.mem_extensionIntermediateField _ _ _ _).mpr ⟨_, rfl⟩)

theorem placeClosureAlgHom_completionMap (u : FinitePlacesAbove K z) (a : z.adicCompletion F) :
    placeClosureAlgHom z u (FiniteExtension.completionMap z u.1 a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F)) a :=
  (placeClosureAlgHom z u).commutes a

/-- Two places of `K` above `z` whose place embeddings differ by an automorphism of
`\bar{F_z}` are equal. -/
theorem eq_of_placeEmbedding_eq (u u' : FinitePlacesAbove K z)
    (τ : Field.absoluteGaloisGroup (padicField z).Carrier)
    (h : ∀ k : K, AlgEquiv.toAlgHom τ (placeEmbedding z u k) = placeEmbedding z u' k) :
    u = u' := by
  classical
  let ψ₁ : z.adicCompletion F ⊗[F] K →ₐ[z.adicCompletion F]
      AlgebraicClosure (z.adicCompletion F) :=
    (((AlgEquiv.toAlgHom τ).comp (placeClosureAlgHom z u)).comp
      (Pi.evalAlgHom _ _ u)).comp (finiteTensorMap z)
  let ψ₂ : z.adicCompletion F ⊗[F] K →ₐ[z.adicCompletion F]
      AlgebraicClosure (z.adicCompletion F) :=
    ((placeClosureAlgHom z u').comp (Pi.evalAlgHom _ _ u')).comp (finiteTensorMap z)
  have hψ : ψ₁ = ψ₂ := by
    apply Algebra.TensorProduct.ext'
    intro a k
    change AlgEquiv.toAlgHom τ (placeClosureAlgHom z u (finiteTensorMap z (a ⊗ₜ k) u)) =
      placeClosureAlgHom z u' (finiteTensorMap z (a ⊗ₜ k) u')
    rw [finiteTensorMap_tmul, finiteTensorMap_tmul, map_mul, map_mul, map_mul,
      placeClosureAlgHom_completionMap, placeClosureAlgHom_completionMap, AlgHom.commutes,
      placeClosureAlgHom_algebraMap, placeClosureAlgHom_algebraMap, h k]
  obtain ⟨t, ht⟩ := finiteTensorMap_surjective (L := K) z (Pi.single u 1)
  have h₁ : ψ₁ t = 1 := by
    change AlgEquiv.toAlgHom τ (placeClosureAlgHom z u (finiteTensorMap z t u)) = 1
    rw [ht, Pi.single_eq_same, map_one, map_one]
  by_contra hne
  have h₂ : ψ₂ t = 0 := by
    change placeClosureAlgHom z u' (finiteTensorMap z t u') = 0
    rw [ht, Pi.single_eq_of_ne' hne, map_zero]
  rw [hψ, h₂] at h₁
  exact zero_ne_one h₁

/-- Every `F`-embedding of `K` into `\bar{F_z}` is a place embedding followed by an
automorphism of `\bar{F_z}` over `F_z`. -/
theorem exists_placeEmbedding (ε : K →+* AlgebraicClosure (z.adicCompletion F))
    (hε : ∀ a : F, ε (algebraMap F K a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F))
        (algebraMap F (z.adicCompletion F) a)) :
    ∃ (u : FinitePlacesAbove K z) (τ : Field.absoluteGaloisGroup (padicField z).Carrier),
      ∀ k : K, ε k = AlgEquiv.toAlgHom τ (placeEmbedding z u k) := by
  classical
  have hbij := finiteTensorMap_bijective_of_local_degree_bounds (L := K) z
    (fun r => completedLocalDegreeLowerBound F K z r.1)
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := K) z) hbij
  let εA : K →ₐ[F] AlgebraicClosure (z.adicCompletion F) :=
    { ε with
      commutes' := fun a => (hε a).trans
        (IsScalarTower.algebraMap_apply F (z.adicCompletion F) _ a).symm }
  let ε' : z.adicCompletion F ⊗[F] K →ₐ[z.adicCompletion F]
      AlgebraicClosure (z.adicCompletion F) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) εA (fun _ _ => Commute.all _ _)
  let ψ := ε'.comp e.symm.toAlgHom
  have hψk : ∀ k : K,
      ψ (fun q : FinitePlacesAbove K z => algebraMap K (q.1.adicCompletion K) k) = ε k := by
    intro k
    have he : e (1 ⊗ₜ k) = fun q : FinitePlacesAbove K z => algebraMap K (q.1.adicCompletion K) k :=
      funext fun q => finiteTensorMap_one_tmul z k q
    change ε' (e.symm _) = _
    rw [← he, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  obtain ⟨u, hu⟩ : ∃ u : FinitePlacesAbove K z, ψ (Pi.single u 1) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := congrArg ψ (Finset.univ_sum_single (1 : ∀ q : FinitePlacesAbove K z,
      q.1.adicCompletion K))
    rw [map_sum, map_one] at h1
    simp only [Pi.one_apply, hall, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hu1 : ψ (Pi.single u 1) = 1 := by
    have hidem : ψ (Pi.single u 1) * ψ (Pi.single u 1) = ψ (Pi.single u 1) * 1 := by
      rw [← map_mul, ← Pi.single_mul, one_mul, mul_one]
    exact mul_left_cancel₀ hu hidem
  have hsingle : ∀ t : u.1.adicCompletion K,
      Pi.single u t = (Pi.single u 1 : ∀ q : FinitePlacesAbove K z, q.1.adicCompletion K) *
        Pi.single u t := by
    intro t
    rw [← Pi.single_mul, one_mul]
  let ψu : u.1.adicCompletion K →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) :=
    { toFun := fun t => ψ (Pi.single u t)
      map_one' := hu1
      map_mul' := fun s t => by
        rw [Pi.single_mul, map_mul]
      map_zero' := by
        rw [Pi.single_zero, map_zero]
      map_add' := fun s t => by
        rw [Pi.single_add, map_add]
      commutes' := fun a => by
        have ha : (Pi.single u (algebraMap (z.adicCompletion F) (u.1.adicCompletion K) a) :
            ∀ q : FinitePlacesAbove K z, q.1.adicCompletion K) =
            algebraMap (z.adicCompletion F) _ a * Pi.single u 1 := by
          funext q
          by_cases hq : q = u
          · subst hq
            simp [Pi.single_eq_same]
          · simp [Pi.single_eq_of_ne hq]
        rw [ha, map_mul, AlgHom.commutes, hu1, mul_one] }
  have hψu : ∀ k : K, ψu (algebraMap K (u.1.adicCompletion K) k) = ε k := by
    intro k
    have hk : (Pi.single u (algebraMap K (u.1.adicCompletion K) k) :
        ∀ q : FinitePlacesAbove K z, q.1.adicCompletion K) =
        Pi.single u 1 * fun q : FinitePlacesAbove K z => algebraMap K (q.1.adicCompletion K) k := by
      funext q
      by_cases hq : q = u
      · subst hq
        simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hq]
    change ψ (Pi.single u _) = _
    rw [hk, map_mul, hu1, one_mul, hψk]
  let : Algebra (u.1.adicCompletion K) (AlgebraicClosure (z.adicCompletion F)) :=
    (completionClosureEmbedding z u.1).toAlgebra
  have : IsScalarTower (z.adicCompletion F) (u.1.adicCompletion K)
      (AlgebraicClosure (z.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a => (completionClosureEmbedding_algebraMap z u.1 a).symm
  let σ := ψu.liftNormal (AlgebraicClosure (z.adicCompletion F))
  have hσ : ∀ x : u.1.adicCompletion K, σ (completionClosureEmbedding z u.1 x) = ψu x :=
    fun x => AlgHom.liftNormal_commutes ψu _ x
  refine ⟨u, (AlgEquiv.ofBijective σ (AlgHom.normal_bijective _ _ _ σ) :
    Field.absoluteGaloisGroup (padicField z).Carrier), fun k => ?_⟩
  change ε k = σ (completionClosureEmbedding z u.1 (algebraMap K (u.1.adicCompletion K) k))
  rw [hσ, hψu]

/-- Every map with dense range into `G_{F_z}` meets, on the place embedding at `u`, every
automorphism of `\bar{F_z}`: the set of automorphisms agreeing with `τ` there is a translate
of the open range of `extensionGaloisMap`. -/
theorem exists_dense_placeEmbedding {X : Type*} (f : X → Field.absoluteGaloisGroup
      (padicField z).Carrier) (hf : DenseRange f) (u : FinitePlacesAbove K z)
    (τ : Field.absoluteGaloisGroup (padicField z).Carrier) :
    ∃ x : X, ∀ k : K,
      AlgEquiv.toAlgHom (f x) (placeEmbedding z u k) =
        AlgEquiv.toAlgHom τ (placeEmbedding z u k) := by
  let R := (Weil.Local.extensionGaloisMap (padicField z) (towerPadicField z u.1)
    (completionPadicAlgHom z u.1)).toMonoidHom.range
  have hR : IsOpen ((fun σ => τ⁻¹ * σ) ⁻¹' (R : Set (Field.absoluteGaloisGroup
      (padicField z).Carrier))) :=
    (Weil.Local.extensionGaloisMap_range_isOpen _ _ _).preimage (continuous_const.mul continuous_id)
  obtain ⟨x, hx⟩ := hf.exists_mem_open hR ⟨τ, by simp [R.one_mem]⟩
  refine ⟨x, fun k => ?_⟩
  have hfix := (placeEmbedding_fixed_iff z u _).mpr hx k
  rw [← mul_inv_cancel_left τ (f x)]
  exact congrArg (AlgEquiv.toAlgHom τ) hfix

/-- Every automorphism of `\bar{F_z}` agrees on the place embedding at `u` with the Galois
image of an element of the local Weil group. -/
theorem exists_localProjection_placeEmbedding (u : FinitePlacesAbove K z)
    (τ : Field.absoluteGaloisGroup (padicField z).Carrier) :
    ∃ ℓ : Weil.Local.localWeilGroup (padicField z), ∀ k : K,
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ) (placeEmbedding z u k) =
        AlgEquiv.toAlgHom τ (placeEmbedding z u k) :=
  exists_dense_placeEmbedding z (Weil.Local.localProjection (padicField z))
    (Weil.Local.localProjection_denseRange (padicField z)) u τ

/-- Every homomorphism of `F_z`-algebras `K_u → \bar{F_z}` is `completionClosureEmbedding z u`
followed by an automorphism of `\bar{F_z}` over `F_z`. -/
theorem exists_eq_comp_completionClosureEmbedding (u : FinitePlacesAbove K z)
    (κ : u.1.adicCompletion K →+* AlgebraicClosure (z.adicCompletion F))
    (hκ : ∀ a : z.adicCompletion F, κ (algebraMap (z.adicCompletion F) (u.1.adicCompletion K) a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F)) a) :
    ∃ τ : Field.absoluteGaloisGroup (padicField z).Carrier, ∀ x : u.1.adicCompletion K,
      κ x = AlgEquiv.toAlgHom τ (completionClosureEmbedding z u.1 x) := by
  let κA : u.1.adicCompletion K →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) :=
    { κ with commutes' := hκ }
  let _ : Algebra (u.1.adicCompletion K) (AlgebraicClosure (z.adicCompletion F)) :=
    (completionClosureEmbedding z u.1).toAlgebra
  have : IsScalarTower (z.adicCompletion F) (u.1.adicCompletion K)
      (AlgebraicClosure (z.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a => (completionClosureEmbedding_algebraMap z u.1 a).symm
  let σ := κA.liftNormal (AlgebraicClosure (z.adicCompletion F))
  refine ⟨(AlgEquiv.ofBijective σ (AlgHom.normal_bijective _ _ _ σ) :
    Field.absoluteGaloisGroup (padicField z).Carrier), fun x => ?_⟩
  exact (AlgHom.liftNormal_commutes κA _ x).symm

end Places

section Cosets

attribute [local instance] relativeGaloisTopology

variable (c : FundamentalClass.ClassFamily.{u}) {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (K : Type u) [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal]

/-- The embedding `E → E_w → \bar{F_z}` of the local condition. -/
def closurePlaceEmbedding : E →+* AlgebraicClosure (z.adicCompletion F) :=
  (completionClosureEmbedding z w).comp (algebraMap E (w.adicCompletion E))

omit [IsGalois F E] in
theorem closurePlaceEmbedding_algebraMap (a : F) :
    closurePlaceEmbedding z w (algebraMap F E a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F))
        (algebraMap F (z.adicCompletion F) a) := by
  change completionClosureEmbedding z w (algebraMap E (w.adicCompletion E) (algebraMap F E a)) = _
  rw [← FiniteExtension.completionMap_coe z w]
  exact completionClosureEmbedding_algebraMap z w _

/-- The `F`-embedding of `K` attached to `g ∈ W_{E/F}`:
`k ↦ j_w((projection g)⁻¹ k)`. -/
def cosetEmbedding (g : RelativeWeilGroup c F E) : K →+* AlgebraicClosure (z.adicCompletion F) :=
  ((closurePlaceEmbedding z w).comp (projection c F E g)⁻¹.toAlgHom.toRingHom).comp
    (algebraMap K E)

omit [NumberField K] [Algebra F K] [IsScalarTower F K E] in
theorem cosetEmbedding_apply (g : RelativeWeilGroup c F E) (k : K) :
    cosetEmbedding c K z w g k =
      closurePlaceEmbedding z w ((projection c F E g)⁻¹ (algebraMap K E k)) :=
  rfl

omit [NumberField K] in
theorem cosetEmbedding_algebraMap (g : RelativeWeilGroup c F E) (a : F) :
    cosetEmbedding c K z w g (algebraMap F K a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F))
        (algebraMap F (z.adicCompletion F) a) := by
  rw [cosetEmbedding_apply, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    closurePlaceEmbedding_algebraMap]

omit [NumberField F] [NumberField E] [IsGalois F E] [NumberField K] in
theorem aut_inv_apply_apply (σ : E ≃ₐ[F] E) (x : E) : σ⁻¹ (σ x) = x := by
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

omit [NumberField F] [NumberField E] [IsGalois F E] [NumberField K] in
theorem aut_apply_inv_apply (σ : E ≃ₐ[F] E) (x : E) : σ (σ⁻¹ x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

omit [NumberField F] [NumberField E] [IsGalois F E] [NumberField K] in
theorem mem_range_restrictScalarsHom_iff (σ : E ≃ₐ[F] E) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : (E ≃ₐ[K] E) →* (E ≃ₐ[F] E)).range ↔
      ∀ k : K, σ (algebraMap K E k) = algebraMap K E k := by
  constructor
  · rintro ⟨τ, rfl⟩ k
    exact τ.commutes k
  · intro hσ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, ?_⟩
    ext x
    rfl

variable (h : FundamentalClass.Restriction c)

/-- Two elements of `W_{E/F}` lie in the same right coset of the image of `W_{E/K}` exactly
when their coset embeddings agree. -/
theorem mem_range_restrictionInclusion_iff (g g' : RelativeWeilGroup c F E) :
    g' * g⁻¹ ∈ (restrictionInclusion c F E K h).toMonoidHom.range ↔
      ∀ k : K, cosetEmbedding c K z w g k = cosetEmbedding c K z w g' k := by
  rw [range_restrictionInclusion, Subgroup.mem_comap, map_mul, map_inv,
    mem_range_restrictScalarsHom_iff]
  simp only [cosetEmbedding_apply]
  constructor
  · intro hk k
    congr 1
    have := congrArg (fun y : E => ((projection c F E g')⁻¹ : E ≃ₐ[F] E) y) (hk k)
    simp only [AlgEquiv.mul_apply, aut_inv_apply_apply] at this
    exact this
  · intro hk k
    have := (closurePlaceEmbedding z w).injective (hk k)
    rw [AlgEquiv.mul_apply, this, aut_apply_inv_apply]

/-- Every place embedding of `K` is the coset embedding of some element of `W_{E/F}`. -/
theorem exists_cosetEmbedding_eq (u : FinitePlacesAbove K z) :
    ∃ g : RelativeWeilGroup c F E, ∀ k : K,
      cosetEmbedding c K z w g k = placeEmbedding z u k := by
  have hu : ∀ a : F, placeEmbedding z u (algebraMap F K a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F))
        (algebraMap F (z.adicCompletion F) a) := by
    intro a
    change completionClosureEmbedding z u.1
      (algebraMap K (u.1.adicCompletion K) (algebraMap F K a)) = _
    rw [← FiniteExtension.completionMap_coe z u.1]
    exact completionClosureEmbedding_algebraMap z u.1 _
  let _ : Algebra K (AlgebraicClosure (z.adicCompletion F)) := (placeEmbedding z u).toAlgebra
  have : IsScalarTower F K (AlgebraicClosure (z.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsScalarTower.algebraMap_apply F (z.adicCompletion F) _ a).trans (hu a).symm
  let φ : E →ₐ[K] AlgebraicClosure (z.adicCompletion F) := IsAlgClosed.lift
  let φF : E →ₐ[F] AlgebraicClosure (z.adicCompletion F) := φ.restrictScalars F
  let _ : Algebra E (AlgebraicClosure (z.adicCompletion F)) := (closurePlaceEmbedding z w).toAlgebra
  have : IsScalarTower F E (AlgebraicClosure (z.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsScalarTower.algebraMap_apply F (z.adicCompletion F) _ a).trans
        (closurePlaceEmbedding_algebraMap z w a).symm
  have : Normal F E := IsGalois.to_normal
  obtain ⟨g, hg⟩ := projection_surjective c F E (φF.restrictNormal' E)⁻¹
  refine ⟨g, fun k => ?_⟩
  rw [cosetEmbedding_apply, hg, inv_inv]
  change algebraMap E (AlgebraicClosure (z.adicCompletion F))
    (φF.restrictNormal E (algebraMap K E k)) = _
  rw [AlgHom.restrictNormal_commutes]
  change φ (algebraMap K E k) = _
  rw [φ.commutes]
  rfl

variable (ι : Weil.Local.localWeilGroup (padicField z) →* RelativeWeilGroup c F E)
  (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
    closurePlaceEmbedding z w (projection c F E (ι g) x) =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
        (closurePlaceEmbedding z w x))

include hι in
omit [NumberField K] [Algebra F K] [IsScalarTower F K E] in
/-- Right multiplication by the image of `ℓ ∈ W_{F_z}` composes the coset embedding with
the Galois image of `ℓ⁻¹`. -/
theorem cosetEmbedding_mul (g : RelativeWeilGroup c F E)
    (ℓ : Weil.Local.localWeilGroup (padicField z)) (k : K) :
    cosetEmbedding c K z w (g * ι ℓ) k =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ⁻¹)
        (cosetEmbedding c K z w g k) := by
  rw [cosetEmbedding_apply, cosetEmbedding_apply, map_mul, mul_inv_rev, AlgEquiv.mul_apply,
    ← map_inv (projection c F E) (ι ℓ), ← map_inv ι, hι]

theorem absoluteGalois_inv_apply_apply (σ : Field.absoluteGaloisGroup (padicField z).Carrier)
    (y : AlgebraicClosure (z.adicCompletion F)) :
    AlgEquiv.toAlgHom σ⁻¹ (AlgEquiv.toAlgHom σ y) = y := by
  change AlgEquiv.toAlgHom (σ⁻¹ * σ) y = y
  rw [inv_mul_cancel]
  rfl

include hι in
/-- The conjugate of `ι ℓ` by a representative of the place `u` lies in the image of
`W_{E/K}` exactly when `ℓ` lies in the image of `W_{K_u}`. -/
theorem conj_mem_range_restrictionInclusion_iff (u : FinitePlacesAbove K z)
    (x : RelativeWeilGroup c F E) (hx : ∀ k : K, cosetEmbedding c K z w x k = placeEmbedding z u k)
    (ℓ : Weil.Local.localWeilGroup (padicField z)) :
    x * ι ℓ * x⁻¹ ∈ (restrictionInclusion c F E K h).toMonoidHom.range ↔
      ℓ ∈ (completionWeilMap z u.1).toMonoidHom.range := by
  rw [mem_range_restrictionInclusion_iff c K z w h x (x * ι ℓ)]
  simp only [cosetEmbedding_mul c K z w ι hι, hx]
  calc (∀ k : K, placeEmbedding z u k = AlgEquiv.toAlgHom
          (Weil.Local.localProjection (padicField z) ℓ⁻¹) (placeEmbedding z u k)) ↔
        ∀ k : K, AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ⁻¹)
          (placeEmbedding z u k) = placeEmbedding z u k := forall_congr' fun _ => eq_comm
    _ ↔ ℓ⁻¹ ∈ (completionWeilMap z u.1).toMonoidHom.range := by
      rw [placeEmbedding_fixed_iff, completionWeilMap, Weil.Local.extensionWeilMap_range]
      rfl
    _ ↔ ℓ ∈ (completionWeilMap z u.1).toMonoidHom.range := Subgroup.inv_mem_iff _

include hι in
/-- The double cosets of distinct places are disjoint. -/
theorem place_eq_of_mul_eq [IsGalois K E] (x : FinitePlacesAbove K z → RelativeWeilGroup c F E)
    (hx : ∀ u k, cosetEmbedding c K z w (x u) k = placeEmbedding z u k)
    (m m' : RelativeWeilGroup c K E) (u u' : FinitePlacesAbove K z)
    (ℓ ℓ' : Weil.Local.localWeilGroup (padicField z))
    (heq : restrictionInclusion c F E K h m * (x u * ι ℓ) =
      restrictionInclusion c F E K h m' * (x u' * ι ℓ')) :
    u = u' := by
  have hleft : ∀ (n : RelativeWeilGroup c K E) (y : RelativeWeilGroup c F E) (k : K),
      cosetEmbedding c K z w y k =
        cosetEmbedding c K z w (restrictionInclusion c F E K h n * y) k := by
    intro n y
    exact (mem_range_restrictionInclusion_iff c K z w h y _).mp
      ⟨n, (mul_inv_cancel_right _ _).symm⟩
  have h3 : ∀ k : K, cosetEmbedding c K z w (x u * ι ℓ) k =
      cosetEmbedding c K z w (x u' * ι ℓ') k := fun k =>
    ((hleft m _ k).trans (congrArg (fun g => cosetEmbedding c K z w g k) heq)).trans
      (hleft m' _ k).symm
  simp only [cosetEmbedding_mul c K z w ι hι, hx] at h3
  apply eq_of_placeEmbedding_eq z u u'
    ((Weil.Local.localProjection (padicField z) ℓ'⁻¹)⁻¹ *
      Weil.Local.localProjection (padicField z) ℓ⁻¹)
  intro k
  change AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ'⁻¹)⁻¹
    (AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ⁻¹) (placeEmbedding z u k)) = _
  rw [h3 k, absoluteGalois_inv_apply_apply]

include hι in
/-- The double cosets of the places cover `W_{E/F}`. -/
theorem exists_eq_mul [IsGalois K E] (x : FinitePlacesAbove K z → RelativeWeilGroup c F E)
    (hx : ∀ u k, cosetEmbedding c K z w (x u) k = placeEmbedding z u k)
    (g : RelativeWeilGroup c F E) :
    ∃ (m : RelativeWeilGroup c K E) (u : FinitePlacesAbove K z)
      (ℓ : Weil.Local.localWeilGroup (padicField z)),
      g = restrictionInclusion c F E K h m * (x u * ι ℓ) := by
  obtain ⟨u, τ, hτ⟩ := exists_placeEmbedding z (cosetEmbedding c K z w g)
    (cosetEmbedding_algebraMap c K z w g)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_localProjection_placeEmbedding z u τ
  have hk : ∀ k : K, cosetEmbedding c K z w (x u * ι ℓ₀⁻¹) k = cosetEmbedding c K z w g k := by
    intro k
    rw [cosetEmbedding_mul c K z w ι hι, inv_inv, hx, hℓ₀, hτ]
  obtain ⟨m, hm⟩ := (mem_range_restrictionInclusion_iff c K z w h (x u * ι ℓ₀⁻¹) g).mpr hk
  exact ⟨m, u, ℓ₀⁻¹, mul_inv_eq_iff_eq_mul.mp hm.symm⟩

/-- A representative in `W_{E/F}` of the double coset of the place `u`: an element whose
coset embedding is the place embedding at `u`. -/
def placeRepresentative (u : FinitePlacesAbove K z) : RelativeWeilGroup c F E :=
  (exists_cosetEmbedding_eq c K z w u).choose

theorem cosetEmbedding_placeRepresentative (u : FinitePlacesAbove K z) (k : K) :
    cosetEmbedding c K z w (placeRepresentative c K z w u) k = placeEmbedding z u k :=
  (exists_cosetEmbedding_eq c K z w u).choose_spec k

include h in
/-- The local map `W_{K_u} → W_{E/K}`: conjugate `ι` restricted to `W_{K_u}` by the
representative of `u`, read back in `W_{E/K}`. -/
def localPlaceMap [IsGalois K E]
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
      closurePlaceEmbedding z w (projection c F E (ι g) x) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w x))
    (u : FinitePlacesAbove K z) :
    Weil.Local.localWeilGroup (towerPadicField z u.1) →ₜ* RelativeWeilGroup c K E where
  toMonoidHom :=
    (InductionAlong.rangeInverse (restrictionInclusion c F E K h).toMonoidHom
        (restrictionInclusion_injective c F E K h)).comp
      ((((MulAut.conj (placeRepresentative c K z w u)).toMonoidHom.comp ι.toMonoidHom).comp
        (completionWeilMap z u.1).toMonoidHom).codRestrict _ fun n =>
          (conj_mem_range_restrictionInclusion_iff c K z w h ι.toMonoidHom hι u _
            (cosetEmbedding_placeRepresentative c K z w u) _).mpr ⟨n, rfl⟩)
  continuous_toFun :=
    (InductionAlong.continuous_rangeInverse _
      (isOpenEmbedding_restrictionInclusion c F E K h).isEmbedding).comp
      (((continuous_const.mul (ι.continuous.comp (completionWeilMap z u.1).continuous)).mul
        continuous_const).subtype_mk _)

theorem restrictionInclusion_localPlaceMap [IsGalois K E]
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
      closurePlaceEmbedding z w (projection c F E (ι g) x) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w x))
    (u : FinitePlacesAbove K z) (n : Weil.Local.localWeilGroup (towerPadicField z u.1)) :
    restrictionInclusion c F E K h (localPlaceMap c K z w h ι hι u n) =
      placeRepresentative c K z w u * ι (completionWeilMap z u.1 n) *
        (placeRepresentative c K z w u)⁻¹ :=
  InductionAlong.apply_rangeInverse _ (restrictionInclusion_injective c F E K h) _

end Cosets

end Langlands.ClassField.Global.RelativeWeilGroup
