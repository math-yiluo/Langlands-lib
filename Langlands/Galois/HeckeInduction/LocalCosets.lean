import Langlands.Galois.HeckeInduction.RestrictionIndex
import Langlands.Galois.QuadraticFrobeniusPatching.Local
import Langlands.Galois.FrobeniusDensity
import Langlands.Galois.FiniteUnramifiedGaloisRestrictionProof
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-!
# Right cosets of the image of a finite extension and the places above a base place

Let `E/K` be an extension of number fields, `e : K̄ → Ē` a closure embedding and `H` the image of
`Gal(Ē/E)` in `Gal(K̄/K)`. For a finite place `v` of `K` and a place `w` of `E` above `v`,
`placeConj e v w` compares the embeddings `K̄ → Ē → \bar{E_w}` and `K̄ → \bar{K_v} → \bar{E_w}`
of Mathlib's chosen closure embeddings. Conjugation by it carries the image of `Gal(\bar{E_w}/E_w)`
through `K_v` into `H` (`placeConj_relation`), and an element of `Gal(\bar{K_v}/K_v)` comes from
`Gal(\bar{E_w}/E_w)` exactly when its conjugate lies in `H` (`conj_mem_iff_mem_range`).

The coset of `x ∈ Gal(K̄/K)` determines an embedding of `E` into `\bar{K_v}` and hence a prime of
`E` above `v` (`cosetPrime`), unchanged by left multiplication by `H` and right multiplication by
the local Galois group; the coset of `placeConj e v w` gives `w` (`cosetPrime_placeConj`). For a
geometric Frobenius lift `γ` at `v`, no power `γ ^ m` with `0 < m < f(w|v)` comes from
`Gal(\bar{E_w}/E_w)` (`pow_not_mem_range`), while `γ ^ f(w|v)` does when local inertia does
(`pow_inertiaDeg_mem_range`). Local inertia comes from `Gal(\bar{E_w}/E_w)` when the place of the
normal closure of `E` induced by the completion embedding is unramified
(`inertia_fixes_conjugates`, `inertia_mem_range`).
-/

noncomputable section

universe uK uE

namespace Langlands.GaloisRepresentation.HeckeInduction

open Langlands.Global.AdelicFunctoriality
open Langlands.GaloisRepresentation.QuadraticFrobeniusPatching
open NumberField IsLocalRing
open scoped NumberField Valued

/-- Two embeddings of an algebraic closure that agree on the base field differ by an
automorphism of the algebraic closure. -/
theorem exists_closureChange {F Ω : Type*} [Field F] [Field Ω]
    (ι₁ ι₂ : AlgebraicClosure F →+* Ω)
    (h : ∀ x : F, ι₁ (algebraMap F (AlgebraicClosure F) x) =
      ι₂ (algebraMap F (AlgebraicClosure F) x)) :
    ∃ c : Field.absoluteGaloisGroup F, ∀ x, ι₁ (AlgEquiv.toRingEquiv c x) = ι₂ x := by
  let : Algebra F Ω := (ι₁.comp (algebraMap F (AlgebraicClosure F))).toAlgebra
  let ι₁' : AlgebraicClosure F →ₐ[F] Ω := { ι₁ with commutes' := fun _ => rfl }
  let ι₂' : AlgebraicClosure F →ₐ[F] Ω := { ι₂ with commutes' := fun x => (h x).symm }
  let : Algebra (AlgebraicClosure F) Ω := ι₁'.toAlgebra
  exact ⟨ι₂'.restrictNormal' (AlgebraicClosure F),
    fun x => ι₂'.restrictNormal_commutes (AlgebraicClosure F) x⟩

section ClosureMaps

variable {F M : Type*} [Field F] [Field M] (f : F →+* M)

/-- Mathlib's chosen closure embedding over a field homomorphism, as a ring homomorphism. -/
def closureHom : AlgebraicClosure F →+* AlgebraicClosure M := by
  let : Algebra F M := f.toAlgebra
  exact (chosenClosureEmbedding f).toRingHom

theorem closureHom_algebraMap (x : F) :
    closureHom f (algebraMap F (AlgebraicClosure F) x) = algebraMap M (AlgebraicClosure M) (f x) :=
  chosenClosureEmbedding_commutes f x

theorem closureHom_map (g : Field.absoluteGaloisGroup M) (x : AlgebraicClosure F) :
    closureHom f (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map f g) x) =
      AlgEquiv.toRingEquiv g (closureHom f x) :=
  map_commutes f g x

theorem closureHom_bijective (hf : letI : Algebra F M := f.toAlgebra; Algebra.IsAlgebraic F M) :
    Function.Bijective (closureHom f) :=
  chosenClosureEmbedding_bijective f hf

end ClosureMaps

variable {K : Type uK} {E : Type uE} [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]

section Place

variable (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
  (v : Global.FinitePlace K) (w : Global.FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

/-- The embedding `K̄ → Ē → \bar{E_w}` through the given closure embedding. -/
def globalClosureMap : AlgebraicClosure K →+* AlgebraicClosure (Global.FiniteCompletion E w) :=
  (closureHom (NumberField.FinitePlace.embedding w)).comp e.toRingHom

/-- The embedding `K̄ → \bar{K_v} → \bar{E_w}` through the completions. -/
def localClosureMap : AlgebraicClosure K →+* AlgebraicClosure (Global.FiniteCompletion E w) :=
  (closureHom (FiniteExtension.completionMap v w)).comp
    (closureHom (NumberField.FinitePlace.embedding v))

omit [NumberField K] in
theorem globalClosureMap_apply (x : AlgebraicClosure K) :
    globalClosureMap e w x = closureHom (NumberField.FinitePlace.embedding w) (e x) :=
  rfl

theorem localClosureMap_apply (x : AlgebraicClosure K) :
    localClosureMap v w x = closureHom (FiniteExtension.completionMap v w)
      (closureHom (NumberField.FinitePlace.embedding v) x) := rfl

theorem globalClosureMap_algebraMap (x : K) :
    globalClosureMap e w (algebraMap K (AlgebraicClosure K) x) =
      algebraMap (Global.FiniteCompletion E w) (AlgebraicClosure (Global.FiniteCompletion E w))
        (NumberField.FinitePlace.embedding w (algebraMap K E x)) := by
  rw [globalClosureMap_apply, e.commutes, IsScalarTower.algebraMap_apply K E (AlgebraicClosure E),
    closureHom_algebraMap]

theorem localClosureMap_algebraMap (x : K) :
    localClosureMap v w (algebraMap K (AlgebraicClosure K) x) =
      algebraMap (Global.FiniteCompletion E w) (AlgebraicClosure (Global.FiniteCompletion E w))
        (NumberField.FinitePlace.embedding w (algebraMap K E x)) := by
  rw [localClosureMap_apply, closureHom_algebraMap, closureHom_algebraMap]
  congr 1
  exact FiniteExtension.completionMap_coe v w x

/-- The element of the absolute Galois group of `K` comparing the two embeddings into
`\bar{E_w}`. -/
def placeConj : Field.absoluteGaloisGroup K :=
  (exists_closureChange (globalClosureMap e w) (localClosureMap v w) fun x => by
    rw [globalClosureMap_algebraMap, localClosureMap_algebraMap]).choose

theorem placeConj_spec (x : AlgebraicClosure K) :
    globalClosureMap e w (AlgEquiv.toRingEquiv (placeConj e v w) x) = localClosureMap v w x :=
  (exists_closureChange (globalClosureMap e w) (localClosureMap v w) fun x => by
    rw [globalClosureMap_algebraMap, localClosureMap_algebraMap]).choose_spec x

/-- **The comparison square.** The image in `Gal(K̄/K)` of an element `a` of the absolute
Galois group of `E_w`, through `E`, is the conjugate by `placeConj` of its image through `K_v`. -/
theorem placeConj_relation (a : LocalGroup w) :
    restrictionAlongClosure e (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w) a) *
        placeConj e v w =
      placeConj e v w * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)
        (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a) := by
  apply AlgEquiv.ext
  intro x
  apply (globalClosureMap e w).injective
  change globalClosureMap e w (AlgEquiv.toRingEquiv (restrictionAlongClosure e
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w) a))
        (AlgEquiv.toRingEquiv (placeConj e v w) x)) =
    globalClosureMap e w (AlgEquiv.toRingEquiv (placeConj e v w)
      (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)
        (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a)) x))
  rw [placeConj_spec, globalClosureMap_apply, restrictionAlongClosure_commutes, closureHom_map,
    ← globalClosureMap_apply, placeConj_spec, localClosureMap_apply, localClosureMap_apply,
    closureHom_map, closureHom_map]

theorem conj_placeConj_map (a : LocalGroup w) :
    placeConj e v w * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)
        (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a) *
        (placeConj e v w)⁻¹ =
      restrictionAlongClosure e
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w) a) := by
  rw [← placeConj_relation, mul_inv_cancel_right]

theorem completionMap_isAlgebraic :
    letI : Algebra (Global.FiniteCompletion K v) (Global.FiniteCompletion E w) :=
      (FiniteExtension.completionMap v w).toAlgebra
    Algebra.IsAlgebraic (Global.FiniteCompletion K v) (Global.FiniteCompletion E w) := by
  let := FiniteExtension.local_finite v w
  infer_instance

omit [NumberField K] in
theorem absGal_apply_inv_apply (g : Field.absoluteGaloisGroup K) (y : AlgebraicClosure K) :
    AlgEquiv.toRingEquiv g (AlgEquiv.toRingEquiv g⁻¹ y) = y := by
  change AlgEquiv.toRingEquiv (g * g⁻¹) y = y
  rw [mul_inv_cancel]
  rfl

omit [NumberField K] in
theorem absGal_inv_apply_apply (g : Field.absoluteGaloisGroup K) (y : AlgebraicClosure K) :
    AlgEquiv.toRingEquiv g⁻¹ (AlgEquiv.toRingEquiv g y) = y := by
  change AlgEquiv.toRingEquiv (g⁻¹ * g) y = y
  rw [inv_mul_cancel]
  rfl

/-- The image in the closure of `K_v` of the transported copy of an element of `E`, moved
by the inverse of `placeConj`, is the element itself seen in `\bar{E_w}`. -/
theorem localClosureMap_placeConj_inv (t : E) :
    localClosureMap v w (AlgEquiv.toRingEquiv (placeConj e v w)⁻¹ (transportedEmbedding e t)) =
      algebraMap (Global.FiniteCompletion E w) (AlgebraicClosure (Global.FiniteCompletion E w))
        (NumberField.FinitePlace.embedding w t) := by
  rw [← placeConj_spec, absGal_apply_inv_apply, globalClosureMap_apply, e_transportedEmbedding,
    closureHom_algebraMap]

/-- **Fixing the copy of `E`.** If the conjugate of the image of `b` lies in the image of the
absolute Galois group of `E`, then `b` comes from the absolute Galois group of `E_w`. -/
theorem mem_range_of_conj_mem (b : LocalGroup v)
    (hb : placeConj e v w * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b *
        (placeConj e v w)⁻¹ ∈ (restrictionAlongClosure e).toMonoidHom.range) :
    b ∈ (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range := by
  let g := FiniteExtension.completionMap v w
  let eδ := RingEquiv.ofBijective (closureHom g) (closureHom_bijective g
    (completionMap_isAlgebraic v w))
  rw [mem_map_range_iff g eδ (fun _ => rfl)]
  intro y
  let : Algebra (Global.FiniteCompletion K v) (Global.FiniteCompletion E w) := g.toAlgebra
  let f₂ : Global.FiniteCompletion E w →ₐ[Global.FiniteCompletion K v]
      AlgebraicClosure (Global.FiniteCompletion K v) :=
    { toRingHom := eδ.symm.toRingHom.comp
        (algebraMap (Global.FiniteCompletion E w) (AlgebraicClosure (Global.FiniteCompletion E w)))
      commutes' := fun c => by
        change eδ.symm (algebraMap _ _ (g c)) = _
        rw [RingEquiv.symm_apply_eq]
        exact (closureHom_algebraMap g c).symm }
  let bA : AlgebraicClosure (Global.FiniteCompletion K v) ≃ₐ[Global.FiniteCompletion K v]
      AlgebraicClosure (Global.FiniteCompletion K v) := b
  let f₁ := bA.toAlgHom.comp f₂
  have key : ∀ t : E, algebraMap E (Global.FiniteCompletion E w) t ∈ AlgHom.equalizer f₁ f₂ := by
    intro t
    change AlgEquiv.toRingEquiv b (eδ.symm (algebraMap _ _ (algebraMap E _ t))) =
      eδ.symm (algebraMap _ _ (algebraMap E _ t))
    have hz : eδ.symm (algebraMap _ (AlgebraicClosure (Global.FiniteCompletion E w))
        (algebraMap E (Global.FiniteCompletion E w) t)) =
        closureHom (NumberField.FinitePlace.embedding v)
          (AlgEquiv.toRingEquiv (placeConj e v w)⁻¹ (transportedEmbedding e t)) := by
      rw [RingEquiv.symm_apply_eq]
      exact (localClosureMap_placeConj_inv e v w t).symm
    rw [hz, ← closureHom_map]
    congr 1
    have hfix := (mem_range_restrictionAlongClosure_iff e _).mp hb t
    have h2 : AlgEquiv.toRingEquiv (placeConj e v w)
        (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b)
          (AlgEquiv.toRingEquiv (placeConj e v w)⁻¹ (transportedEmbedding e t))) =
        transportedEmbedding e t := hfix
    have h3 := congrArg (AlgEquiv.toRingEquiv (placeConj e v w)⁻¹) h2
    rw [absGal_inv_apply_apply] at h3
    exact h3
  have hS := subalgebra_eq_top_of_algebraMap_mem v w (AlgHom.equalizer f₁ f₂) key
  have hy : y ∈ AlgHom.equalizer f₁ f₂ := hS ▸ Algebra.mem_top
  exact hy

theorem conj_mem_iff_mem_range (b : LocalGroup v) :
    placeConj e v w * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b *
        (placeConj e v w)⁻¹ ∈ (restrictionAlongClosure e).toMonoidHom.range ↔
      b ∈ (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range := by
  refine ⟨mem_range_of_conj_mem e v w b, ?_⟩
  rintro ⟨a, rfl⟩
  exact ⟨_, (conj_placeConj_map e v w a).symm⟩

end Place

section Prime

variable (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) (v : Global.FinitePlace K)

/-- The embedding of `E` into `\bar{K_v}` attached to the right coset of `x`. -/
def cosetEmbedding (x : Field.absoluteGaloisGroup K) :
    E →+* AlgebraicClosure (Global.FiniteCompletion K v) :=
  (closureHom (NumberField.FinitePlace.embedding v)).comp
    ((AlgEquiv.toRingEquiv (x⁻¹ : Field.absoluteGaloisGroup K)).toRingHom.comp
      (transportedEmbedding e).toRingHom)

theorem cosetEmbedding_apply (x : Field.absoluteGaloisGroup K) (t : E) :
    cosetEmbedding e v x t = closureHom (NumberField.FinitePlace.embedding v)
      (AlgEquiv.toRingEquiv (x⁻¹ : Field.absoluteGaloisGroup K) (transportedEmbedding e t)) := rfl

/-- The coset embedding on the integers of `E`, with values in the spectral integers. -/
def cosetIntegers (x : Field.absoluteGaloisGroup K) :
    (𝓞 E) →+* LocalGalois.extensionIntegers (Global.FiniteCompletion K v)
      (AlgebraicClosure (Global.FiniteCompletion K v)) :=
  ((cosetEmbedding e v x).comp (algebraMap (𝓞 E) E)).codRestrict
    (LocalGalois.extensionIntegers (Global.FiniteCompletion K v)
      (AlgebraicClosure (Global.FiniteCompletion K v))).toSubring fun t => by
      apply (LocalGalois.integral_iff_mem_spectralIntegers (Global.FiniteCompletion K v)
        (AlgebraicClosure (Global.FiniteCompletion K v)) _).mp
      exact IsIntegral.map_of_comp_eq (algebraMap ℤ (LocalGalois.baseIntegers
        (Global.FiniteCompletion K v))) (cosetEmbedding e v x) (RingHom.ext_int _ _) t.property

theorem coe_cosetIntegers (x : Field.absoluteGaloisGroup K) (t : 𝓞 E) :
    (cosetIntegers e v x t : AlgebraicClosure (Global.FiniteCompletion K v)) =
      cosetEmbedding e v x t := rfl

/-- The prime of `E` attached to the right coset of `x`: the kernel of the reduction of the
coset embedding. -/
def cosetPrime (x : Field.absoluteGaloisGroup K) : Ideal (𝓞 E) :=
  RingHom.ker ((residue _).comp (cosetIntegers e v x))

theorem mem_cosetPrime_iff (x : Field.absoluteGaloisGroup K) (t : 𝓞 E) :
    t ∈ cosetPrime e v x ↔ cosetIntegers e v x t ∈ maximalIdeal _ := by
  rw [cosetPrime, RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff]

/-- The attached prime does not change under left multiplication by the image of the absolute
Galois group of `E` and right multiplication by the image of the local group. -/
theorem cosetPrime_mul (x h : Field.absoluteGaloisGroup K)
    (hh : h ∈ (restrictionAlongClosure e).toMonoidHom.range) (b : LocalGroup v) :
    cosetPrime e v (h * x * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b) =
      cosetPrime e v x := by
  have hint (t : 𝓞 E) : cosetIntegers e v
      (h * x * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b) t =
      LocalGalois.integerAut _ _ b⁻¹ (cosetIntegers e v x t) := by
    apply Subtype.ext
    rw [coe_cosetIntegers]
    change cosetEmbedding e v _ (t : E) = AlgEquiv.toRingEquiv b⁻¹ (cosetEmbedding e v x (t : E))
    have hfix : AlgEquiv.toRingEquiv (h⁻¹ : Field.absoluteGaloisGroup K)
        (transportedEmbedding e (t : E)) = transportedEmbedding e (t : E) :=
      (mem_range_restrictionAlongClosure_iff e h⁻¹).mp (inv_mem hh) t
    have hinv : ((h * x * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b)⁻¹ :
        Field.absoluteGaloisGroup K) =
        Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b⁻¹ * x⁻¹ * h⁻¹ := by
      rw [map_inv]
      group
    rw [cosetEmbedding_apply, cosetEmbedding_apply, hinv]
    calc closureHom (NumberField.FinitePlace.embedding v) (AlgEquiv.toRingEquiv
          (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b⁻¹ * x⁻¹ * h⁻¹ :
            Field.absoluteGaloisGroup K) (transportedEmbedding e (t : E))) =
        closureHom (NumberField.FinitePlace.embedding v) (AlgEquiv.toRingEquiv
          (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b⁻¹)
            (AlgEquiv.toRingEquiv (x⁻¹ : Field.absoluteGaloisGroup K)
              (AlgEquiv.toRingEquiv (h⁻¹ : Field.absoluteGaloisGroup K)
                (transportedEmbedding e (t : E))))) := rfl
      _ = closureHom (NumberField.FinitePlace.embedding v) (AlgEquiv.toRingEquiv
          (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b⁻¹)
            (AlgEquiv.toRingEquiv (x⁻¹ : Field.absoluteGaloisGroup K)
              (transportedEmbedding e (t : E)))) := by rw [hfix]
      _ = _ := closureHom_map _ b⁻¹ _
  ext t
  rw [mem_cosetPrime_iff, mem_cosetPrime_iff, hint, ← residue_eq_zero_iff, ← residue_eq_zero_iff,
    ← LocalGalois.residueHom_apply, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem cosetPrime_eq_of_coset_eq (x x' : Field.absoluteGaloisGroup K) (b b' : LocalGroup v)
    (h : (x' * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b') *
        (x * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b)⁻¹ ∈
      (restrictionAlongClosure e).toMonoidHom.range) :
    cosetPrime e v x' = cosetPrime e v x := by
  have hx : x' = ((x' * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b') *
      (x * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) b)⁻¹) * x *
      Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) (b * b'⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [hx, cosetPrime_mul e v x _ h]

variable (w : Global.FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

theorem completionMap_norm_le_one_iff (x : Global.FiniteCompletion K v) :
    ‖FiniteExtension.completionMap v w x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simpa only [Valued.toNormedField.norm_le_one_iff,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using
    FiniteExtension.completionMap_mem_integers_iff v w x

/-- **The prime of `placeConj`.** The coset of `placeConj e v w` is attached to `w`. -/
theorem cosetPrime_placeConj : cosetPrime e v (placeConj e v w) = w.asIdeal := by
  let g := FiniteExtension.completionMap v w
  let ε := QuadraticFrobeniusPatching.closureIntegerEquiv g (completionMap_norm_le_one_iff v w)
    (completionMap_isAlgebraic v w)
  ext t
  rw [mem_cosetPrime_iff]
  have hval : ε (cosetIntegers e v (placeConj e v w) t) =
      algebraMap (LocalGalois.baseIntegers (Global.FiniteCompletion E w))
        (LocalGalois.extensionIntegers (Global.FiniteCompletion E w)
          (AlgebraicClosure (Global.FiniteCompletion E w)))
        (Global.CompletionResidue.integersMap E w t) := by
    apply Subtype.ext
    change closureHom g (cosetEmbedding e v (placeConj e v w) (t : E)) = _
    rw [cosetEmbedding_apply]
    exact localClosureMap_placeConj_inv e v w (t : E)
  have hmax : cosetIntegers e v (placeConj e v w) t ∈ maximalIdeal _ ↔
      ε (cosetIntegers e v (placeConj e v w) t) ∈ maximalIdeal _ := by
    rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff ε]
  rw [hmax, hval, ← residue_eq_zero_iff,
    ← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,
    map_eq_zero_iff _ (algebraMap (ResidueField (LocalGalois.baseIntegers
      (Global.FiniteCompletion E w))) _).injective]
  exact Global.CompletionResidue.residueMap_eq_zero_iff E w t

end Prime

section Frobenius

variable (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
  (v : Global.FinitePlace K) (w : Global.FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

theorem residueAction_inv_pow {γ : LocalGroup v} (hγ : IsGeometricFrobeniusLift v γ) (m : ℕ)
    (y : LocalResidueClosure v) :
    localResidueAction v ((γ⁻¹) ^ m) y = y ^ (residueCardinality v ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', map_mul, AlgEquiv.mul_apply, hγ, ih, ← pow_mul, pow_succ]

theorem residueCardinality_eq_pow :
    residueCardinality w = residueCardinality v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  let := w.isPrime
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

theorem one_lt_residueCardinality : 1 < residueCardinality v := by
  have h := Global.CompletionResidue.card_residueField K v
  rw [residueCardinality, ← h]
  exact Finite.one_lt_card

/-- **Cycle lengths are at least the residue degree.** A power `γ ^ m` of a geometric
Frobenius lift with `0 < m < f(w|v)` does not come from the absolute Galois group of `E_w`:
its residue action would fix the residue field of `E_w`, which has `q_v ^ f` elements. -/
theorem pow_not_mem_range {γ : LocalGroup v} (hγ : IsGeometricFrobeniusLift v γ) {m : ℕ}
    (hm0 : 0 < m) (hmf : m < w.asIdeal.inertiaDeg (𝓞 K)) :
    γ ^ m ∉ (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range := by
  rintro ⟨a, ha⟩
  let g := FiniteExtension.completionMap v w
  let ε := closureResidueEquiv g (completionMap_norm_le_one_iff v w) (completionMap_isAlgebraic v w)
  set q := residueCardinality v with hq
  have hact (z : LocalResidueClosure w) : localResidueAction w a⁻¹ z = z ^ (q ^ m) := by
    obtain ⟨y, rfl⟩ := ε.surjective z
    have h := closureResidueEquiv_action g (completionMap_norm_le_one_iff v w)
      (completionMap_isAlgebraic v w) a⁻¹ y
    change ε (localResidueAction v (Field.absoluteGaloisGroup.map g a⁻¹) y) =
      localResidueAction w a⁻¹ (ε y) at h
    rw [← h, map_inv]
    change ε (localResidueAction v ((Field.absoluteGaloisGroup.map g).toMonoidHom a)⁻¹ y) = _
    rw [ha, ← inv_pow, residueAction_inv_pow v hγ m, map_pow]
  have hbase (r : ResidueField (LocalGalois.baseIntegers (Global.FiniteCompletion E w))) :
      r ^ (q ^ m) = r := by
    have h1 : localResidueAction w a⁻¹ (algebraMap _ (LocalResidueClosure w) r) =
        algebraMap _ (LocalResidueClosure w) r := (localResidueAction w a⁻¹).commutes r
    rw [hact, ← map_pow] at h1
    exact (algebraMap _ (LocalResidueClosure w)).injective h1
  have hq1 : 1 < q := one_lt_residueCardinality v
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm0.ne' hq1
  let k := ResidueField (LocalGalois.baseIntegers (Global.FiniteCompletion E w))
  let : Fintype k := Fintype.ofFinite k
  have hP := FiniteField.X_pow_card_sub_X_ne_zero (K' := k) hqm
  have hsub : (Finset.univ : Finset k).val ⊆ (Polynomial.X ^ (q ^ m) - Polynomial.X : Polynomial k).roots := by
    intro r _
    rw [Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hbase, sub_self]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hqm, Finset.card_univ, ← Nat.card_eq_fintype_card,
    Global.CompletionResidue.card_residueField E w] at hcard
  change residueCardinality w ≤ q ^ m at hcard
  rw [residueCardinality_eq_pow v w, ← hq, Nat.pow_le_pow_iff_right hq1] at hcard
  omega

/-- If local inertia comes from the absolute Galois group of `E_w`, so does the residue-degree
power of every geometric Frobenius lift. -/
theorem pow_inertiaDeg_mem_range
    (hI : ∀ i ∈ localInertia v,
      i ∈ (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range)
    {γ : LocalGroup v} (hγ : IsGeometricFrobeniusLift v γ) :
    γ ^ w.asIdeal.inertiaDeg (𝓞 K) ∈
      (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range := by
  obtain ⟨a, ha⟩ := exists_geometricFrobeniusLift w
  have hres := residueAction_map_eq_pow (FiniteExtension.completionMap v w)
    (completionMap_norm_le_one_iff v w) (completionMap_isAlgebraic v w) _
    (residueCardinality_eq_pow v w) ha hγ
  set f := w.asIdeal.inertiaDeg (𝓞 K)
  have hi : (γ ^ f)⁻¹ * Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a ∈
      localInertia v := by
    change localResidueAction v _ = 1
    rw [map_mul, map_inv, hres, inv_mul_cancel]
  have heq : γ ^ f = Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a *
      ((γ ^ f)⁻¹ * Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a)⁻¹ := by
    group
  rw [heq]
  exact mul_mem ⟨a, rfl⟩ (inv_mem (hI _ hi))

/-- If the image of local inertia fixes every conjugate of the transported copy of `E`, local
inertia comes from the absolute Galois group of `E_w`. -/
theorem inertia_mem_range
    (hfix : ∀ i ∈ localInertia v, ∀ (y : Field.absoluteGaloisGroup K) (t : E),
      AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i)
        (AlgEquiv.toRingEquiv y (transportedEmbedding e t)) =
          AlgEquiv.toRingEquiv y (transportedEmbedding e t))
    (i : LocalGroup v) (hi : i ∈ localInertia v) :
    i ∈ (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w)).toMonoidHom.range := by
  apply mem_range_of_conj_mem e v w
  rw [mem_range_restrictionAlongClosure_iff]
  intro t
  change AlgEquiv.toRingEquiv (placeConj e v w) (AlgEquiv.toRingEquiv
    (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i)
      (AlgEquiv.toRingEquiv ((placeConj e v w)⁻¹ : Field.absoluteGaloisGroup K)
        (transportedEmbedding e t))) = _
  rw [hfix i hi _ t]
  exact absGal_apply_inv_apply _ _

end Frobenius

section NormalClosure

/-- The induced prime of a finite subextension, as a finite place. -/
def inducedPlace (v : Global.FinitePlace K) (M : IntermediateField K (AlgebraicClosure K)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 M) where
  asIdeal := inducedPrime v M
  isPrime := inducedPrime_isPrime v M
  ne_bot := by
    intro h
    have hl := (inducedPrime_liesOver v M).over
    rw [h, Ideal.under_bot] at hl
    exact v.ne_bot hl

theorem inducedPlace_liesOver (v : Global.FinitePlace K)
    (M : IntermediateField K (AlgebraicClosure K)) :
    (inducedPlace v M).asIdeal.LiesOver v.asIdeal :=
  inducedPrime_liesOver v M

/-- **Inertia is trivial on an unramified normal subextension.** If the induced prime of a
finite normal subextension `M` is unramified over `K`, the image of local inertia fixes `M`
pointwise: a geometric Frobenius lift times an inertia element is again one, and the arithmetic
Frobenius at an unramified prime is unique. -/
theorem inertia_fixes_of_unramified (M : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K M] [Normal K M] (v : Global.FinitePlace K)
    (hunr : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v M).asIdeal) {i : LocalGroup v}
    (hi : i ∈ localInertia v) (z : AlgebraicClosure K) (hz : z ∈ M) :
    AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i) z =
      z := by
  let : NumberField M := NumberField.of_module_finite K M
  obtain ⟨γ, hγ⟩ := exists_geometricFrobeniusLift v
  have h := ClassFieldTheory.Global.Artin.eq_of_isArithFrobAt_mapAlgHom (inducedPlace v M) hunr
    (arithmeticFrobeniusAt_inducedPrime v M (isGeometricFrobeniusLift_mul_of_mem_localInertia hγ hi))
    (arithmeticFrobeniusAt_inducedPrime v M hγ)
  let φ := (AlgEquiv.restrictNormalHom M).comp (absoluteToGal K)
  have h1 : φ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) (γ * i))⁻¹ =
      φ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) γ)⁻¹ := h
  rw [map_mul, mul_inv_rev, map_mul, mul_eq_right, map_inv, inv_eq_one] at h1
  have h : AlgEquiv.restrictNormalHom M
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i) = 1 := h1
  have h2 := AlgEquiv.restrictNormalHom_apply M
    (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i) ⟨z, hz⟩
  rw [h] at h2
  exact h2.symm

variable (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)

/-- The normal closure of `E` inside the algebraic closure of `K`. -/
abbrev normalClosureField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.normalClosure K E (AlgebraicClosure K)

/-- At a place whose induced prime in the normal closure is unramified, the image of local
inertia fixes every conjugate of the transported copy of `E`. -/
theorem inertia_fixes_conjugates (v : Global.FinitePlace K)
    (hunr : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v (normalClosureField (E := E))).asIdeal)
    (i : LocalGroup v) (hi : i ∈ localInertia v) (y : Field.absoluteGaloisGroup K) (t : E) :
    AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i)
        (AlgEquiv.toRingEquiv y (transportedEmbedding e t)) =
      AlgEquiv.toRingEquiv y (transportedEmbedding e t) := by
  apply inertia_fixes_of_unramified _ v hunr hi
  let yA : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := y
  exact (yA.toAlgHom.comp (transportedEmbedding e)).fieldRange_le_normalClosure ⟨t, rfl⟩

end NormalClosure

end Langlands.GaloisRepresentation.HeckeInduction
