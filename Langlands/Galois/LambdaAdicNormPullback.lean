import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Galois.AlgebraicHeckeLambdaAdicRealizationStatement
import Langlands.Galois.ClosureRestrictionGalois
import Langlands.Galois.PureWeightParity
import Langlands.Galois.QuadraticFrobeniusPatching.Local
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTransport

/-!
# Restriction of a compatible rank-one realization to a finite extension

Let `ψ` be a compatible family of `λ`-adic characters realizing a Hecke character `χ` of a
number field `F`, and let `F'/F` be a finite extension. Composing `ψ` with the restriction of
absolute Galois groups along a closure embedding realizes the norm pullback `χ ∘ N_{F'/F}`.
At a place `w` of `F'` above a good place `v` of `F`, unramified in `F'/F`, the local Galois
group at `w` maps into the local Galois group at `v` up to conjugation, inertia into inertia
and a geometric Frobenius lift to the `f(w|v)`-th power of one modulo inertia. On the Hecke
side the norm pullback sends a uniformizer of `F'_w` to `χ_v(ϖ_v) ^ f(w|v)`.
-/

noncomputable section

universe u uL

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality IsDedekindDomain
open scoped NumberField Valued

section Local

variable {F F' : Type u} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem residueCardinality_eq_pow_of_liesOver (v : FinitePlace F) (w : FinitePlace F')
    [w.asIdeal.LiesOver v.asIdeal] :
    residueCardinality w = residueCardinality v ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  let := w.isPrime
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

theorem completionMap_norm_le_one_iff (v : FinitePlace F) (w : FinitePlace F')
    [w.asIdeal.LiesOver v.asIdeal] (x : FiniteCompletion F v) :
    ‖FiniteExtension.completionMap v w x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simpa only [Valued.toNormedField.norm_le_one_iff,
    HeightOneSpectrum.mem_adicCompletionIntegers] using
    FiniteExtension.completionMap_mem_integers_iff v w x

theorem completionMap_isAlgebraic (v : FinitePlace F) (w : FinitePlace F')
    [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (FiniteCompletion F v) (FiniteCompletion F' w) :=
      (FiniteExtension.completionMap v w).toAlgebra
    Algebra.IsAlgebraic (FiniteCompletion F v) (FiniteCompletion F' w) := by
  let := FiniteExtension.local_finite v w
  infer_instance

end Local

section Square

variable {F F' B C : Type*} [Field F] [Field F'] [Field B] [Field C] [Algebra F F']

/-- For a commuting square of field embeddings `F → F' → C` and `F → B → C`, the two
restrictions from the absolute group of `C` to that of `F`, through `F'` along `θ` or through
`B`, are conjugate. Hence a character into a commutative group takes the same value on both
images. -/
theorem restriction_square_eq {M : Type*} [CommGroup M]
    (ψ : Field.absoluteGaloisGroup F →* M)
    (θ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (ev : F →+* B) (ew : F' →+* C) (g : B →+* C)
    (hsq : ∀ x : F, g (ev x) = ew (algebraMap F F' x))
    (a : Field.absoluteGaloisGroup C) :
    ψ (restrictionAlongClosure θ (Field.absoluteGaloisGroup.map ew a)) =
      ψ (Field.absoluteGaloisGroup.map ev (Field.absoluteGaloisGroup.map g a)) := by
  let : Algebra F C := (ew.comp (algebraMap F F')).toAlgebra
  let : Algebra F' C := ew.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra F B := ev.toAlgebra
  let κ₁ : AlgebraicClosure F →ₐ[F] AlgebraicClosure C :=
    { toRingHom := (chosenClosureEmbedding ew).toRingHom.comp θ.toRingHom
      commutes' := fun x => by
        change chosenClosureEmbedding ew (θ (algebraMap F (AlgebraicClosure F) x)) =
          algebraMap C (AlgebraicClosure C) (algebraMap F C x)
        rw [θ.commutes, IsScalarTower.algebraMap_apply F F' (AlgebraicClosure F'),
          QuadraticFrobeniusPatching.chosenClosureEmbedding_commutes]
        rfl }
  let κ₂ : AlgebraicClosure F →ₐ[F] AlgebraicClosure C :=
    { toRingHom := (chosenClosureEmbedding g).toRingHom.comp (chosenClosureEmbedding ev).toRingHom
      commutes' := fun x => by
        change chosenClosureEmbedding g (chosenClosureEmbedding ev
            (algebraMap F (AlgebraicClosure F) x)) =
          algebraMap C (AlgebraicClosure C) (algebraMap F C x)
        rw [QuadraticFrobeniusPatching.chosenClosureEmbedding_commutes,
          QuadraticFrobeniusPatching.chosenClosureEmbedding_commutes, hsq]
        rfl }
  have h₁ : restrictionAlongClosure θ (Field.absoluteGaloisGroup.map ew a) =
      restrictionAlongClosure κ₁ a := by
    apply eq_restrictionAlongClosure
    intro x
    change chosenClosureEmbedding ew (θ (AlgEquiv.toRingEquiv
        (restrictionAlongClosure θ (Field.absoluteGaloisGroup.map ew a)) x)) =
      AlgEquiv.toRingEquiv a (chosenClosureEmbedding ew (θ x))
    rw [restrictionAlongClosure_commutes]
    exact QuadraticFrobeniusPatching.map_commutes ew a (θ x)
  have h₂ : Field.absoluteGaloisGroup.map ev (Field.absoluteGaloisGroup.map g a) =
      restrictionAlongClosure κ₂ a := by
    apply eq_restrictionAlongClosure
    intro x
    change chosenClosureEmbedding g (chosenClosureEmbedding ev (AlgEquiv.toRingEquiv
        (Field.absoluteGaloisGroup.map ev (Field.absoluteGaloisGroup.map g a)) x)) =
      AlgEquiv.toRingEquiv a (chosenClosureEmbedding g (chosenClosureEmbedding ev x))
    rw [QuadraticFrobeniusPatching.map_commutes, QuadraticFrobeniusPatching.map_commutes]
  rw [h₁, h₂]
  have hc := closureChange_intertwines κ₁ κ₂ a
  have hc' : restrictionAlongClosure κ₁ a =
      closureChange κ₁ κ₂ * restrictionAlongClosure κ₂ a * (closureChange κ₁ κ₂)⁻¹ := by
    rw [hc, mul_inv_cancel_right]
  rw [hc', map_mul, map_mul, map_inv, mul_comm (ψ (closureChange κ₁ κ₂)), mul_assoc,
    mul_inv_cancel, mul_one]

end Square

section LocalRestriction

variable {F F' : Type u} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

/-- The local form of `restriction_square_eq` at places `w | v`. -/
theorem restriction_localGroup_eq {M : Type*} [CommGroup M]
    (ψ : Field.absoluteGaloisGroup F →* M)
    (θ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (v : FinitePlace F) (w : FinitePlace F') [w.asIdeal.LiesOver v.asIdeal]
    (a : LocalGroup w) :
    ψ (restrictionAlongClosure θ
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w) a)) =
      ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)
        (Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w) a)) :=
  restriction_square_eq ψ θ _ _ _ (fun x => FiniteExtension.completionMap_coe v w x) a

end LocalRestriction

section Realization

variable {F F' : Type u} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']
variable {L : Type uL} [Field L] [NumberField L]

/-- Composition with the restriction along a closure embedding realizes the norm pullback. -/
theorem isCompatibleLambdaAdicRealization_normComp (ι : L →+* ℂ) (χ : HeckeCharacter F)
    (ψ : (lam : FinitePlace L) → LambdaAdicCharacter F L lam)
    (h : IsCompatibleLambdaAdicRealization ι χ ψ)
    (θ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') :
    IsCompatibleLambdaAdicRealization ι (HeckeCharacter.normComp (L := F') χ)
      (fun lam => (ψ lam).comp (restrictionAlongClosure θ)) := by
  obtain ⟨S, hS⟩ := h
  have hgood : ∀ᶠ w : FinitePlace F' in Filter.cofinite,
      w.under (𝓞 F) ∉ S ∧ w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    have h1 : ∀ᶠ v : FinitePlace F in Filter.cofinite, v ∉ S :=
      S.finite_toSet.eventually_cofinite_notMem
    have h2 := eventually_ramificationIdx_eq_one (K := F) (L := F')
    filter_upwards [Automorphic.Unramified.WeakInduction.tendsto_under_cofinite.eventually h1,
      Automorphic.Unramified.WeakInduction.tendsto_under_cofinite.eventually h2] with w hw1 hw2
    exact ⟨hw1, hw2 w (Ideal.LiesOver.mk rfl)⟩
  refine ⟨(Filter.eventually_cofinite.mp hgood).toFinset, fun w hw => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw
  obtain ⟨hvS, he⟩ := hw
  set v := w.under (𝓞 F) with hv
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.mk rfl
  obtain ⟨hχv, a, ⟨ϖ, hϖ, hχϖ⟩, hψ⟩ := hS v hvS
  set f := w.asIdeal.inertiaDeg (𝓞 F)
  refine ⟨HeckeCharacter.normComp_isUnramifiedAt χ v hχv ⟨w, this⟩, a ^ f, ?_, ?_⟩
  · obtain ⟨π, hπ⟩ := Automorphic.Unramified.WeakInduction.exists_uniformizer w
    refine ⟨π, hπ, ?_⟩
    rw [HeckeCharacter.normComp_finiteComponent_uniformizer χ v ⟨w, this⟩ he hχv π hπ ϖ hϖ,
      Units.val_pow_eq_pow_val, hχϖ, map_pow]
  · intro lam hlam
    rw [residueCharacteristic_eq_of_liesOver v w] at hlam
    obtain ⟨hψu, hψF⟩ := hψ lam hlam
    let g := FiniteExtension.completionMap v w
    have hg := completionMap_norm_le_one_iff v w
    have hAlg := completionMap_isAlgebraic v w
    have hloc (b : LocalGroup w) :
        LambdaAdicCharacter.atFinitePlace ((ψ lam).comp (restrictionAlongClosure θ)) w b =
          (ψ lam).atFinitePlace v (Field.absoluteGaloisGroup.map g b) :=
      restriction_localGroup_eq (ψ lam).toMonoidHom θ v w b
    refine ⟨fun i => ?_, fun b hb => ?_⟩
    · rw [hloc]
      exact hψu ⟨_, (QuadraticFrobeniusPatching.map_mem_inertia_iff g hg hAlg i.val).2 i.prop⟩
    · rw [hloc]
      let c := geometricFrobeniusLift v
      have hc := geometricFrobeniusLift_spec v
      have hres := QuadraticFrobeniusPatching.residueAction_map_eq_pow g hg hAlg f
        (residueCardinality_eq_pow_of_liesOver v w) hb hc
      have hker : Field.absoluteGaloisGroup.map g b * (c ^ f)⁻¹ ∈ localInertia v := by
        change localResidueAction v _ = 1
        rw [map_mul, map_inv, hres, mul_inv_cancel]
      have hone := hψu ⟨_, hker⟩
      rw [map_mul, map_inv, mul_inv_eq_one] at hone
      rw [hone, map_pow, Units.val_pow_eq_pow_val, hψF c hc, map_pow]

end Realization

section RingHomRealization

variable {F F' : Type u} [Field F] [NumberField F] [Field F'] [NumberField F']
variable {L : Type uL} [Field L] [NumberField L]

/-- The form of `isCompatibleLambdaAdicRealization_normComp` for the algebra structure induced
by a field homomorphism. -/
theorem isCompatibleLambdaAdicRealization_normComp_hom (f : F →+* F') (ι : L →+* ℂ)
    (χ : HeckeCharacter F) (ψ : (lam : FinitePlace L) → LambdaAdicCharacter F L lam)
    (h : IsCompatibleLambdaAdicRealization ι χ ψ) (θ : ClosureEmbedding f) :
    letI : Algebra F F' := f.toAlgebra
    IsCompatibleLambdaAdicRealization ι (HeckeCharacter.normComp (L := F') χ)
      (fun lam => (ψ lam).comp (restrictionAlongClosureHom f θ)) := by
  letI : Algebra F F' := f.toAlgebra
  exact isCompatibleLambdaAdicRealization_normComp ι χ ψ h θ

/-- The idele-class norm for two algebra structures related by an automorphism of the top
field. -/
theorem ideleClassNorm_algebra_twist (A₁ A₂ : Algebra F F') (σ : F' ≃+* F')
    (hσ : ∀ x, σ (@algebraMap F F' _ _ A₁ x) = @algebraMap F F' _ _ A₂ x)
    (y : IdeleClasses F') :
    @ideleClassNorm F F' _ _ _ _ A₂ (ideleClassEquiv σ y) =
      @ideleClassNorm F F' _ _ _ _ A₁ y := by
  have h := @ideleClassNorm_equiv F F' F F' _ _ _ _ A₁ _ _ _ _ A₂ (RingEquiv.refl F) σ hσ y
  rw [h, ideleClassEquiv_refl]
  rfl

end RingHomRealization

end Langlands.GaloisRepresentation
