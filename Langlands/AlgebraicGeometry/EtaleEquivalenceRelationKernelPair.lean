import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientProof
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The kernel pair relation of an étale morphism and cartesian morphisms to it

For an étale morphism `q : U ⟶ M` the kernel pair `U ×_M U ⇉ U` is an étale equivalence
relation. If `M` is affine and `q` is surjective, then `q` itself is an affine quotient.
An étale equivalence relation `E` admits a cartesian morphism to this kernel pair as soon as
there is `f : E.U ⟶ U` for which `E.R` is the fibre product of `t ≫ f` and `s ≫ f ≫ q`
over `M`. For `E.U` affine, the published pullback statement for affine quotients
(`etaleEquivalenceRelationCartesianAffineQuotient`) then gives `E` an affine quotient.
The last part gives ring-level forms of this criterion.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

namespace EtaleEquivalenceRelation

/-- The kernel pair `U ×_M U ⇉ U` of an étale morphism `q : U ⟶ M`, with `t` the first and
`s` the second projection. -/
noncomputable def kernelPair {U M : Scheme.{u}} (q : U ⟶ M) [Etale q] :
    EtaleEquivalenceRelation.{u} where
  U := U
  R := pullback q q
  t := pullback.fst q q
  s := pullback.snd q q
  mono_lift := by
    constructor
    intro Z r r' h
    apply pullback.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using congrArg (fun k => k ≫ prod.fst) h
    · simpa only [Category.assoc, prod.lift_snd] using congrArg (fun k => k ≫ prod.snd) h
  refl T a := ⟨pullback.lift a a rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  symm T r := ⟨pullback.lift (r ≫ pullback.snd q q) (r ≫ pullback.fst q q)
      (by simp only [Category.assoc, pullback.condition]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  trans T r r' h := ⟨pullback.lift (r ≫ pullback.fst q q) (r' ≫ pullback.snd q q)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc,
        pullback.condition, Category.assoc]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  etale_t := inferInstance
  etale_s := inferInstance

variable {U M : Scheme.{u}} (q : U ⟶ M) [Etale q]

@[simp]
lemma kernelPair_U : (kernelPair q).U = U := rfl

@[simp]
lemma kernelPair_R : (kernelPair q).R = pullback q q := rfl

@[simp]
lemma kernelPair_t : (kernelPair q).t = pullback.fst q q := rfl

@[simp]
lemma kernelPair_s : (kernelPair q).s = pullback.snd q q := rfl

/-- A surjective étale morphism to an affine scheme is an affine quotient of its kernel
pair. -/
theorem kernelPair_hasAffineQuotient [Surjective q] [IsAffine M] :
    (kernelPair q).HasAffineQuotient := by
  have hfl : Flat q := inferInstance
  have hlfp : LocallyOfFinitePresentation q := inferInstance
  exact ⟨M, q, inferInstance, IsPullback.of_hasPullback q q, hfl, hlfp, ‹Surjective q›⟩

/-- Let `E` be an étale equivalence relation and `f : E.U ⟶ U` a morphism such that the square
formed by `E.t ≫ f`, `E.s`, `q` and `f ≫ q` is a pullback. Then `f`, together with the induced
map `E.R ⟶ U ×_M U`, is a cartesian morphism from `E` to the kernel pair of `q`. -/
theorem isCartesianHom_kernelPair (E : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ U)
    (h : IsPullback (E.t ≫ f) E.s q (f ≫ q)) :
    IsCartesianHom E (kernelPair q) f
      (pullback.lift (E.t ≫ f) (E.s ≫ f) (by rw [h.w, Category.assoc])) := by
  refine ⟨pullback.lift_fst _ _ _, ?_⟩
  have h₂ : IsPullback (pullback.fst q q) (pullback.snd q q) q q := IsPullback.of_hasPullback q q
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) h₂
  convert h using 1
  all_goals first | rfl | exact pullback.lift_fst _ _ _

/-- The cartesian criterion: if `E.U` and `U` are affine, `q` is surjective onto an affine
scheme and `E.R` is the fibre product of `E.t ≫ f` and `E.s` over `M` for some
`f : E.U ⟶ U`, then `E` has an affine quotient. -/
theorem hasAffineQuotient_of_isPullback_kernelPair [Surjective q] [IsAffine M] [IsAffine U]
    (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] (f : E.U ⟶ U)
    (h : IsPullback (E.t ≫ f) E.s q (f ≫ q)) : E.HasAffineQuotient :=
  etaleEquivalenceRelationCartesianAffineQuotient E (kernelPair q) f _
    (isCartesianHom_kernelPair q E f h) inferInstance (by simpa using ‹IsAffine U›)
    (kernelPair_hasAffineQuotient q)

end EtaleEquivalenceRelation

/-! ### Ring-level forms -/

namespace CommRingCat

variable {R S A P : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing P]
  [Algebra R S] [Algebra R A]

/-- For ring maps `i : S → P` and `j : A → P` that agree on `R`, the induced ring map
`S ⊗[R] A → P`, `x ⊗ y ↦ i x * j y`. -/
noncomputable def tensorLift (i : S →+* P) (j : A →+* P)
    (hw : i.comp (algebraMap R S) = j.comp (algebraMap R A)) : S ⊗[R] A →+* P :=
  ((CommRingCat.isPushout_tensorProduct R S A).desc (CommRingCat.ofHom i)
    (CommRingCat.ofHom j) (by ext x; exact congrArg (fun k : R →+* P => k x) hw)).hom

@[simp]
lemma tensorLift_tmul (i : S →+* P) (j : A →+* P)
    (hw : i.comp (algebraMap R S) = j.comp (algebraMap R A)) (x : S) (y : A) :
    tensorLift i j hw (x ⊗ₜ y) = i x * j y := by
  have hl := congrArg (fun k => k.hom x) ((CommRingCat.isPushout_tensorProduct R S A).inl_desc
    (CommRingCat.ofHom i) (CommRingCat.ofHom j)
    (by ext x; exact congrArg (fun k : R →+* P => k x) hw))
  have hr := congrArg (fun k => k.hom y) ((CommRingCat.isPushout_tensorProduct R S A).inr_desc
    (CommRingCat.ofHom i) (CommRingCat.ofHom j)
    (by ext x; exact congrArg (fun k : R →+* P => k x) hw))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hl hr
  rw [show x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] y) by simp]
  rw [map_mul]
  exact congrArg₂ (· * ·) hl hr

/-- Let `i : S → P` and `j : A → P` be ring maps and `F : S ⊗[R] A → P` a bijective ring map
with `F (x ⊗ y) = i x * j y`. Then the square of `R → S`, `R → A`, `i` and `j` is a pushout of
commutative rings. -/
theorem isPushout_of_bijective (i : S →+* P) (j : A →+* P) (F : S ⊗[R] A →+* P)
    (hF : ∀ x y, F (x ⊗ₜ y) = i x * j y) (hbij : Function.Bijective F) :
    IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom i) (CommRingCat.ofHom j) :=
  (CommRingCat.isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (RingEquiv.ofBijective F hbij).toCommRingCatIso (by simp) (by simp)
    (by ext x; simp [hF]) (by ext y; simp [hF])

end CommRingCat

namespace EtaleEquivalenceRelation

variable {A₁ B₁ : Type u} [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]

/-- The spectrum map of an étale algebra `A₁ → B₁`. -/
noncomputable abbrev specAlgebraMap (A₁ B₁ : Type u) [CommRing A₁] [CommRing B₁]
    [Algebra A₁ B₁] : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of A₁) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₁ B₁))

instance [Algebra.Etale A₁ B₁] : Etale (specAlgebraMap A₁ B₁) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)

instance [Module.FaithfullyFlat A₁ B₁] : Surjective (specAlgebraMap A₁ B₁) :=
  ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A₁ B₁))).mpr
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)).2

/-- The ring-level cartesian criterion. Let `A₁ → B₁` be étale and faithfully flat, let `E` be
an étale equivalence relation identified through isomorphisms `eU` and `eR` with
`Spec C ⇉ Spec D`, where `t` is induced by a ring map `τ : D → C` and `s` by `algebraMap D C`,
and let `φ : B₁ → D` be an `A₁`-algebra map. If a bijective ring map
`F : B₁ ⊗[A₁] D → C` satisfies `F (b ⊗ d) = τ (φ b) * d`, then `E` has a cartesian morphism to
the kernel pair of `Spec B₁ → Spec A₁`, hence an affine quotient. -/
theorem hasAffineQuotient_of_bijective [Algebra.Etale A₁ B₁] [Module.FaithfullyFlat A₁ B₁]
    {D C : Type u} [CommRing D] [CommRing C] [Algebra A₁ D] [Algebra D C] (τ : D →+* C)
    (E : EtaleEquivalenceRelation.{u}) (eU : E.U ≅ Spec (CommRingCat.of D))
    (eR : E.R ≅ Spec (CommRingCat.of C))
    (ht : E.t ≫ eU.hom = eR.hom ≫ Spec.map (CommRingCat.ofHom τ))
    (hs : E.s ≫ eU.hom = eR.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D C)))
    (φ : B₁ →ₐ[A₁] D) (F : B₁ ⊗[A₁] D →+* C)
    (hF : ∀ b d, F (b ⊗ₜ d) = τ (φ b) * algebraMap D C d) (hbij : Function.Bijective F) :
    E.HasAffineQuotient := by
  have hpo := CommRingCat.isPushout_of_bijective (τ.comp (φ : B₁ →+* D)) (algebraMap D C) F
    hF hbij
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have : IsAffine E.U := IsAffine.of_isIso eU.hom
  refine hasAffineQuotient_of_isPullback_kernelPair (specAlgebraMap A₁ B₁) E
    (eU.hom ≫ Spec.map (CommRingCat.ofHom (φ : B₁ →+* D))) ?_
  refine hpb.of_iso eR.symm (Iso.refl _) eU.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% ht, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← hs, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      Iso.inv_hom_id_assoc]
    dsimp only [specAlgebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
