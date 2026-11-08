import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Langlands.Algebra.PushoutIdealTensor

/-! # Sections of relative spaces over affine bases on preimages of affine opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RelativeAffineSections

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The relative space `Spec S ×_R X` of an `R`-algebra `S`. -/
abbrev relSpace (S : Type u) [CommRing S] [Algebra R S] : Scheme.{u} :=
  (relativeSpace f).obj (affineBase R S)

/-- The projection of the relative space of `S` to `Spec S`. -/
abbrev relProj (S : Type u) [CommRing S] [Algebra R S] :
    relSpace f S ⟶ Spec (CommRingCat.of S) :=
  (relativeProjection f).app (affineBase R S)

/-- The relative-space map of an algebra homomorphism. -/
abbrev relMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (s : S →ₐ[R] S') : relSpace f S' ⟶ relSpace f S :=
  (relativeSpace f).map (affineBaseMap s)

/-- The structure map from `S` to the sections of the relative space over an open. -/
def structureHom (S : Type u) [CommRing S] [Algebra R S] (V : (relSpace f S).Opens) :
    CommRingCat.of S ⟶ Γ(relSpace f S, V) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (relProj f S).appLE ⊤ V le_top

lemma relMap_comp {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S'']
    [Algebra R S] [Algebra R S'] [Algebra R S''] (s : S →ₐ[R] S') (t : S' →ₐ[R] S'') :
    relMap f (t.comp s) = relMap f t ≫ relMap f s := by
  change (relativeSpace f).map (affineBaseMap (t.comp s)) = _
  rw [affineBaseMap_comp, Functor.map_comp]

/-- The base-change square of an algebra homomorphism is Cartesian. -/
lemma isPullback_relMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S'] (s : S →ₐ[R] S') :
    IsPullback (relMap f s) (relProj f S') (relProj f S)
      (Spec.map (CommRingCat.ofHom s.toRingHom)) :=
  relativeProjection_isPullback f (affineBaseMap s)

/-- On the preimage of an affine open, the sections of the base change are the pushout of
the sections and the base change ring. -/
lemma isPushout_sections {S S' : Type u} [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S'] (s : S →ₐ[R] S') (V : (relSpace f S).Opens) (hV : IsAffineOpen V) :
    IsPushout (structureHom f S V) (CommRingCat.ofHom s.toRingHom)
      ((relMap f s).appLE V (relMap f s ⁻¹ᵁ V) le_rfl)
      (structureHom f S' (relMap f s ⁻¹ᵁ V)) := by
  have H := isPullback_relMap f s
  have hUY : relMap f s ⁻¹ᵁ V = relMap f s ⁻¹ᵁ V ⊓ relProj f S' ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := V)
    (by simp) le_top hUY (isAffineOpen_top _) (isAffineOpen_top _) hV
  have h := (isIso_pushoutSection_iff H (by simp) le_top hUY).mp hiso
  refine IsPushout.of_iso h (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of S')) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [structureHom]
  · convert Scheme.ΓSpecIso_naturality (CommRingCat.ofHom s.toRingHom) using 2
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  · simp
  · simp [structureHom]


/-- `isPushout_sections` for any algebra structures whose algebra maps are the given maps. -/
lemma algebraIsPushout_sections {S A : Type u} [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] (s : S →ₐ[R] A) (V : (relSpace f S).Opens) (hV : IsAffineOpen V)
    [Algebra S A] [Algebra S Γ(relSpace f S, V)] [Algebra A Γ(relSpace f A, relMap f s ⁻¹ᵁ V)]
    [Algebra Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V)]
    [Algebra S Γ(relSpace f A, relMap f s ⁻¹ᵁ V)]
    [IsScalarTower S A Γ(relSpace f A, relMap f s ⁻¹ᵁ V)]
    [IsScalarTower S Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V)]
    (h₁ : algebraMap S A = s.toRingHom)
    (h₂ : algebraMap S Γ(relSpace f S, V) = (structureHom f S V).hom)
    (h₃ : algebraMap A Γ(relSpace f A, relMap f s ⁻¹ᵁ V) =
      (structureHom f A (relMap f s ⁻¹ᵁ V)).hom)
    (h₄ : algebraMap Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V) =
      ((relMap f s).appLE V (relMap f s ⁻¹ᵁ V) le_rfl).hom) :
    Algebra.IsPushout S A Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V) := by
  have h := isPushout_sections f s V hV
  have e₁ : CommRingCat.ofHom s.toRingHom = CommRingCat.ofHom (algebraMap S A) := by rw [h₁]
  have e₂ : structureHom f S V = CommRingCat.ofHom (algebraMap S Γ(relSpace f S, V)) := by
    rw [h₂]; rfl
  have e₃ : structureHom f A (relMap f s ⁻¹ᵁ V) =
      CommRingCat.ofHom (algebraMap A Γ(relSpace f A, relMap f s ⁻¹ᵁ V)) := by
    rw [h₃]; rfl
  have e₄ : (relMap f s).appLE V (relMap f s ⁻¹ᵁ V) le_rfl =
      CommRingCat.ofHom (algebraMap Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V)) := by
    rw [h₄]; rfl
  rw [e₁, e₂, e₃, e₄] at h
  exact (CommRingCat.isPushout_iff_isPushout.mp h).symm

/-- Sections of a flat relative space over an affine open are flat over the base ring. -/
lemma flat_structureHom [Flat f] (S : Type u) [CommRing S] [Algebra R S]
    (V : (relSpace f S).Opens) (hV : IsAffineOpen V) : (structureHom f S V).hom.Flat := by
  have : Flat (relProj f S) := by
    change Flat (pullback.fst _ f)
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback (affineBase R S).hom f).flip inferInstance
  have h := HasRingHomProperty.appLE (P := @Flat) (relProj f S) this
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.bijective) h

/-- Reduction along a surjective algebra map kills exactly the extended kernel, on the sections
over every affine open. -/
lemma ker_appLE_eq_map {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (q : A →ₐ[R] B) (hq : Function.Surjective q) (V : (relSpace f A).Opens) (hV : IsAffineOpen V) :
    RingHom.ker ((relMap f q).appLE V (relMap f q ⁻¹ᵁ V) le_rfl).hom =
      Ideal.map (structureHom f A V).hom (RingHom.ker q.toRingHom) := by
  let : Algebra A B := q.toRingHom.toAlgebra
  let : Algebra A Γ(relSpace f A, V) := (structureHom f A V).hom.toAlgebra
  let : Algebra B Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    (structureHom f B (relMap f q ⁻¹ᵁ V)).hom.toAlgebra
  let : Algebra Γ(relSpace f A, V) Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    ((relMap f q).appLE V (relMap f q ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  let : Algebra A Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    ((structureHom f A V) ≫ (relMap f q).appLE V (relMap f q ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  have hsq := (isPushout_sections f q V hV).w
  have : IsScalarTower A B Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ConcreteCategory.congr_hom hsq a
  have : IsScalarTower A Γ(relSpace f A, V) Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := algebraIsPushout_sections f q V hV rfl rfl rfl rfl
  have : Algebra.IsPushout A Γ(relSpace f A, V) B Γ(relSpace f B, relMap f q ⁻¹ᵁ V) :=
    Algebra.IsPushout.symm inferInstance
  exact Langlands.Algebra.PushoutIdealTensor.ker_algebraMap_eq_map (S := A) (S' := B) hq

/-- Two maps into the same relative space have the same preimage of every open if they agree
after composing with a surjection on points. -/
lemma preimage_relMap_eq {S A A' : Type u} [CommRing S] [CommRing A] [CommRing A']
    [Algebra R S] [Algebra R A] [Algebra R A'] (s s' : S →ₐ[R] A) (t : A →ₐ[R] A')
    (hts : t.comp s = t.comp s') (ht : Function.Surjective (relMap f t).base)
    (V : (relSpace f S).Opens) : relMap f s ⁻¹ᵁ V = relMap f s' ⁻¹ᵁ V := by
  ext x
  obtain ⟨y, rfl⟩ := ht x
  have h : relMap f t ≫ relMap f s = relMap f t ≫ relMap f s' := by
    rw [← relMap_comp, ← relMap_comp, hts]
  simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

end Langlands.AlgebraicGeometry.Picard.RelativeAffineSections
