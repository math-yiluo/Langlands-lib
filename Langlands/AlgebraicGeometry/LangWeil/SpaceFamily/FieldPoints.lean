import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Field points over the integers

Schemes over the terminal scheme `Spec (ULift ℤ)`, lifting of points with values in an
algebraically closed field along morphisms locally of finite type, and descent of points
that are invariant under all automorphisms of a Galois extension.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The terminal base scheme `Spec (ULift ℤ)`. -/
abbrev S0 : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

/-- A scheme as a scheme over the terminal base. -/
abbrev toOver (T : Scheme.{u}) : Over S0.{u} := Over.mk (specULiftZIsTerminal.from T)

/-- A morphism of schemes as a morphism over the terminal base. -/
def toOverHom {T T' : Scheme.{u}} (f : T ⟶ T') : toOver T ⟶ toOver T' :=
  Over.homMk f (specULiftZIsTerminal.hom_ext _ _)

@[simp]
theorem toOverHom_left {T T' : Scheme.{u}} (f : T ⟶ T') : (toOverHom f).left = f := rfl

@[simp]
theorem toOverHom_comp {T T' T'' : Scheme.{u}} (f : T ⟶ T') (g : T' ⟶ T'') :
    toOverHom (f ≫ g) = toOverHom f ≫ toOverHom g := by
  ext; rfl

@[simp]
theorem toOverHom_id (T : Scheme.{u}) : toOverHom (𝟙 T) = 𝟙 (toOver T) := by
  ext; rfl

/-- Every morphism between schemes over the terminal base is a morphism of schemes. -/
theorem eq_toOverHom {T T' : Scheme.{u}} (f : toOver T ⟶ toOver T') :
    f = toOverHom f.left := by
  ext; rfl

/-- Every scheme over the terminal base is isomorphic to its underlying scheme over it. -/
def isoToOver (T : Over S0.{u}) : T ≅ toOver T.left :=
  Over.isoMk (Iso.refl _) (specULiftZIsTerminal.hom_ext _ _)

/-- Lifting a point with values in an algebraically closed field along a morphism locally of
finite type, when the image point lies in the range. -/
theorem exists_lift_of_mem_range {Z T : Scheme.{u}} (f : Z ⟶ T) [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (CommRingCat.of Ω) ⟶ T)
    (hv : v (IsLocalRing.closedPoint Ω) ∈ Set.range f) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z, p ≫ f = v := by
  obtain ⟨z, hz⟩ := hv
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := v) z
    (IsLocalRing.closedPoint Ω) hz
  obtain ⟨x, hx, -⟩ := FieldSchemePoints.exists_closed_specialization (pullback.snd f v) w
  refine ⟨pointOfClosedPoint (pullback.snd f v) x hx ≫ pullback.fst f v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

/-- Lifting a point with values in an algebraically closed field along a surjective morphism
locally of finite type. -/
theorem exists_lift_of_surjective {Z T : Scheme.{u}} (f : Z ⟶ T) [LocallyOfFiniteType f]
    [Surjective f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (CommRingCat.of Ω) ⟶ T) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z, p ≫ f = v :=
  exists_lift_of_mem_range f v (f.surjective _)

/-- Lifting a point with values in an algebraically closed field along a morphism locally of
finite type and locally quasi-finite, through a prescribed point of the source over the image
of the closed point. -/
theorem exists_lift_at_point {Z T : Scheme.{u}} (f : Z ⟶ T) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (CommRingCat.of Ω) ⟶ T) (z : Z) (hz : f z = v (IsLocalRing.closedPoint Ω)) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z, p ≫ f = v ∧ p (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := v) z
    (IsLocalRing.closedPoint Ω) hz
  have hdisc := (pullback.snd f v).isDiscrete_preimage_singleton (IsLocalRing.closedPoint Ω)
  have huniv : (pullback.snd f v) ⁻¹' {IsLocalRing.closedPoint Ω} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hdisc' : _root_.IsDiscrete (Set.univ : Set ↥(pullback f v)) := by
    rw [← huniv]; exact hdisc
  have : DiscreteTopology ↥(pullback f v) := isDiscrete_univ_iff.mp hdisc'
  have hw : IsClosed ({w} : Set ↥(pullback f v)) := isClosed_discrete _
  refine ⟨pointOfClosedPoint (pullback.snd f v) w hw ≫ pullback.fst f v, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  · exact (congrArg (pullback.fst f v) (pointOfClosedPoint_apply _ _ hw _)).trans hw1

/-- Two morphisms from the spectrum of a field into an affine scheme agree when they agree
after an extension of the field. -/
theorem spec_hom_ext {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω] {V : Scheme.{u}}
    [IsAffine V] {v v' : Spec (CommRingCat.of κ) ⟶ V}
    (h : Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ v =
      Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ v') : v = v' := by
  let φ : Γ(V, ⊤) ⟶ CommRingCat.of κ := Spec.preimage (v ≫ V.isoSpec.hom)
  let φ' : Γ(V, ⊤) ⟶ CommRingCat.of κ := Spec.preimage (v' ≫ V.isoSpec.hom)
  have hφ : Spec.map φ = v ≫ V.isoSpec.hom := Spec.map_preimage _
  have hφ' : Spec.map φ' = v' ≫ V.isoSpec.hom := Spec.map_preimage _
  have h2 : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap κ Ω)) =
      Spec.map (φ' ≫ CommRingCat.ofHom (algebraMap κ Ω)) := by
    rw [Spec.map_comp, Spec.map_comp, hφ, hφ', ← Category.assoc, h, Category.assoc]
  have h3 := Spec.map_injective h2
  have h4 : φ = φ' := by
    ext a
    exact (algebraMap κ Ω).injective (congrArg (fun g => g.hom a) h3)
  rw [← cancel_mono V.isoSpec.hom, ← hφ, ← hφ', h4]

/-- A point with values in a Galois extension of a field, invariant under every automorphism,
descends to the field, provided the target scheme is affine. -/
theorem exists_desc_of_aut_invariant {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    [IsGalois κ Ω] {V : Scheme.{u}} [IsAffine V] (w : Spec (CommRingCat.of Ω) ⟶ V)
    (hw : ∀ σ : Ω ≃ₐ[κ] Ω, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ w = w) :
    ∃ v : Spec (CommRingCat.of κ) ⟶ V,
      Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ v = w := by
  let φ : Γ(V, ⊤) ⟶ CommRingCat.of Ω := Spec.preimage (w ≫ V.isoSpec.hom)
  have hφ : Spec.map φ = w ≫ V.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ (σ : Ω ≃ₐ[κ] Ω) (a : Γ(V, ⊤)), σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom (σ : Ω →+* Ω)) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hw σ]
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap κ Ω) := fun a =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (φ a)).2 fun σ => hfix σ a
  choose c hc using hmem
  have hinj := (algebraMap κ Ω).injective
  let φ' : Γ(V, ⊤) →+* κ :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, hc, hc, hc, map_mul])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [map_add, hc, hc, hc, map_add]) }
  have hφ' : CommRingCat.ofHom φ' ≫ CommRingCat.ofHom (algebraMap κ Ω) = φ := by
    ext a
    exact hc a
  refine ⟨Spec.map (CommRingCat.ofHom φ') ≫ V.isoSpec.inv, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hφ', hφ, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The morphism of spectra induced by a field extension. -/
abbrev specMap (κ Ω : Type u) [Field κ] [Field Ω] [Algebra κ Ω] :
    Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of κ) :=
  Spec.map (CommRingCat.ofHom (algebraMap κ Ω))

/-- The spectrum of an extension field maps the unique point to the unique point. -/
theorem specMap_comp_apply {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω] {V : Scheme.{u}}
    (v : Spec (CommRingCat.of κ) ⟶ V) :
    (specMap κ Ω ≫ v) (IsLocalRing.closedPoint Ω) = v (IsLocalRing.closedPoint κ) :=
  congrArg v (Subsingleton.elim _ _)

/-- An automorphism of an extension field commutes with the morphism of spectra. -/
theorem specMap_aut_comp {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω] (σ : Ω ≃ₐ[κ] Ω) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ specMap κ Ω = specMap κ Ω := by
  rw [specMap, ← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

/-- A point with values in a field lifts along a closed immersion when it does so after an
extension of the field: the preimage of the closed immersion is a nonempty closed subscheme
of the spectrum of the field, hence all of it. -/
theorem exists_lift_of_isClosedImmersion {R T : Scheme.{u}} (i : R ⟶ T) [IsClosedImmersion i]
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω] (y : Spec (CommRingCat.of κ) ⟶ T)
    (ρ : Spec (CommRingCat.of Ω) ⟶ R) (hρ : ρ ≫ i = specMap κ Ω ≫ y) :
    ∃ σ : Spec (CommRingCat.of κ) ⟶ R, σ ≫ i = y := by
  have : Nonempty ↥(pullback i y) :=
    ⟨pullback.lift ρ (specMap κ Ω) hρ (IsLocalRing.closedPoint Ω)⟩
  have : Surjective (pullback.snd i y) :=
    ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : IsIso (pullback.snd i y) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd i y) ≫ pullback.fst i y, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- An affine scheme locally of finite type over the integers has finitely many points with
values in a finite field. -/
theorem finite_hom_of_isAffine (V : Scheme.{u}) [IsAffine V]
    [LocallyOfFiniteType (specULiftZIsTerminal.from V)] (κ : Type u) [Field κ] [Finite κ] :
    Finite (Spec (CommRingCat.of κ) ⟶ V) := by
  let : Algebra (ULift.{u} ℤ) κ :=
    ((Int.castRingHom κ).comp ULift.ringEquiv.toRingHom).toAlgebra
  have : IsAffine (toOver V).left := ‹_›
  have : LocallyOfFiniteType (toOver V).hom := ‹_›
  have := FiniteFieldPoints.finite_ringPoint (C := ULift.{u} ℤ) (V := toOver V) κ
  exact Finite.of_surjective
    (fun p : PointTopology.RingPoint (ULift.{u} ℤ) (toOver V) κ => p.left)
    (fun f => ⟨Over.homMk f (specULiftZIsTerminal.hom_ext _ _), rfl⟩)

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
