import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Over

/-! # Morphisms of schemes from natural maps on affine points

A morphism of schemes `X ⟶ Y` is determined by its composites with all morphisms
`Spec A ⟶ X`, and every family of maps on affine points that is natural in the ring `A`
comes from a unique morphism `X ⟶ Y`. The same holds over a base `Spec R`, with affine points
taken over `Spec R` and indexed by `R`-algebras.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.AffinePoints

/-- Two morphisms of schemes agreeing on every affine point are equal. -/
theorem hom_ext {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ X), t ≫ f = t ≫ g) :
    f = g :=
  Scheme.Cover.hom_ext X.affineCover f g fun i => h _ (X.affineCover.f i)

/-- Naturality of a family of maps on affine points along ring maps implies naturality along
every morphism of affine schemes. -/
theorem comp_eq_of_natural {X Y : Scheme.{u}}
    (F : ∀ A : CommRingCat.{u}, (Spec A ⟶ X) → (Spec A ⟶ Y))
    (hF : ∀ (A B : CommRingCat.{u}) (φ : A ⟶ B) (t : Spec A ⟶ X),
      F B (Spec.map φ ≫ t) = Spec.map φ ≫ F A t)
    {A B : CommRingCat.{u}} (s : Spec B ⟶ Spec A) (t : Spec A ⟶ X) :
    s ≫ F A t = F B (s ≫ t) := by
  rw [← Spec.map_preimage s, hF]

/-- A family of maps on affine points that is natural in the ring comes from a morphism of
schemes. -/
theorem exists_hom {X Y : Scheme.{u}}
    (F : ∀ A : CommRingCat.{u}, (Spec A ⟶ X) → (Spec A ⟶ Y))
    (hF : ∀ (A B : CommRingCat.{u}) (φ : A ⟶ B) (t : Spec A ⟶ X),
      F B (Spec.map φ ≫ t) = Spec.map φ ≫ F A t) :
    ∃ f : X ⟶ Y, ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ X), t ≫ f = F A t := by
  let g : ∀ i, X.affineCover.X i ⟶ Y := fun i => F _ (X.affineCover.f i)
  have hg : ∀ i j, pullback.fst (X.affineCover.f i) (X.affineCover.f j) ≫ g i =
      pullback.snd _ _ ≫ g j := by
    intro i j
    refine hom_ext fun A t => ?_
    rw [← Category.assoc, ← Category.assoc]
    have e : (t ≫ pullback.fst (X.affineCover.f i) (X.affineCover.f j)) ≫ X.affineCover.f i =
        (t ≫ pullback.snd _ _) ≫ X.affineCover.f j := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    exact (comp_eq_of_natural F hF _ _).trans
      ((congrArg (F A) e).trans (comp_eq_of_natural F hF _ _).symm)
  refine ⟨X.affineCover.glueMorphisms g hg, fun A t => ?_⟩
  refine Scheme.Cover.hom_ext (X.affineCover.pullback₁ t) _ _
    fun (i : X.affineCover.I₀) => hom_ext fun B s => ?_
  have e : (X.affineCover.pullback₁ t).f i ≫ t =
      pullback.snd t (X.affineCover.f i) ≫ X.affineCover.f i := pullback.condition
  have e' : (X.affineCover.pullback₁ t).f i ≫ t ≫ X.affineCover.glueMorphisms g hg =
      pullback.snd t (X.affineCover.f i) ≫ g i :=
    ((reassoc_of% e) _).trans
      (congrArg (pullback.snd t (X.affineCover.f i) ≫ ·) (X.affineCover.ι_glueMorphisms g hg i))
  have e'' : (s ≫ pullback.snd t (X.affineCover.f i)) ≫ X.affineCover.f i =
      (s ≫ (X.affineCover.pullback₁ t).f i) ≫ t :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
  exact (congrArg (s ≫ ·) e').trans ((Category.assoc _ _ _).symm.trans
    ((comp_eq_of_natural F hF _ _).trans ((congrArg (F B) e'').trans
      ((comp_eq_of_natural F hF _ _).symm.trans (Category.assoc _ _ _)))))

section Over

variable {R : Type u} [CommRing R]

/-- The affine scheme of an `R`-algebra, as a scheme over `Spec R`. -/
abbrev specOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The morphism of affine schemes over `Spec R` induced by an `R`-algebra map. -/
def specMapOver {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : specOver (R := R) B ⟶ specOver A :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : R →+* B => Spec.map (CommRingCat.ofHom f)) (RingHom.ext φ.commutes))

@[simp] theorem specMapOver_left {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) :
    (specMapOver φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

/-- The `R`-algebra structure on `A` induced by a morphism `Spec A ⟶ Spec R`. -/
abbrev algebraOfHom {A : Type u} [CommRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) : Algebra R A :=
  (Spec.preimage s).hom.toAlgebra

theorem specMap_algebraMap_algebraOfHom {A : Type u} [CommRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    letI := algebraOfHom s
    Spec.map (CommRingCat.ofHom (algebraMap R A)) = s := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- Two `R`-algebra structures inducing the same morphism to `Spec R` agree. -/
theorem algebra_ext_of_specMap {A : Type u} [CommRing A] (i₁ i₂ : Algebra R A)
    (h : Spec.map (CommRingCat.ofHom (@algebraMap R A _ _ i₁)) =
      Spec.map (CommRingCat.ofHom (@algebraMap R A _ _ i₂))) : i₁ = i₂ := by
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  exact Algebra.algebra_ext _ _ fun r => by
    simpa using congrArg (fun f : R →+* A => f r) h'

/-- A ring map compatible with given morphisms to `Spec R` is an `R`-algebra map for any
compatible algebra structures. -/
def algHomOfSpec {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →+* B)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) : A →ₐ[R] B :=
  { φ with
    commutes' := fun r => by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
      have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
      simpa using congrArg (fun f : R →+* B => f r) h' }

@[simp] theorem algHomOfSpec_toRingHom {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →+* B)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    (algHomOfSpec φ h).toRingHom = φ := rfl

/-- The point over `Spec R` given by a morphism from an affine scheme, with its induced
algebra structure. -/
def pointOfHom {T : Over (Spec (CommRingCat.of R))} {A : Type u} [CommRing A]
    (t : Spec (CommRingCat.of A) ⟶ T.left) :
    letI := algebraOfHom (t ≫ T.hom)
    specOver (R := R) A ⟶ T :=
  letI := algebraOfHom (t ≫ T.hom)
  Over.homMk t (specMap_algebraMap_algebraOfHom (t ≫ T.hom)).symm

@[simp] theorem pointOfHom_left {T : Over (Spec (CommRingCat.of R))} {A : Type u}
    [CommRing A] (t : Spec (CommRingCat.of A) ⟶ T.left) : (pointOfHom t).left = t := rfl

/-- Two morphisms over `Spec R` agreeing on every affine point over `Spec R` are equal. -/
theorem over_hom_ext {X Y : Over (Spec (CommRingCat.of R))} {f g : X ⟶ Y}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : specOver (R := R) A ⟶ X),
      x ≫ f = x ≫ g) : f = g := by
  ext1
  refine hom_ext fun A t => ?_
  let := algebraOfHom (t ≫ X.hom)
  have := congrArg CommaMorphism.left (h A (pointOfHom t))
  simpa using this

/-- Maps on affine points over `Spec R` only depend on the underlying morphism of schemes
once the algebra structures agree. -/
theorem F_left_congr {X Y : Over (Spec (CommRingCat.of R))}
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], (specOver (R := R) A ⟶ X) →
      (specOver (R := R) A ⟶ Y))
    {A : Type u} [CommRing A] {i₁ i₂ : Algebra R A} (h : i₁ = i₂)
    (x₁ : @specOver R _ A _ i₁ ⟶ X) (x₂ : @specOver R _ A _ i₂ ⟶ X) (hx : x₁.left = x₂.left) :
    (@F A _ i₁ x₁).left = (@F A _ i₂ x₂).left := by
  subst h
  obtain rfl : x₁ = x₂ := Over.OverMorphism.ext hx
  rfl

/-- A family of maps on affine points over `Spec R` that is natural for `R`-algebra maps comes
from a morphism over `Spec R`. -/
theorem exists_over_hom {X Y : Over (Spec (CommRingCat.of R))}
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], (specOver (R := R) A ⟶ X) →
      (specOver (R := R) A ⟶ Y))
    (hF : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (x : specOver (R := R) A ⟶ X),
      F B (specMapOver φ ≫ x) = specMapOver φ ≫ F A x) :
    ∃ f : X ⟶ Y, ∀ (A : Type u) [CommRing A] [Algebra R A] (x : specOver (R := R) A ⟶ X),
      x ≫ f = F A x := by
  let F' : ∀ A : CommRingCat.{u}, (Spec A ⟶ X.left) → (Spec A ⟶ Y.left) := fun A t =>
    letI := algebraOfHom (t ≫ X.hom)
    (F A (pointOfHom t)).left
  have hF' : ∀ (A B : CommRingCat.{u}) (φ : A ⟶ B) (t : Spec A ⟶ X.left),
      F' B (Spec.map φ ≫ t) = Spec.map φ ≫ F' A t := by
    intro A B φ t
    let iA := algebraOfHom (t ≫ X.hom)
    let iB := algebraOfHom ((Spec.map φ ≫ t) ≫ X.hom)
    have hφ : Spec.map (CommRingCat.ofHom φ.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [specMap_algebraMap_algebraOfHom, specMap_algebraMap_algebraOfHom, Category.assoc,
        CommRingCat.ofHom_hom]
    let ψ := algHomOfSpec φ.hom hφ
    have hx : pointOfHom (Spec.map φ ≫ t) = specMapOver ψ ≫ pointOfHom t := by
      ext1; rfl
    change (F B (pointOfHom (Spec.map φ ≫ t))).left = Spec.map φ ≫ (F A (pointOfHom t)).left
    rw [hx, hF]
    rfl
  obtain ⟨f, hf⟩ := exists_hom F' hF'
  have hfw : f ≫ Y.hom = X.hom := by
    refine hom_ext fun A t => ?_
    rw [← Category.assoc, hf]
    let := algebraOfHom (t ≫ X.hom)
    exact (Over.w (F A (pointOfHom t))).trans (specMap_algebraMap_algebraOfHom _)
  refine ⟨Over.homMk f hfw, fun A _ _ x => ?_⟩
  ext1
  change x.left ≫ f = _
  rw [hf]
  have hi : algebraOfHom (x.left ≫ X.hom) = ‹Algebra R A› := by
    refine algebra_ext_of_specMap _ _ ?_
    rw [specMap_algebraMap_algebraOfHom]
    simp
  exact F_left_congr F hi _ _ rfl

end Over

end Langlands.AlgebraicGeometry.AffinePoints
