import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Points of schemes over affine spectra through affine charts

Fix an affine open `S₀` of a base scheme `S`. Every algebra `C` over `Γ(S, S₀)` gives a scheme
`Spec C` over `S`. For a scheme `Y` over `S` and an affine open `U` of `Y` lying over `S₀`,
algebra maps `Γ(Y, U) → C` give points `Spec C ⟶ Y` over `S`. These points are injective in
the algebra map, natural in `C`, and they are exactly the points whose image lies in `U`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)

/-- The structure morphism of `Spec C` for an algebra `C` over sections on `S₀`. -/
def testMap (C : Type u) [CommRing C] [Algebra Γ(S, S₀) C] : Spec (CommRingCat.of C) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) C)) ≫ hS₀.fromSpec

/-- The scheme `Spec C` as an object over `S`. -/
@[implicit_reducible]
def testObj (C : Type u) [CommRing C] [Algebra Γ(S, S₀) C] : Over S :=
  Over.mk (testMap hS₀ C)

variable {C C' C'' : Type u} [CommRing C] [CommRing C'] [CommRing C'']
  [Algebra Γ(S, S₀) C] [Algebra Γ(S, S₀) C'] [Algebra Γ(S, S₀) C'']

/-- An algebra map induces a morphism of spectra over `S`, in the opposite direction. -/
def testHom (q : C →ₐ[Γ(S, S₀)] C') : testObj hS₀ C' ⟶ testObj hS₀ C :=
  Over.homMk (Spec.map (CommRingCat.ofHom (q : C →+* C'))) (by
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc]
    congr 2
    ext r
    exact q.commutes r)

@[simp]
lemma testHom_left (q : C →ₐ[Γ(S, S₀)] C') :
    (testHom hS₀ q).left = Spec.map (CommRingCat.ofHom (q : C →+* C')) := rfl

@[simp]
lemma testHom_id : testHom hS₀ (AlgHom.id Γ(S, S₀) C) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

lemma testHom_comp (q : C →ₐ[Γ(S, S₀)] C') (q' : C' →ₐ[Γ(S, S₀)] C'') :
    testHom hS₀ (q'.comp q) = testHom hS₀ q' ≫ testHom hS₀ q := by
  ext1
  rw [Over.comp_left, testHom_left, testHom_left, testHom_left, ← Spec.map_comp]
  rfl

/-- A surjective ring map with nilpotent kernel induces a surjection of spectra. -/
lemma specMap_surjective (q : C →+* C') (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker q, IsNilpotent x) :
    Function.Surjective (Spec.map (CommRingCat.ofHom q)) := by
  have h : Set.range (PrimeSpectrum.comap q) = Set.univ := by
    rw [range_comap_of_surjective _ _ hq, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    exact (mem_nilradical).mpr (hnil x hx)
  intro z
  obtain ⟨w, hw⟩ := (Set.eq_univ_iff_forall.mp h) z
  exact ⟨w, hw⟩

/-- Precomposition with a nil-thickening does not change the image of a morphism. -/
lemma range_testHom_comp (q : C →ₐ[Γ(S, S₀)] C') (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker (q : C →+* C'), IsNilpotent x) {Y : Over S}
    (x : testObj hS₀ C ⟶ Y) :
    Set.range (testHom hS₀ q ≫ x).left = Set.range x.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(testHom hS₀ q).left w, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := specMap_surjective (q : C →+* C') hq hnil w
    refine ⟨v, ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply, testHom_left]
    exact congrArg x.left hv

variable (S₀) in
/-- An affine open of a scheme over `S`, lying over the fixed affine open `S₀`. -/
structure Chart (Y : Over S) where
  /-- The affine open. -/
  U : Y.left.Opens
  isAffine : IsAffineOpen U
  le : U ≤ Y.hom ⁻¹ᵁ S₀

namespace Chart

variable {Y : Over S} (c : Chart S₀ Y)

/-- The ring of sections on a chart. -/
def Ring : Type u := Γ(Y.left, c.U)

instance : CommRing c.Ring := inferInstanceAs (CommRing Γ(Y.left, c.U))

instance : Algebra Γ(S, S₀) c.Ring := (Y.hom.appLE S₀ c.U c.le).hom.toAlgebra

lemma algebraMap_eq : algebraMap Γ(S, S₀) c.Ring = (Y.hom.appLE S₀ c.U c.le).hom := rfl

/-- The canonical open immersion from the spectrum of the chart ring. -/
def fromSpec : Spec (CommRingCat.of c.Ring) ⟶ Y.left := c.isAffine.fromSpec

instance : IsOpenImmersion c.fromSpec := inferInstanceAs (IsOpenImmersion c.isAffine.fromSpec)

lemma range_fromSpec : Set.range c.fromSpec = c.U := c.isAffine.range_fromSpec

lemma fromSpec_hom : c.fromSpec ≫ Y.hom =
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)) ≫ hS₀.fromSpec :=
  (IsAffineOpen.SpecMap_appLE_fromSpec Y.hom hS₀ c.isAffine c.le).symm

/-- The point of `Y` defined by an algebra map out of the sections on a chart. -/
def pt (ψ : c.Ring →ₐ[Γ(S, S₀)] C) : testObj hS₀ C ⟶ Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom (ψ : c.Ring →+* C)) ≫ c.fromSpec) (by
    change (Spec.map (CommRingCat.ofHom (ψ : c.Ring →+* C)) ≫ c.fromSpec) ≫ Y.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) C)) ≫ hS₀.fromSpec
    rw [Category.assoc, c.fromSpec_hom hS₀, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact ψ.commutes r)

@[simp]
lemma pt_left (ψ : c.Ring →ₐ[Γ(S, S₀)] C) :
    (c.pt hS₀ ψ).left = Spec.map (CommRingCat.ofHom (ψ : c.Ring →+* C)) ≫ c.fromSpec := rfl

lemma pt_injective : Function.Injective (c.pt hS₀ (C := C)) := by
  intro ψ ψ' h
  have h' := congrArg CommaMorphism.left h
  have h'' : Spec.map (CommRingCat.ofHom (ψ : c.Ring →+* C)) ≫ c.fromSpec =
      Spec.map (CommRingCat.ofHom (ψ' : c.Ring →+* C)) ≫ c.fromSpec := h'
  have h''' := Spec.map_injective ((cancel_mono c.fromSpec).mp h'')
  apply AlgHom.coe_ringHom_injective
  exact congrArg CommRingCat.Hom.hom h'''

lemma testHom_comp_pt (q : C →ₐ[Γ(S, S₀)] C') (ψ : c.Ring →ₐ[Γ(S, S₀)] C) :
    testHom hS₀ q ≫ c.pt hS₀ ψ = c.pt hS₀ (q.comp ψ) := by
  ext1
  rw [Over.comp_left, testHom_left, pt_left, pt_left, ← Spec.map_comp_assoc]
  rfl

lemma range_pt (ψ : c.Ring →ₐ[Γ(S, S₀)] C) : Set.range (c.pt hS₀ ψ).left ⊆ c.U := by
  rintro _ ⟨z, rfl⟩
  rw [pt_left, Scheme.Hom.comp_apply, ← c.range_fromSpec]
  exact ⟨_, rfl⟩

/-- Every point over `S` with image in a chart comes from an algebra map. -/
lemma exists_pt (x : testObj hS₀ C ⟶ Y) (hx : Set.range x.left ⊆ c.U) :
    ∃ ψ : c.Ring →ₐ[Γ(S, S₀)] C, c.pt hS₀ ψ = x := by
  let x' : Spec (CommRingCat.of C) ⟶ Y.left := x.left
  let g := IsOpenImmersion.lift c.fromSpec x' (by rw [c.range_fromSpec]; exact hx)
  have hg : g ≫ c.fromSpec = x' := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hw : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring) ≫ φ) ≫ hS₀.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) C)) ≫ hS₀.fromSpec := by
    rw [Spec.map_comp_assoc, ← c.fromSpec_hom hS₀, ← Category.assoc, hφ, hg]
    exact Over.w x
  have hw' := Spec.map_injective ((cancel_mono _).mp hw)
  refine ⟨{ φ.hom with commutes' := fun r => ?_ }, ?_⟩
  · exact congrArg (fun h => CommRingCat.Hom.hom h r) hw'
  · ext1
    change Spec.map φ ≫ c.fromSpec = x'
    rw [hφ, hg]

end Chart

end Langlands.AlgebraicGeometry
