import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Mathlib.AlgebraicGeometry.SpreadingOut

/-! # Spreading out local parametrizations of unirational schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]

/-- A finite-dimensional affine space over the ground field is unirational. -/
theorem isUnirational_affineSpace (ι : Type u) [Finite ι] :
    IsUnirational k
      (Over.mk (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) := by
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨x, -⟩ := (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).surjective s
  refine ⟨ι, inferInstance, ⊤, ⟨x, trivial⟩, Over.homMk (⊤ : (𝔸(ι; Spec
    (CommRingCat.of k))).Opens).ι rfl, ?_⟩
  exact (Opens.isDominant_ι (U := (⊤ : (𝔸(ι; Spec (CommRingCat.of k))).Opens))
    (by simp)).denseRange

/-- A dominant morphism over the ground field from a nonempty open subscheme of a
unirational scheme makes its target unirational. -/
theorem IsUnirational.of_open_denseRange {Y X : Over (Spec (CommRingCat.of k))}
    (hY : IsUnirational k Y) (V : Y.left.Opens) (hV : (V : Set Y.left).Nonempty)
    (f : V.toScheme ⟶ X.left) (hf : f ≫ X.hom = V.ι ≫ Y.hom) (hdense : DenseRange f) :
    IsUnirational k X := by
  obtain ⟨ι, hι, U, -, p, hp⟩ := hY
  let W : U.toScheme.Opens := p.left ⁻¹ᵁ V
  have hW : (W : Set U.toScheme).Nonempty := by
    obtain ⟨a, ha⟩ := hp.exists_mem_open V.isOpen hV
    exact ⟨a, ha⟩
  have : IsDominant p.left := ⟨hp⟩
  have : IsDominant f := ⟨hdense⟩
  have : IsDominant (p.left ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant p.left› V
  refine ⟨ι, hι, U.ι ''ᵁ W, ?_, Over.homMk ((U.ι.isoImage W).inv ≫ (p.left ∣_ V) ≫ f) ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hW
    exact ⟨U.ι a, a, ha, rfl⟩
  · have hp' : p.left ≫ Y.hom = U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)) := Over.w p
    simp only [Over.mk_hom, Category.assoc, hf, morphismRestrict_ι_assoc]
    rw [hp', ← U.ι.isoImage_inv_ι_assoc W]
  · exact Scheme.Hom.denseRange (f := (U.ι.isoImage W).inv ≫ (p.left ∣_ V) ≫ f)

/-- If a morphism from the spectrum of a local ring of a unirational scheme into a
scheme locally of finite type over the ground field has dense image, then the
target is unirational. -/
theorem IsUnirational.of_stalk {Y X : Over (Spec (CommRingCat.of k))}
    (hY : IsUnirational k Y) [LocallyOfFiniteType X.hom]
    (y : Y.left) [Y.left.IsGermInjectiveAt y]
    (φ : Spec (Y.left.presheaf.stalk y) ⟶ X.left)
    (hφ : φ ≫ X.hom = Y.left.fromSpecStalk y ≫ Y.hom)
    (hdense : DenseRange φ) :
    IsUnirational k X := by
  obtain ⟨V, hyV, f, hφf, hf⟩ := spread_out_of_isGermInjective' Y.hom X.hom φ hφ
  refine hY.of_open_denseRange V ⟨y, hyV⟩ f hf ?_
  refine hdense.mono ?_
  rw [hφf]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, rfl⟩

/-- A morphism over the ground field from the spectrum of a local ring of a
finite-dimensional affine space, with dense image in a scheme locally of finite
type, makes that scheme unirational. -/
theorem IsUnirational.of_affineSpace_stalk {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] {ι : Type u} [Finite ι]
    (x : 𝔸(ι; Spec (CommRingCat.of k)))
    (φ : Spec ((𝔸(ι; Spec (CommRingCat.of k))).presheaf.stalk x) ⟶ X.left)
    (hφ : φ ≫ X.hom = (𝔸(ι; Spec (CommRingCat.of k))).fromSpecStalk x ≫
      (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (hdense : DenseRange φ) :
    IsUnirational k X :=
  haveI : (Over.mk (𝔸(ι; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))).left.IsGermInjectiveAt x :=
    inferInstanceAs ((𝔸(ι; Spec (CommRingCat.of k))).IsGermInjectiveAt x)
  (isUnirational_affineSpace (k := k) ι).of_stalk
    (Y := Over.mk (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) x φ hφ hdense

/-- `X` has a point over the rational function field of a finite-dimensional affine
space over `k` (the local ring of that affine space at its generic point), compatible
with the maps to `Spec k`, whose image is dense in `X`. -/
def HasDenseRationalFunctionFieldPoint (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι)
      (φ : Spec (𝔸(ι; Spec (CommRingCat.of k))).functionField ⟶ X.left),
    φ ≫ X.hom = (𝔸(ι; Spec (CommRingCat.of k))).fromSpecStalk
        (genericPoint (𝔸(ι; Spec (CommRingCat.of k)))) ≫
      (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ∧
      DenseRange φ

/-- A dense point over a rational function field spreads out to an actual
affine-open parametrization. -/
theorem HasDenseRationalFunctionFieldPoint.isUnirational
    {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    (hX : HasDenseRationalFunctionFieldPoint k X) : IsUnirational k X := by
  obtain ⟨ι, hι, φ, hφ, hdense⟩ := hX
  exact IsUnirational.of_affineSpace_stalk _ φ hφ hdense

end Langlands.AlgebraicGeometry.PointTopology
