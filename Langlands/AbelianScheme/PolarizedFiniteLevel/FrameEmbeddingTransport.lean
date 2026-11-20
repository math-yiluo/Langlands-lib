import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbedding
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizedBundleTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.FibreDetection
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroTensor
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Frame-normalized embeddings: flatness of the image and transport along isomorphisms -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- The underlying scheme morphism of an isomorphism of abelian schemes is an isomorphism. -/
instance isIso_hom_of_iso {A B : AbelianScheme S} (e : A ≅ B) : IsIso (hom e.hom) :=
  ⟨⟨hom e.inv, by rw [← hom_comp, e.hom_inv_id, hom_id],
    by rw [← hom_comp, e.inv_hom_id, hom_id]⟩⟩

/-- The underlying scheme morphism of a homomorphism of abelian schemes lies over the
base. -/
@[reassoc (attr := simp)]
lemma hom_structure {A B : AbelianScheme S} (f : A ⟶ B) :
    hom f ≫ B.X.hom = A.X.hom :=
  Over.w (groupHom f).hom.hom

/-- A polarized isomorphism carries every torsion point to the torsion point with the same
coefficients. -/
theorem PolarizedIso.torsionPoint_hom {a b : Datum P S g d n} (e : PolarizedIso a b)
    (r : Fin (2 * g) → ZMod n) :
    a.torsionPoint r ≫ hom e.abelianIso.hom = b.torsionPoint r := by
  rw [Datum.torsionPoint, Datum.torsionPoint, ← e.mapTuple_eq, enumerateTuple_map]
  rfl

variable {a : Datum P S g d n} {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}
  {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}

/-- The closed subscheme cut out by a closed immersion over the base is isomorphic to its
source over the base. -/
lemma subschemeι_ker_toBase {X : Scheme.{u}} (ψ : X ⟶ RelativeProjectiveSpace S m)
    [IsClosedImmersion ψ] {π : X ⟶ S} (hψ : ψ ≫ RelativeProjectiveSpace.toBase S m = π) :
    ψ.ker.subschemeι ≫ RelativeProjectiveSpace.toBase S m = inv ψ.toImage ≫ π := by
  have h1 : ψ.ker.subschemeι = inv ψ.toImage ≫ ψ :=
    (IsIso.eq_inv_comp ψ.toImage).mpr ψ.toImage_imageι
  rw [h1, Category.assoc, hψ]

/-- The closed subscheme cut out by a frame-normalized embedding is flat over the base. -/
lemma Datum.IsFrameEmbedding.flat (h : a.IsFrameEmbedding ρ ψ) :
    Flat (ψ.ker.subschemeι ≫ RelativeProjectiveSpace.toBase S m) := by
  have := h.isClosedImmersion
  rw [subschemeι_ker_toBase ψ h.toBase]
  infer_instance

/-- The closed subscheme cut out by a frame-normalized embedding is locally of finite
presentation over the base. -/
lemma Datum.IsFrameEmbedding.locallyOfFinitePresentation (h : a.IsFrameEmbedding ρ ψ) :
    LocallyOfFinitePresentation (ψ.ker.subschemeι ≫ RelativeProjectiveSpace.toBase S m) := by
  have := h.isClosedImmersion
  rw [subschemeι_ker_toBase ψ h.toBase]
  infer_instance

/-- A frame-normalized embedding of `b` induces one of every datum polarized-isomorphic to
`b`, by precomposition with the isomorphism of abelian schemes. -/
theorem Datum.IsFrameEmbedding.ofPolarizedIso {a b : Datum P S g d n} (e : PolarizedIso a b)
    {ψ : b.abelian.X.left ⟶ RelativeProjectiveSpace S m} (h : b.IsFrameEmbedding ρ ψ) :
    a.IsFrameEmbedding ρ (hom e.abelianIso.hom ≫ ψ) where
  toBase := by rw [Category.assoc, h.toBase, hom_structure]
  isClosedImmersion := by
    have := h.isClosedImmersion
    infer_instance
  cubic := by
    obtain ⟨N, ⟨i⟩⟩ := h.cubic
    refine ⟨N, ⟨((LineBundle.pullbackComp _ _).app _).symm ≪≫
      (LineBundle.pullback (hom e.abelianIso.hom)).mapIso i ≪≫
      LineBundle.pullbackTensorObjIso P.preservation _ _ _ ≪≫
      LineBundle.tensorIso P.preservation
        (ObjectProperty.isoMk _ e.cubicBundlePullbackIso)
        ((LineBundle.pullbackComp _ _).app _ ≪≫
          eqToIso (congrArg (fun f => (LineBundle.pullback f).obj N)
            (hom_structure e.abelianIso.hom)))⟩⟩
  basis j k hkj := by
    have := h.basis j k hkj
    rwa [← e.torsionPoint_hom, Category.assoc] at this
  unit i k := by
    have := h.unit i k
    rwa [← e.torsionPoint_hom, Category.assoc] at this

/-- Precomposition with the isomorphism of a polarized isomorphism realizes the same
embedded family. -/
theorem Datum.Realizes.ofPolarizedIso {a b : Datum P S g d n} (e : PolarizedIso a b)
    {ψ : b.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {I : (RelativeProjectiveSpace S m).IdealSheafData}
    {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}
    (h : b.Realizes ψ I σ) : a.Realizes (hom e.abelianIso.hom ≫ ψ) I σ := by
  refine ⟨?_, fun r => ?_⟩
  · rw [Scheme.Hom.ker_comp_of_isIso]
    exact h.1
  · rw [← h.2 r, ← e.torsionPoint_hom]
    simp only [Category.assoc]

end Langlands.AbelianScheme.PolarizedFiniteLevel
