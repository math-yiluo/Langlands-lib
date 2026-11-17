import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.GroupScheme.Torus.MultiplicativeTypeInfinitesimalLiftStatement
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Infinitesimal lifting along arbitrary nilpotent surjections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {B C : Type u} [CommRing B] [CommRing C]

/-- The test scheme of a surjective ring map is canonically its kernel quotient over the
original affine base. -/
def surjectionTestIso (φ : B →+* C) (hφ : Function.Surjective φ) :
    Over.mk (Spec.map (CommRingCat.ofHom φ)) ≅
      Over.mk (Spec.algebraMap B (B ⧸ RingHom.ker φ)) :=
  Over.isoMk (Scheme.Spec.mapIso (φ.quotientKerEquivOfSurjective hφ).toCommRingCatIso.op) (by
    change Spec.map (CommRingCat.ofHom
        (φ.quotientKerEquivOfSurjective hφ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ RingHom.ker φ))) =
        Spec.map (CommRingCat.ofHom φ)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1)

/-- Evaluation along an isomorphism of test schemes is bijective. -/
theorem evaluate_iso_bijective {S : Scheme.{u}} {H G : GroupScheme S}
    {T T' : Over S} (e : T' ≅ T) :
    Function.Bijective (evaluate (H := H) (G := G) e.hom) := by
  constructor
  · intro f g hfg
    have h := congrArg (evaluate (H := H) (G := G) e.inv) hfg
    simpa only [← evaluate_comp, e.inv_hom_id, evaluate_id] using h
  · intro f
    refine ⟨evaluate e.inv f, ?_⟩
    rw [← evaluate_comp, e.hom_inv_id, evaluate_id]

/-- The published infinitesimal proposition implies the same lifting and kernel-conjugacy
conclusions for any surjective ring map with nilpotent kernel. -/
theorem infinitesimal_lifting_of_surjection
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (φ : B →+* C) (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (H G : GroupScheme (Spec (CommRingCat.of B))) [Smooth G.X.hom]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) :
    let r := Spec.map (CommRingCat.ofHom φ)
    (∀ f₀ : (baseChange r).obj H ⟶ (baseChange r).obj G,
      ∃ f : H ⟶ G, (baseChange r).map f = f₀) ∧
    (∀ f f' : H ⟶ G, (baseChange r).map f = (baseChange r).map f' →
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of B))) ⟶ G.X,
        G.constantPoint g (Over.mk r) = 1 ∧ f' = f ≫ (G.innerIso g).hom) := by
  let r := Spec.map (CommRingCat.ofHom φ)
  let q := Spec.algebraMap B (B ⧸ RingHom.ker φ)
  let e : Over.mk r ≅ Over.mk q := surjectionTestIso φ hφ
  have hEval := evaluate_iso_bijective (H := H) (G := G) e
  obtain ⟨hlift, hconj⟩ := hInf B (RingHom.ker φ) hnil G H hH
  constructor
  · intro f₀
    obtain ⟨f, hf⟩ := hlift (evaluate e.inv f₀)
    refine ⟨f, ?_⟩
    calc
      _ = evaluate e.hom ((baseChange q).map f) := (evaluate_baseChange e.hom f).symm
      _ = evaluate e.hom (evaluate e.inv f₀) := congrArg (evaluate e.hom) hf
      _ = f₀ := by rw [← evaluate_comp, e.hom_inv_id, evaluate_id]
  · intro f f' hff'
    have hq : (baseChange q).map f = (baseChange q).map f' := by
      apply hEval.injective
      calc
        _ = (baseChange r).map f := evaluate_baseChange e.hom f
        _ = (baseChange r).map f' := hff'
        _ = _ := (evaluate_baseChange e.hom f').symm
    obtain ⟨g, hg, hfg⟩ := hconj f f' hq
    refine ⟨g, ?_, hfg⟩
    calc
      _ = e.hom ≫ G.constantPoint g (Over.mk q) :=
        (G.constantPoint_naturality g e.hom).symm
      _ = e.hom ≫ 1 := congrArg (e.hom ≫ ·) hg
      _ = 1 := MonObj.comp_one _

end Langlands.GroupScheme.HomScheme
