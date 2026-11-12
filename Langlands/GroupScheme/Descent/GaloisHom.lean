import Langlands.GroupScheme.HomScheme.GraphBaseChange
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.CocharacterTransportNaturality

/-! # Actual homomorphisms descended from arbitrary Galois extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Compatibility of a homomorphism makes any actual graph inclusion
specified by its two projection identities compatible as well. -/
theorem graphHom_descent {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (G H : GroupScheme B)
    (f : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj H)
    (g : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj (G ⊗ H))
    (hfst : g ≫ (GroupScheme.baseChange b).map (CartesianMonoidalCategory.fst G H) = 𝟙 _)
    (hsnd : g ≫ (GroupScheme.baseChange b).map (CartesianMonoidalCategory.snd G H) = f)
    (hf : (GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha H).hom =
      (descentBaseChangeIso b a ha G).hom ≫ f) :
    (GroupScheme.baseChange a).map g ≫ (descentBaseChangeIso b a ha (G ⊗ H)).hom =
      (descentBaseChangeIso b a ha G).hom ≫ g := by
  apply (cancel_mono (baseChangeTensorIso b G H).hom).mp
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, baseChangeTensorIso_hom_fst]
    rw [← descentBaseChangeIso_naturality b a ha (CartesianMonoidalCategory.fst G H)]
    rw [← Category.assoc, ← Functor.map_comp]
    simp only [hfst, Category.comp_id]
    rw [(GroupScheme.baseChange a).map_id]
    exact Category.id_comp _
  · simp only [Category.assoc, baseChangeTensorIso_hom_snd]
    rw [← descentBaseChangeIso_naturality b a ha (CartesianMonoidalCategory.snd G H)]
    rw [← Category.assoc, ← Functor.map_comp]
    simpa only [hsnd] using hf

namespace Descent.GaloisHom

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj H)
    (hf : ∀ σ : L ≃ₐ[k] L,
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map f ≫
          (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
            (galoisBaseMap_over k L σ) H).hom =
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom ≫ f)

include hf

/-- A canonically Galois-compatible affine-group homomorphism has an actual
homomorphism over the original field with exact scalar-extension recovery. -/
theorem exists_hom : ∃ f₀ : G ⟶ H,
    (GroupScheme.baseChange (algebraBaseMap k L)).map f₀ = f := by
  let b := algebraBaseMap k L
  let g : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj (G ⊗ H) :=
    HomScheme.graphHom f ≫ (baseChangeTensorIso b G H).inv
  have hfst : g ≫ (GroupScheme.baseChange b).map (CartesianMonoidalCategory.fst G H) = 𝟙 _ := by
    simp only [g, Category.assoc, baseChangeTensorIso_inv_map_fst]
    exact HomScheme.graphHom_fst f
  have hsnd : g ≫ (GroupScheme.baseChange b).map (CartesianMonoidalCategory.snd G H) = f := by
    simp only [g, Category.assoc, baseChangeTensorIso_inv_map_snd, HomScheme.graphHom_snd]
  let : IsSeparated ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd H.X.hom b))
  have hg : IsClosedSubgroup g :=
    (show IsClosedSubgroup (HomScheme.graphHom f) from
      HomScheme.isClosedImmersion_graphHom f).comp_iso (baseChangeTensorIso b G H).symm
  have hginv : ∀ σ : L ≃ₐ[k] L,
      SubgroupFunctor.range (radicalGaloisHom g σ) = SubgroupFunctor.range g := by
    intro σ
    change SubgroupFunctor.range
      ((GroupScheme.baseChange (galoisBaseMap k L σ)).map g ≫
        (descentBaseChangeIso b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
          (G ⊗ H)).hom) = _
    rw [graphHom_descent b _ _ G H f g hfst hsnd (hf σ)]
    exact SubgroupFunctor.range_iso_comp _ _
  let : IsAffineHom (G ⊗ H).X.hom := by
    change IsAffineHom (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    let : IsAffineHom (pullback.fst G.X.hom H.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom H.X.hom)
    infer_instance
  obtain ⟨R, j, r, _, _, hr⟩ := GaloisInvariantClosedSubgroup.exists_descent hg hginv
  let p : R ⟶ G := j ≫ CartesianMonoidalCategory.fst G H
  have hp : (GroupScheme.baseChange b).map p = r.hom := by
    rw [Functor.map_comp, hr, Category.assoc, hfst, Category.comp_id]
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  let : IsIso ((GroupScheme.baseChange b).map p) := by rw [hp]; infer_instance
  let : IsIso p := isIso_of_baseChange b p
  refine ⟨inv p ≫ j ≫ CartesianMonoidalCategory.snd G H, ?_⟩
  apply (cancel_epi ((GroupScheme.baseChange b).map p)).mp
  rw [← Functor.map_comp]
  simp only [IsIso.hom_inv_id_assoc]
  rw [Functor.map_comp, hr, Category.assoc, hsnd, hp]

/-- Choose the actual descended homomorphism. -/
def hom : G ⟶ H := (exists_hom f hf).choose

/-- Scalar extension recovers the supplied compatible homomorphism exactly. -/
theorem baseChange_hom :
    (GroupScheme.baseChange (algebraBaseMap k L)).map (hom f hf) = f :=
  (exists_hom f hf).choose_spec

/-- Recovery determines the descended homomorphism uniquely. -/
theorem unique (f₀ : G ⟶ H)
    (h₀ : (GroupScheme.baseChange (algebraBaseMap k L)).map f₀ = f) : f₀ = hom f hf := by
  let b := algebraBaseMap k L
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  apply Grp.hom_ext
  apply (Over.pullback b).map_injective
  change ((GroupScheme.baseChange b).map f₀).hom.hom =
    ((GroupScheme.baseChange b).map (hom f hf)).hom.hom
  rw [h₀, baseChange_hom]

/-- An invertible compatible homomorphism descends as an actual isomorphism. -/
def iso [IsIso f] : G ≅ H := by
  let b := algebraBaseMap k L
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  let : IsIso ((GroupScheme.baseChange b).map (hom f hf)) := by
    rw [baseChange_hom]
    infer_instance
  let : IsIso (hom f hf) := isIso_of_baseChange b _
  exact asIso (hom f hf)

/-- The descended isomorphism's homomorphism has the exact requested recovery. -/
theorem baseChange_iso_hom [IsIso f] :
    (GroupScheme.baseChange (algebraBaseMap k L)).map (iso f hf).hom = f :=
  baseChange_hom f hf

end Descent.GaloisHom

end Langlands.GroupScheme
