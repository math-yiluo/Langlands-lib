import Langlands.Geometry.Building.CrossTorusTranslation
import Langlands.GroupScheme.Rational.CrossTorusRootTransport

/-! # Root-function families under actual cross-torus transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

namespace RootFunctionFamily

/-- Reindex the entire family by the actual character and ambient-point isomorphisms. -/
def transportEquiv (e : S ≅ S') (f : G ≅ H) :
    RootFunctionFamily S G ≃ RootFunctionFamily S' H where
  toFun φ := ⟨fun a g => φ ((characterLattice.congr e).symm a) (rationalPoints.map f.inv g)⟩
  invFun ψ := ⟨fun a g => ψ (characterLattice.congr e a) (rationalPoints.map f.hom g)⟩
  left_inv φ := by
    ext a g
    simp only [AddEquiv.symm_apply_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv ψ := by
    ext a g
    simp only [AddEquiv.apply_symm_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- The forward map uses inverse precomposition on both actual indices. -/
theorem transportEquiv_apply (e : S ≅ S') (f : G ≅ H) (φ : RootFunctionFamily S G)
    (a : characterLattice S') (g : rationalPoints H) :
    transportEquiv e f φ a g =
      φ ((characterLattice.congr e).symm a) (rationalPoints.map f.inv g) := rfl

/-- On actual transported inputs the value is unchanged. -/
@[simp] theorem transportEquiv_apply_map (e : S ≅ S') (f : G ≅ H)
    (φ : RootFunctionFamily S G) (a : characterLattice S) (g : rationalPoints G) :
    transportEquiv e f φ (characterLattice.congr e a) (rationalPoints.map f.hom g) =
      φ a g := by
  simp only [transportEquiv_apply, AddEquiv.symm_apply_apply, rationalPoints.map_apply,
    Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

/-- Simultaneous character and cocharacter transport intertwines the original translations. -/
theorem transportEquiv_vadd (e : S ≅ S') (f : G ≅ H)
    (φ : RootFunctionFamily S G) (v : V S) :
    transportEquiv e f (v +ᵥ φ) = cocharacterRealCongr e v +ᵥ transportEquiv e f φ := by
  ext a g
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  simp only [transportEquiv_apply, vadd_apply, AddEquiv.symm_apply_apply,
    eval_cocharacterRealCongr]

/-- The whole equipollence relation is carried to the target relation. -/
theorem equipollent_transportEquiv_iff (e : S ≅ S') (f : G ≅ H)
    (φ ψ : RootFunctionFamily S G) :
    Equipollent (transportEquiv e f φ) (transportEquiv e f ψ) ↔ Equipollent φ ψ := by
  constructor
  · rintro ⟨v', hv'⟩
    obtain ⟨v, rfl⟩ := (cocharacterRealCongr e).surjective v'
    refine ⟨v, (transportEquiv e f).injective ?_⟩
    rw [transportEquiv_vadd]
    exact hv'
  · rintro ⟨v, rfl⟩
    exact ⟨cocharacterRealCongr e v, transportEquiv_vadd e f φ v⟩

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- The family equivalence intertwines the original action of actual normalizer points. -/
theorem transportEquiv_smul (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints i) (φ : RootFunctionFamily S G) :
    transportEquiv e f (n • φ) =
      normalizerPointsTransportEquiv e f h n • transportEquiv e f φ := by
  ext a g
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  let g₀ := rationalPoints.map f.inv g
  have hg : g = rationalPoints.map f.hom g₀ := by
    dsimp [g₀]
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [hg, smul_apply, ← map_inv, weylAction_transport]
  have hn : (normalizerPointsTransportEquiv e f h n : rationalPoints H) =
      rationalPoints.map f.hom (n : rationalPoints G) := rfl
  rw [hn, ← map_inv, ← map_mul, ← map_mul, transportEquiv_apply_map,
    transportEquiv_apply_map, smul_apply]

end RootFunctionFamily

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include h

/-- Membership in the actual rational root group is preserved and reflected. -/
theorem rootGroupPoints_transport_iff (a : characterLattice S) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ rootGroupPoints j (characterLattice.congr e a) ↔
      g ∈ rootGroupPoints i a := by
  exact Iff.of_eq (congrArg (fun K : SubgroupFunctor G => g ∈ K.carrier (Over.mk (𝟙 _)))
    (RelativeRoot.subgroup_comap_of_transport e f h a))

/-- Every actual filtration set is transported with its original level unchanged. -/
theorem rootFiltration_transport_iff (φ : RootFunctionFamily S G)
    (a : characterLattice S) (r : ℝ) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        rootFiltration j (RootFunctionFamily.transportEquiv e f φ) (characterLattice.congr e a) r ↔
      g ∈ rootFiltration i φ a r := by
  rw [mem_rootFiltration, mem_rootFiltration, rootGroupPoints_transport_iff e f h,
    RootFunctionFamily.transportEquiv_apply_map]

end Langlands.Geometry.Building
