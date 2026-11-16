import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Affine refinements of étale surjections over compact bases -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}}

/-- An affine étale map into the covering scheme whose composite still covers the base. -/
structure AffineEtaleRefinement (p : S ⟶ B) where
  obj : Scheme.{u}
  map : obj ⟶ S
  affine : IsAffine obj
  etale : Etale map
  surjective : Surjective (map ≫ p)

attribute [instance] AffineEtaleRefinement.affine AffineEtaleRefinement.etale
  AffineEtaleRefinement.surjective

theorem exists_affineEtaleRefinement (p : S ⟶ B) [Etale p] [Surjective p]
    [CompactSpace B] : Nonempty (AffineEtaleRefinement p) := by
  let U := p.cover (show Etale p from inferInstance)
  have : QuasiCompactCover U.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun _ => p.isOpenMap)
  obtain ⟨V, f, hfin, hopen⟩ :
      ∃ (V : Scheme.AffineCover.{u} @Etale B) (f : V.cover ⟶ U),
        Finite V.I₀ ∧ ∀ i, IsOpenImmersion (f.h₀ i) :=
    QuasiCompactCover.exists_hom U
  have : Finite V.cover.I₀ := hfin
  have (i : V.I₀) : IsOpenImmersion (f.h₀ i) := hopen i
  have (i : V.cover.I₀) : IsAffine (V.cover.X i) := by
    change IsAffine (Spec (V.X i))
    infer_instance
  let q : (∐ V.cover.X) ⟶ S := Sigma.desc (fun i => f.h₀ i)
  have hq : q ≫ p = Sigma.desc V.cover.f := by
    apply Sigma.hom_ext
    intro i
    simpa only [q, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      U, Scheme.Hom.cover_f] using f.w₀ i
  refine ⟨{
    obj := ∐ V.cover.X
    map := q
    affine := by infer_instance
    etale := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i => inferInstance)
    surjective := ?_ }⟩
  rw [hq]
  infer_instance

/-- Choose an actual affine étale refinement of an étale surjection over a compact base. -/
def affineEtaleRefinement (p : S ⟶ B) [Etale p] [Surjective p] [CompactSpace B] :
    AffineEtaleRefinement p :=
  Classical.choice (exists_affineEtaleRefinement p)

end Langlands.GroupScheme.Descent
