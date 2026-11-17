import Langlands.GroupScheme.HomogeneousQuotientSheaf
import Langlands.GroupScheme.RelativeQuasiAffineHomogeneousQuotient
import Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent

/-! # Recovering homogeneous quotients from their canonical sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.HomogeneousQuotientSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : Smooth H.X.hom)
  (V : Over S) (e : (schemeYoneda S).obj V ≅ presheaf i)

/-- The canonical quotient map transported through a scheme representation. -/
def schemeProjection : G.X ⟶ V :=
  (schemeYoneda S).preimage (projection i ≫ e.inv)

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
@[reassoc]
lemma schemeProjection_fac :
    (schemeYoneda S).map (schemeProjection i V e) ≫ e.hom = projection i := by
  dsimp [schemeProjection]
  rw [Functor.map_preimage]
  simp

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
lemma schemeProjection_isPullback :
    IsPullback (𝟙 ((schemeYoneda S).obj G.X))
      ((schemeYoneda S).map (schemeProjection i V e)) (projection i) e.hom :=
  IsPullback.of_horiz_isIso ⟨by simpa using (schemeProjection_fac i V e).symm⟩

omit [IsAffineHom G.X.hom] in
include hH in
lemma smooth_schemeProjection : Smooth (schemeProjection i V e).left :=
  (smooth_projection i hH).projection e.hom (𝟙 _) (schemeProjection i V e)
    (schemeProjection_isPullback i V e)

omit [IsAffineHom G.X.hom] in
include hH in
lemma surjective_schemeProjection : Surjective (schemeProjection i V e).left :=
  (surjective_projection i hH).projection e.hom (𝟙 _) (schemeProjection i V e)
    (schemeProjection_isPullback i V e)

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
lemma schemeProjection_fibers (T : Over S) (g h : T ⟶ G.X) :
    g ≫ schemeProjection i V e = h ≫ schemeProjection i V e ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  rw [← projection_eq_iff i T g h, ← schemeProjection_fac i V e]
  change g ≫ schemeProjection i V e = h ≫ schemeProjection i V e ↔
    e.hom.app (op T) ⟨g ≫ schemeProjection i V e⟩ =
      e.hom.app (op T) ⟨h ≫ schemeProjection i V e⟩
  exact ULift.ext_iff.symm.trans (equivEquivIso.symm (e.app (op T))).injective.eq_iff.symm

/-- A separated scheme representing the canonical coset sheaf has all the
geometry and full coset fibers required of an actual homogeneous quotient. -/
def quotientOfIso [IsSeparated V.hom] : HomogeneousQuotient i := by
  let q := schemeProjection i V e
  let : Smooth q.left := smooth_schemeProjection i hH V e
  let : Surjective q.left := surjective_schemeProjection i hH V e
  have hfp : LocallyOfFinitePresentation V.hom := by
    have : LocallyOfFinitePresentation (q.left ≫ V.hom) := by
      rw [Over.w q]
      infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.left V.hom
  let : LocallyOfFinitePresentation V.hom := hfp
  have hqcomp : QuasiCompact (q.left ≫ V.hom) := by
    rw [Over.w q]
    infer_instance
  let : QuasiCompact (q.left ≫ V.hom) := hqcomp
  have hqc : QuasiCompact V.hom := by
    constructor
    intro U hopen hcompact
    have himage :=
      (QuasiCompact.isCompact_preimage (f := q.left ≫ V.hom) U hopen hcompact).image
        q.left.continuous
    change IsCompact (q.left '' (q.left ⁻¹' (V.hom ⁻¹' U))) at himage
    rwa [Set.image_preimage_eq _ q.left.surjective] at himage
  exact ⟨V, q, inferInstance, inferInstance, hqc, inferInstance, inferInstance,
    QuasiCompact.of_comp q.left V.hom, schemeProjection_fibers i V e⟩

variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- A quasi-affine local homogeneous quotient descends along an affine fppf
base cover to an actual quasi-affine homogeneous quotient. -/
def quotientAfterAffineDescent
    [IsAffine S] [IsAffine S'] [Flat b] [Surjective b]
    [LocallyOfFinitePresentation b]
    (Q : HomogeneousQuotient ((GroupScheme.baseChange b).map i))
    [Q.scheme.left.IsQuasiAffine] :
    {Q₀ : HomogeneousQuotient i // Smooth Q₀.scheme.hom ∧ Q₀.scheme.left.IsQuasiAffine} := by
  let r := Classical.choice (representableBy_baseChange i hH b Q)
  let M := Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent.quasiAffineModel
    r (sheaf i hH).property
  let : M.val.left.IsQuasiAffine := M.property.1
  let e₀ := (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1}
    (presheaf i) M.val) (Classical.choice M.property.2)
  let Q₀ := quotientOfIso i hH M.val e₀
  exact ⟨Q₀, Q₀.smooth_structure, M.property.1⟩

end Langlands.GroupScheme.HomogeneousQuotientSheaf
