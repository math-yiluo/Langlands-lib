import Langlands.GroupScheme.AntiAffineConnected
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy

/-! # A smooth connected geometric core of an anti-affine algebraic group -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual smooth connected closed subgroup with the same underlying
topological space as its ambient group. -/
structure AntiAffineSmoothCore {k : Type u} [Field k]
    (N : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ N
  smooth : Smooth group.X.hom
  connected : ConnectedSpace group.X.left
  closed : IsClosedImmersion inclusion.hom.hom.left
  homeomorph : group.X.left ≃ₜ N.X.left
  homeomorph_apply : ∀ x, homeomorph x = inclusion.hom.hom.left x

namespace IsAntiAffine

variable {k : Type u} [Field k]
    {N : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a perfect field, the actual reduction is the smooth connected core
of an anti-affine group locally of finite type. -/
def smoothCore [PerfectField k] [LocallyOfFiniteType N.X.hom]
    (hN : IsAntiAffine N) : AntiAffineSmoothCore N := by
  let e : (reducedSubgroup N).X.left ≃ₜ N.X.left :=
    (Equiv.ofBijective (ReducedSubgroup.redι N.X.left)
      ⟨ReducedSubgroup.redι_injective _, ReducedSubgroup.redι_surjective _⟩).toHomeomorphOfContinuousClosed
      (ReducedSubgroup.redι N.X.left).continuous (ReducedSubgroup.redι N.X.left).isClosedMap
  have : ConnectedSpace N.X.left := hN.connectedSpace
  refine
    { group := reducedSubgroup N
      inclusion := reducedSubgroupι N
      smooth := inferInstance
      connected := e.connectedSpace_iff.mpr inferInstance
      closed := inferInstance
      homeomorph := e
      homeomorph_apply := fun _ => rfl }

/-- The actual field extension of the ambient group to an algebraic closure. -/
abbrev geometricAmbient (N : GroupScheme (Spec (CommRingCat.of k))) :=
  (GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj N

local instance [LocallyOfFiniteType N.X.hom] :
    LocallyOfFiniteType (geometricAmbient N).X.hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd N.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))

/-- The actual geometric reduction, with its smooth connected subgroup and
canonical closed inclusion, for an arbitrary base field. -/
def geometricSmoothCore [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    (hN : IsAntiAffine N) : AntiAffineSmoothCore (geometricAmbient N) := by
  have : IsSeparated N.X.hom := fieldSeparated k N
  have : CompactSpace N.X.left := QuasiCompact.compactSpace_of_compactSpace N.X.hom
  have : QuasiSeparatedSpace N.X.left := quasiSeparatedSpace_of_quasiSeparated N.X.hom
  exact smoothCore (hN.baseChange (algebraMap k (AlgebraicClosure k)))

/-- Any actual smooth surjection from an anti-affine group to an affine
scheme forces smoothness of the original group. -/
theorem smooth_of_affine_smooth_surjection (hN : IsAntiAffine N)
    (Q : Over (Spec (CommRingCat.of k))) [IsAffine Q.left]
    (q : N.X ⟶ Q) [Smooth q.left] [Surjective q.left] : Smooth N.X.hom := by
  have : IsIso N.X.hom.appTop := hN
  let s := η[N.X].left
  have hq : q.left = N.X.hom ≫ s ≫ q.left :=
    Langlands.AlgebraicGeometry.affineMap_eq_constant_of_isIso_appTop
      N.X.hom s η[N.X].w q.left
  have hsec : Q.hom ≫ (s ≫ q.left) = 𝟙 Q.left := by
    apply (cancel_epi q.left).mp
    simp only [Category.comp_id]
    rw [← Category.assoc, Over.w]
    exact hq.symm
  have hret : (s ≫ q.left) ≫ Q.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w]
    exact η[N.X].w
  let e : Q.left ≅ Spec (CommRingCat.of k) :=
    ⟨Q.hom, s ≫ q.left, hsec, hret⟩
  have : IsIso Q.hom := e.isIso_hom
  rw [← Over.w q]
  infer_instance

end IsAntiAffine

end Langlands.GroupScheme
