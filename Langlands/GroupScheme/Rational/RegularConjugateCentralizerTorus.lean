import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Centralizers of points conjugate to points with toral centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {K L E : Type u} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]

/-- A closed torus containing the all-test centralizer of a point represents that
centralizer: the point lies in its own centralizer and the torus is commutative. -/
theorem isRepresentedBy_pointCentralizer_of_le {G : GroupScheme (Spec (CommRingCat.of L))}
    (z : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ G.X) {S : GroupScheme (Spec (CommRingCat.of L))}
    {j : S ⟶ G} (hS : IsTorus S) (hj : IsClosedSubgroup j)
    (hC : ∀ {Z : Over (Spec (CommRingCat.of L))} (c : Z ⟶ G.X),
      c * (toUnit Z ≫ z) = (toUnit Z ≫ z) * c → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) :
    (G.pointCentralizer z).IsRepresentedBy j := by
  have : IsCommMonObj S.X := hS.isCommMonObj
  have : Mono j.hom.hom.left := hj.mono
  refine ⟨Over.mono_of_mono_left _, range_eq_pointCentralizer G z fun T c hc => ?_⟩
  exact SubgroupFunctor.mem_range.mpr (hC c ((mem_pointCentralizer G z c).mp hc))

/-- **The centralizer of a conjugate of a point with toral centralizer is a torus.** Let the
centralizer of a point `z` of `G` over a field `L ⊇ K` be represented by a torus `S`, and let
a `K`-rational point `x` become conjugate to `z` over a field `E` with a `K`-embedding
`L → E`. Then every group scheme representing the centralizer of `x` is a torus over `K`. -/
theorem isTorus_of_isRepresentedBy_pointCentralizer
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X}
    {S : GroupScheme (Spec (CommRingCat.of L))}
    {j : S ⟶ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G}
    (hS : IsTorus S)
    (hj : (((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
      G).pointCentralizer ((baseChangeBasePointsEquiv _ G).symm z)).IsRepresentedBy j)
    {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X}
    (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X)
    (hg : g * (toUnit _ ≫ x) * g⁻¹ = q ≫ z)
    {T : GroupScheme (Spec (CommRingCat.of K))} {i : T ⟶ G}
    (hi : (G.pointCentralizer x).IsRepresentedBy i) : IsTorus T := by
  have hq : q.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) := Over.w q
  let e : Over.mk (q.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) :=
    Over.homMk (𝟙 _) (by simp [hq])
  have he : e ≫ q = Over.homMk (U := Over.mk (q.left ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K L)))) (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      q.left := by
    apply Over.OverMorphism.ext
    simp [e]
  have hg' : (e ≫ g) * (toUnit _ ≫ x) * (e ≫ g)⁻¹ =
      Over.homMk (U := Over.mk (q.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) q.left ≫ z := by
    rw [← he, Category.assoc, ← hg, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc e (toUnit _) x, toUnit_unique (e ≫ toUnit _) (toUnit _)]
  have hrep := isRepresentedBy_pointCentralizer_baseChange_of_conj G _ q.left hj (e ≫ g) hg'
  let : Algebra L E := (Spec.preimage q.left).hom.toAlgebra
  have hc : Spec.map (CommRingCat.ofHom (algebraMap L E)) = q.left := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hSE : IsTorus ((GroupScheme.baseChange q.left).obj S) := by
    have h := IsTorus.baseChange (K := E) hS
    rwa [hc] at h
  have hTE : IsTorus ((GroupScheme.baseChange
      (q.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj T) :=
    IsTorus.of_iso ((hi.baseChange _).isoOfIsRepresentedBy hrep) hSE
  rw [hq] at hTE
  exact IsTorus.of_baseChange hTE

end Langlands.GroupScheme
