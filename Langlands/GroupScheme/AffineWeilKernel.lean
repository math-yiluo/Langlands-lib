import Langlands.GroupScheme.AffineWeilDynamics
import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.Kernel

/-! # Actual kernels commute with affine Weil restriction -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {G H : GroupScheme (Spec (CommRingCat.of B))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (f : G ⟶ H)

local instance : IsAffine (kernel f).X.left := by
  let : IsAffineHom G.X.hom := inferInstance
  let : IsSeparated H.X.hom := inferInstance
  let : IsAffineHom (kernel f).X.hom := by
    rw [← (kernelι f).hom.hom.w]
    infer_instance
  exact isAffine_of_isAffineHom (kernel f).X.hom

local instance : LocallyOfFiniteType (kernel f).X.hom := by
  let : IsSeparated H.X.hom := inferInstance
  rw [← (kernelι f).hom.hom.w]
  infer_instance

/-- The original and restricted pointwise kernels agree on the actual tensor test. -/
def pointwiseKernelEquiv (T : Over (Spec (CommRingCat.of A))) :
    (((yonedaGrp.map (map A B f)).app (op T)).hom.ker) ≃*
      (((yonedaGrp.map f).app (op (tensorTest A B T))).hom.ker) where
  toFun x := ⟨testPointsEquiv A B G T x.val, by
    have h := Corepresented.groupSchemeMap_points (corepresentableBy A B G)
      (corepresentableBy A B H) (pointTransformation A B f) x.val
    change testPointsEquiv A B H T (x.val ≫ (map A B f).hom.hom) =
      testPointsEquiv A B G T x.val ≫ f.hom.hom at h
    have hx : x.val ≫ (map A B f).hom.hom = 1 := x.property
    rw [hx, map_one] at h
    exact h.symm⟩
  invFun y := ⟨(testPointsEquiv A B G T).symm y.val, by
    apply (testPointsEquiv A B H T).injective
    have h := Corepresented.groupSchemeMap_points (corepresentableBy A B G)
      (corepresentableBy A B H) (pointTransformation A B f)
        ((testPointsEquiv A B G T).symm y.val)
    change testPointsEquiv A B H T
        ((testPointsEquiv A B G T).symm y.val ≫ (map A B f).hom.hom) =
      testPointsEquiv A B G T ((testPointsEquiv A B G T).symm y.val) ≫ f.hom.hom at h
    rw [MulEquiv.apply_symm_apply] at h
    change testPointsEquiv A B H T
        ((testPointsEquiv A B G T).symm y.val ≫ (map A B f).hom.hom) =
      testPointsEquiv A B H T 1
    rw [h, map_one]
    exact y.property⟩
  left_inv x := Subtype.ext ((testPointsEquiv A B G T).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((testPointsEquiv A B G T).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext ((testPointsEquiv A B G T).map_mul x.val y.val)

/-- Points of the two actual kernels agree on every scheme test. -/
def kernelTestPointsEquiv (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (kernel (map A B f)).X) ≃*
      (T ⟶ (groupScheme A B (kernel f)).X) :=
  (kernelPointsEquiv (map A B f) T).trans <|
    (pointwiseKernelEquiv A B f T).trans <|
      (kernelPointsEquiv f (tensorTest A B T)).symm.trans
        (testPointsEquiv A B (kernel f) T).symm

/-- On inclusion into the original source, the comparison is the original Weil comparison. -/
theorem kernelTestPointsEquiv_inclusion (T : Over (Spec (CommRingCat.of A)))
    (x : T ⟶ (kernel (map A B f)).X) :
    testPointsEquiv A B (kernel f) T (kernelTestPointsEquiv A B f T x) ≫
        (kernelι f).hom.hom =
      testPointsEquiv A B G T (x ≫ (kernelι (map A B f)).hom.hom) := by
  dsimp only [kernelTestPointsEquiv, MulEquiv.trans_apply]
  rw [MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val
    ((kernelPointsEquiv f (tensorTest A B T)).apply_symm_apply _)

/-- The actual-kernel comparison commutes with every change of test scheme. -/
theorem kernelTestPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T)
    (x : T ⟶ (kernel (map A B f)).X) :
    kernelTestPointsEquiv A B f T' (a ≫ x) = a ≫ kernelTestPointsEquiv A B f T x := by
  apply (testPointsEquiv A B (kernel f) T').injective
  apply (cancel_mono (kernelι f).hom.hom).mp
  rw [kernelTestPointsEquiv_inclusion,
    testPointsEquiv_naturality A B (kernel f) a]
  simp only [Category.assoc]
  rw [kernelTestPointsEquiv_inclusion]
  exact testPointsEquiv_naturality A B G a _

/-- Restriction of scalars commutes with the actual scheme-theoretic kernel. -/
def kernelIso : kernel (map A B f) ≅ groupScheme A B (kernel f) :=
  isoOfPoints (kernelTestPointsEquiv A B f) (kernelTestPointsEquiv_naturality A B f)

/-- The kernel isomorphism recovers the constructed comparison on all test schemes. -/
theorem kernelIso_hom_points (T : Over (Spec (CommRingCat.of A)))
    (x : T ⟶ (kernel (map A B f)).X) :
    x ≫ (kernelIso A B f).hom.hom.hom = kernelTestPointsEquiv A B f T x :=
  comp_isoOfPoints_hom _ _ T x

/-- The comparison identifies the actual restricted inclusion with the kernel inclusion. -/
theorem kernelIso_hom_inclusion :
    (kernelIso A B f).hom ≫ map A B (kernelι f) = kernelι (map A B f) := by
  apply hom_ext_points
  intro T x
  change x ≫ ((kernelIso A B f).hom.hom.hom ≫
    (map A B (kernelι f)).hom.hom) = x ≫ (kernelι (map A B f)).hom.hom
  rw [← Category.assoc, kernelIso_hom_points]
  apply (testPointsEquiv A B G T).injective
  calc
    _ = testPointsEquiv A B (kernel f) T (kernelTestPointsEquiv A B f T x) ≫
        (kernelι f).hom.hom :=
      Corepresented.groupSchemeMap_points (corepresentableBy A B (kernel f))
        (corepresentableBy A B G) (pointTransformation A B (kernelι f)) _
    _ = _ := kernelTestPointsEquiv_inclusion A B f T x

end Langlands.GroupScheme.AffineWeil
