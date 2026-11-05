import Langlands.GroupScheme.Rational.CommutativeVectorSplitExtension
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.SplitKernelRetractGeometry

/-! # Actual products from split commutative group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CommutativeSplitProduct

variable {S : Scheme.{u}} {E V : GroupScheme S} [IsCommMonObj E.X]
    (q : E ⟶ V) (s : V ⟶ E) (hs : s ≫ q = 𝟙 V)

/-- The full scheme-theoretic kernel, with its inherited commutative group law. -/
abbrev complement : CommGroupScheme S where
  toGrp := kernel q

/-- Multiplication of a kernel point and a section point, on every scheme test. -/
def pointsEquiv (T : Over S) :
    (T ⟶ (kernel q ⊗ V).X) ≃* (T ⟶ E.X) :=
  (productPointsEquiv (kernel q) V T).trans
    (RelativeRoot.CommutativeVectorSplitExtension.splitPointEquiv
      (kernelι q) q rfl s hs T)

/-- The product decomposition commutes with every relative scheme morphism. -/
theorem pointsEquiv_naturality {T W : Over S} (f : W ⟶ T)
    (x : T ⟶ (kernel q ⊗ V).X) :
    pointsEquiv q s hs W (f ≫ x) = f ≫ pointsEquiv q s hs T x := by
  simp only [pointsEquiv, MulEquiv.trans_apply, productPointsEquiv_naturality]
  exact RelativeRoot.CommutativeVectorSplitExtension.splitPointEquiv_natural
    (kernelι q) q rfl s hs f _

/-- A split homomorphism from a commutative group gives an actual product isomorphism. -/
def iso : kernel q ⊗ V ≅ E :=
  isoOfPoints (pointsEquiv q s hs) (pointsEquiv_naturality q s hs)

/-- The actual isomorphism is multiplication of the two factor images on all tests. -/
theorem iso_hom_points (T : Over S) (x : T ⟶ (kernel q ⊗ V).X) :
    x ≫ (iso q s hs).hom.hom.hom =
      ((x ≫ fst (kernel q).X V.X) ≫ (kernelι q).hom.hom) *
        ((x ≫ snd (kernel q).X V.X) ≫ s.hom.hom) := by
  exact comp_isoOfPoints_hom (pointsEquiv q s hs) (pointsEquiv_naturality q s hs) T x

/-- The same decomposition with the section factor first. -/
def factorIso : E ≅ V ⊗ (complement q).toGrp :=
  (iso q s hs).symm ≪≫ β_ (kernel q) V

/-- A split kernel inherits smoothness, affineness and connectedness from its source. -/
theorem complement_geometry {R : CommRingCat.{u}} [IsNoetherianRing R]
    {E V : GroupScheme (Spec R)} [IsCommMonObj E.X]
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    [IsSeparated V.X.hom] (q : E ⟶ V) (s : V ⟶ E) (hs : s ≫ q = 𝟙 V) :
    Smooth (complement q).X.hom ∧ IsAffineHom (complement q).X.hom ∧
      ConnectedSpace (complement q).X.left := by
  have h := SplitKernelRetract.smooth_connected_kernel q (𝟙 V) q s
    (Category.comp_id q) hs
  refine ⟨h.1, ?_, h.2⟩
  change IsAffineHom (kernel q).X.hom
  rw [← (kernelι q).hom.hom.w]
  infer_instance

end Langlands.GroupScheme.CommutativeSplitProduct
