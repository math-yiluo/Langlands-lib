import Langlands.GroupScheme.Rational.VectorQuotientConjugation
import Langlands.GroupScheme.SubgroupPreimageKernel
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Actual torus lifts through vector quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SubgroupPreimage

variable {k : Type u} [Field k]
    {G V Q H : GroupScheme (Spec (CommRingCat.of k))}
    (n : V ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q) (j : H ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))

include hn in
/-- The actual full kernel of an inverse-image projection has the same vector
dimension as the original full kernel presentation. -/
theorem isVectorGroupOfDimension_kernel {d : ℕ}
    (hV : RelativeRoot.IsVectorGroupOfDimension V d) :
    RelativeRoot.IsVectorGroupOfDimension (kernel (projection q j)) d := by
  have hrep : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy n :=
    ⟨inferInstance, hn⟩
  let e : V ≅ kernel q :=
    hrep.isoOfIsRepresentedBy ⟨inferInstance, rfl⟩
  exact RelativeRoot.IsVectorGroupOfDimension.of_iso
    (e ≪≫ (kernelIso q j).symm) hV

end SubgroupPreimage

variable {k : Type u} [Field k]
    {G V Q H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (n : V ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {d : ℕ} (hV : RelativeRoot.IsVectorGroupOfDimension V d)
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (j : H ⟶ Q) (hj : IsClosedSubgroup j) (hH : IsTorus H)

include hn hV hlinear hj hH in
/-- Pulling the quotient back to a closed torus and splitting its actual vector
kernel gives a homomorphic lift over the original field. -/
theorem IsTorus.exists_vectorQuotientLift :
    ∃ l : H ⟶ G, l ≫ q = j := by
  let : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  let : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
  let : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  let : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have hK := SubgroupPreimage.isVectorGroupOfDimension_kernel n q j hn hV
  obtain ⟨s, hs⟩ := hH.exists_vectorExtensionSection
    (kernelι (SubgroupPreimage.projection q j))
    (SubgroupPreimage.projection q j) rfl hK hlinear
  refine ⟨s ≫ SubgroupPreimage.inclusion q j, ?_⟩
  rw [Category.assoc, subgroupIntersection_condition,
    ← Category.assoc, hs, Category.id_comp]

/-- A chosen actual group-scheme lift of a closed torus through a vector
quotient, retaining the exact torus-action linearization input. -/
def IsTorus.vectorQuotientLift : H ⟶ G :=
  Classical.choose (hH.exists_vectorQuotientLift n q hn hV hlinear j hj)

/-- The chosen homomorphism lifts the specified original quotient map. -/
theorem IsTorus.vectorQuotientLift_comp :
    hH.vectorQuotientLift n q hn hV hlinear j hj ≫ q = j :=
  Classical.choose_spec (hH.exists_vectorQuotientLift n q hn hV hlinear j hj)

end Langlands.GroupScheme
