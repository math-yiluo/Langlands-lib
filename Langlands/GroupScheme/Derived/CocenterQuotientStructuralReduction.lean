import Langlands.GroupScheme.Derived.CocenterTorusQuotientData
import Langlands.GroupScheme.Derived.CocenterQuotientStatement
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.SmoothConnectedKernelCocharacters
import Langlands.GroupScheme.DominantHomFlat

/-! # Cocenter existence from maximal-torus products and intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Epimorphism

variable {k : Type u} [Field k]
    {T Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A scheme-surjective homomorphism between field tori is an epimorphism
of actual group schemes. -/
theorem IsTorus.epi_of_surjective_hom
    (hT : IsTorus T) (hQ : IsTorus Q) (f : T ⟶ Q)
    (hf : Surjective f.hom.hom.left) : Epi f := by
  let : Smooth T.X.hom := hT.smooth
  let : Smooth Q.X.hom := hQ.smooth
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  let : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ
  let : IsAffineHom T.X.hom := inferInstance
  let : IsAffineHom Q.X.hom := inferInstance
  let : QuasiCompact f.hom.hom.left := inferInstance
  let : IsLocallyNoetherian Q.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q.X.hom
  let : IsReduced Q.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k Q.X.left Q.X.hom
  let : LocallyOfFiniteType (f.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  let : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left Q.X.hom
  let : Surjective f.hom.hom.left := hf
  let : IsDominant f.hom.hom.left := inferInstance
  let : Flat f.hom.hom.left := DominantHomFlat.flat_of_isDominant f
  let : Epi f.hom.hom := Over.epi_of_epi_left _
  exact (Grp.forget (Over (Spec (CommRingCat.of k)))).epi_of_epi_map
    (inferInstanceAs (Epi f.hom.hom))

end Epimorphism

/-- Maximal-torus product surjectivity and the torus property of the actual
derived intersection supply the exact cocenter quotient proposition. -/
theorem cocenterQuotientExistence_of_product_of_torus_intersections
    (hprod : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hinter : ∀ (k : Type u) [Field k]
      (G D : GroupScheme (Spec (CommRingCat.of k)))
      (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ G) (t : T.toGrp ⟶ G),
      IsConnectedReductive G → IsDerivedSubgroup d → IsMaximalTorus t →
        IsTorus (subgroupIntersection t d)) :
    CocenterQuotientExistenceStatement.{u} := by
  intro k _ G D d hG hd
  let C := cocenterTorusQuotientData hprod hG hd
  let Q := C.1
  let q := C.2.1
  have hC := C.2.2
  let : IsAffineHom Q.X.hom := hC.2.1
  refine ⟨Q, q, isAffine_of_isAffineHom Q.X.hom, hC.2.2.1, hC.2.2.2.1, ?_⟩
  intro T t ht E _ _ hTE
  have hQE := (hC.2.2.2.2 T t ht).2 E hTE
  refine ⟨hQE, ?_⟩
  let b := GaloisPointComparison.baseMap k E
  let F := GroupScheme.baseChange b
  let f : T ⟶ Q := Additive.ofMul (t ≫ q)
  let fE := (CommGroupScheme.baseChange b).map f
  have hf : Surjective (t ≫ q).hom.hom.left := (hC.2.2.2.2 T t ht).1
  let : Surjective (t ≫ q).hom.hom.left := hf
  have hfE : Surjective (F.map (t ≫ q)).hom.hom.left :=
    MorphismProperty.of_isPullback
      (baseChange_map_isPullback b (t ≫ q)).flip inferInstance
  let : Epi (CommGroupScheme.groupHom fE) :=
    hTE.isTorus.epi_of_surjective_hom hQE.isTorus (F.map (t ≫ q)) hfE
  have hK : IsTorus (kernel (F.map (t ≫ q))) :=
    isTorus_kernel_comp_baseChange_of_isTorus_intersection
      t d q hd.1 hC.2.2.1.2.2.2 (hinter k G D T d t hG hd ht) E
  let : Smooth (kernel (CommGroupScheme.groupHom fE)).X.hom := hK.smooth
  let : ConnectedSpace (kernel (CommGroupScheme.groupHom fE)).X.left := hK.connectedSpace
  exact hTE.cocharacter_surjective_of_smooth_connected_kernel hQE fE

/-- Choose actual cocenter quotient data, including integral cocharacter
surjectivity, under the two explicit structural inputs. -/
def cocenterQuotientDataOfStructuralInputs
    (hprod : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hinter : ∀ (k : Type u) [Field k]
      (G D : GroupScheme (Spec (CommRingCat.of k)))
      (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ G) (t : T.toGrp ⟶ G),
      IsConnectedReductive G → IsDerivedSubgroup d → IsMaximalTorus t →
        IsTorus (subgroupIntersection t d))
    {k : Type u} [Field k] {G D : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ G) (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d) :
    Σ (Q : CommGroupScheme (Spec (CommRingCat.of k))),
      {q : G ⟶ Q.toGrp //
        IsAffine Q.X.left ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q ∧
        IsTorus Q.toGrp ∧
        ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
          IsMaximalTorus t →
          ∀ (E : Type u) [Field E] [Algebra k E],
            IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp) →
            IsSplitTorus (GaloisPointComparison.baseChanged k E Q.toGrp) ∧
            Function.Surjective
              (fun ν : cocharacterLattice
                  ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)).obj T) =>
                ν ≫ (CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map
                  (Additive.ofMul (t ≫ q) : T ⟶ Q))} :=
  let h := cocenterQuotientExistence_of_product_of_torus_intersections
    hprod hinter k G D d hG hd
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme
