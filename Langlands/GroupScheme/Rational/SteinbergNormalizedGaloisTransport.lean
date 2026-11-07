import Langlands.GroupScheme.Rational.SteinbergSemilinearRootMaps
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness
import Langlands.GroupScheme.Lie.WeightSupportGalois
import Langlands.GroupScheme.Rational.SteinbergFactorGaloisTransport
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters

/-! # Normalization of actual semilinear simple-root transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (G : GroupScheme B)

theorem descentPoint_inv (U : Over S)
    (y : U ⟶ ((GroupScheme.baseChange b).obj G).X) :
    descentPoint b a ha G U y⁻¹ = (descentPoint b a ha G U y)⁻¹ := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj U)).injective
  rw [baseChangePointsEquiv_descentPoint, map_inv, map_inv,
    baseChangePointsEquiv_descentPoint, GrpObj.comp_inv]

/-- An actual torus comparison commutes with canonical ambient descent. -/
theorem descentPoint_comp_torusIso
    {T : CommGroupScheme B} {T' : CommGroupScheme S}
    (j : T.toGrp ⟶ G) (i : T'.toGrp ⟶ (GroupScheme.baseChange b).obj G)
    (e : T' ≅ (CommGroupScheme.baseChange b).obj T)
    (h : i = CommGroupScheme.groupHom e.hom ≫ (GroupScheme.baseChange b).map j)
    (U : Over S) (t : U ⟶ T'.X) :
    descentPoint b a ha G U (t ≫ i.hom.hom) =
      (descentPoint b a ha T.toGrp U
        (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫
          (CommGroupScheme.groupHom e.inv).hom.hom) ≫ i.hom.hom := by
  have hi : (GroupScheme.baseChange b).map j = CommGroupScheme.groupHom e.inv ≫ i := by
    exact RelativeRoot.inverse_transport_square e (Iso.refl _) (by simpa using h)
  calc
    _ = descentPoint b a ha T.toGrp U
        (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫
          ((GroupScheme.baseChange b).map j).hom.hom := by
      rw [h, Grp.comp_hom_hom, ← Category.assoc, descentPoint_comp_baseChange]
    _ = _ := by rw [hi, Grp.comp_hom_hom, Category.assoc]

end Descent

namespace RelativeRoot

theorem subgroup_changeTorus_eq {B : Scheme.{u}} {T T' : CommGroupScheme B}
    {G : GroupScheme B} {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
    (e : T ≅ T') (h : i = CommGroupScheme.groupHom e.hom ≫ j)
    (χ : characterLattice T) :
    subgroup j (characterLattice.congr e χ) = subgroup i χ := by
  have hs : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom e.hom ≫ j := by
    simpa only [Iso.refl_hom, Category.comp_id] using h
  have he := subgroup_comap_of_transport e (Iso.refl G) hs χ
  ext U g
  exact eq_iff_iff.mp (by
    simpa only [SubgroupFunctor.mem_comap, Iso.refl_hom, Grp.id_hom_hom,
      Category.comp_id] using congrArg (fun F : SubgroupFunctor G => g ∈ F.carrier U) he)

end RelativeRoot

namespace VectorGroup

/-- Character transport expressed after an actual comparison of acting tori. -/
theorem charValue_galois_congr (k K : Type u) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {T' : CommGroupScheme (Spec (CommRingCat.of K))}
    (e : T' ≅ (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    (χ χ' : characterLattice T')
    (hχ : characterLattice.congr e χ' =
      characterLattice.galoisRepresentation k K T σ (characterLattice.congr e χ))
    (U : Over (Spec (CommRingCat.of K))) (t : U ⟶ T'.X) :
    charValue χ' U t =
      charValue χ ((Over.map (galoisBaseMap k K σ)).obj U)
        (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) T.toGrp U
            (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫
              (CommGroupScheme.groupHom e.inv).hom.hom) := by
  have h := characterLattice.galoisRepresentation_points k K T σ
    (characterLattice.congr e χ) U
    (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom)
  rw [← hχ] at h
  have h' := congrArg Units.val h
  change Units.val (Gm.pointsEquiv _ U
    (t ≫ (CommGroupScheme.groupHom (e.hom ≫ e.inv ≫ χ')).hom.hom)) =
      Units.val (Gm.pointsEquiv _ ((Over.map (galoisBaseMap k K σ)).obj U)
        (_ ≫ (CommGroupScheme.groupHom (e.inv ≫ χ)).hom.hom)) at h'
  rw [Iso.hom_inv_id_assoc] at h'
  exact h'

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (σ : K ≃ₐ[k] K)
    (f : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)

/-- Compatibility of whole additive-line homomorphisms with canonical descent,
on every scheme test and every global scalar. -/
def ScalarDescentCompatible
    (f' : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) : Prop :=
    ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (scalarPoint (CommRingCat.of K) U z ≫ f'.hom.hom) =
        scalarPoint (CommRingCat.of K) ((Over.map (galoisBaseMap k K σ)).obj U) z ≫
          f.hom.hom

/-- An all-test scalar descent law yields the formula on the twisted affine test.
The two homomorphisms remain opaque throughout the proof. -/
theorem galoisTestPoint_of_scalar_descent
    (f' : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (scalarPoint (CommRingCat.of K) U z ≫ f'.hom.hom) =
        scalarPoint (CommRingCat.of K) ((Over.map (galoisBaseMap k K σ)).obj U) z ≫
          f.hom.hom)
    (A : Type u) [CommRing A] [Algebra K A] (c : A) :
    Lie.galoisTestPoint k K σ A G
        (scalarPoint (CommRingCat.of K) _
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫ f'.hom.hom) =
      scalarPoint (CommRingCat.of K) ((algSpec (CommRingCat.of K)).obj
        (op (CommAlgCat.of K (Lie.GaloisTestAlgebra σ A))))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫ f.hom.hom := by
  rw [Lie.galoisTestPoint, hf, ← Category.assoc, scalarPoint_comp]
  rfl

/-- Torus equivariance follows from the all-test scalar descent law, the
commuting inclusion square, and transport of the actual character. -/
theorem torus_equivariant_of_scalar_descent
    (f' : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (scalarPoint (CommRingCat.of K) U z ≫ f'.hom.hom) =
        scalarPoint (CommRingCat.of K) ((Over.map (galoisBaseMap k K σ)).obj U) z ≫
          f.hom.hom)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {T' : CommGroupScheme (Spec (CommRingCat.of K))}
    (j : T.toGrp ⟶ G)
    (i : T'.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (eT : T' ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : i = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (χ χ' : characterLattice T')
    (hχ : characterLattice.congr eT χ' =
      characterLattice.galoisRepresentation k K T σ (characterLattice.congr eT χ))
    (heq : ∀ (U : Over (Spec (CommRingCat.of K))) (t : U ⟶ T'.X)
      (z : Γ(U.left, ⊤)),
      (t ≫ i.hom.hom) * (scalarPoint (CommRingCat.of K) U z ≫ f.hom.hom) *
          (t ≫ i.hom.hom)⁻¹ =
        scalarPoint (CommRingCat.of K) U (charValue χ U t * z) ≫ f.hom.hom)
    (U : Over (Spec (CommRingCat.of K))) (t : U ⟶ T'.X) (z : Γ(U.left, ⊤)) :
    (t ≫ i.hom.hom) * (scalarPoint (CommRingCat.of K) U z ≫ f'.hom.hom) *
        (t ≫ i.hom.hom)⁻¹ =
      scalarPoint (CommRingCat.of K) U (charValue χ' U t * z) ≫ f'.hom.hom := by
  apply descentPoint_injective (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G U
  rw [descentPoint_mul, descentPoint_mul, descentPoint_inv,
    descentPoint_comp_torusIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G j i eT hT, hf, hf,
    charValue_galois_congr k K σ eT χ χ' hχ]
  exact heq ((Over.map (galoisBaseMap k K σ)).obj U)
    (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T.toGrp U
        (t ≫ (CommGroupScheme.groupHom eT.hom).hom.hom) ≫
          (CommGroupScheme.groupHom eT.inv).hom.hom) z

end VectorGroup

namespace SplitPinning.NormalizedRootParametrization

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : K ≃ₐ[k] K)

theorem galoisHom_galoisTestPoint (A : Type u) [CommRing A] [Algebra K A] (c : A) :
    Lie.galoisTestPoint k K σ A G
        (VectorGroup.scalarPoint (CommRingCat.of K) _
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫
            (x.galoisHom k K G σ).hom.hom) =
      x.point ((algSpec (CommRingCat.of K)).obj
        (op (CommAlgCat.of K (Lie.GaloisTestAlgebra σ A))))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) := by
  exact VectorGroup.galoisTestPoint_of_scalar_descent k K G σ x.hom
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ) A c

/-- On affine tests, the transported map evaluates the original coefficient
curve with the scalar structure twisted by the actual automorphism. -/
theorem galoisHom_affinePoint (A : Type u) [CommRing A]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A] (c : A) :
    Lie.affineBaseChangeEquiv k K G A
        (VectorGroup.scalarPoint (CommRingCat.of K) _
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫
            (x.galoisHom k K G σ).hom.hom) =
      Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => (c : Lie.GaloisTestAlgebra σ A)) :
          MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ A).restrictScalars k)
        (x.coefficientCurve k K G) := by
  calc
    _ = Lie.affineBaseChangeEquiv k K G (Lie.GaloisTestAlgebra σ A)
        (Lie.galoisTestPoint k K σ A G _) :=
      (Lie.affineBaseChangeEquiv_galoisTestPoint k K σ A G _).symm
    _ = _ := by
      rw [galoisHom_galoisTestPoint]
      exact (x.coefficientCurve_evaluate k K G (Lie.GaloisTestAlgebra σ A) c).symm

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    {c : p.base.support}
    (hroot : characterLattice.congr eT (p.rootDatum.root c) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root a)))

include hT hroot in
theorem galoisHom_represents_root :
    (RelativeRoot.subgroup p.inclusion (p.rootDatum.root c)).IsRepresentedBy
      (x.galoisHom k K G σ) := by
  have hsub (b : p.base.support) :
      RelativeRoot.subgroup p.inclusion (p.rootDatum.root b) =
        RelativeRoot.subgroup ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
          (characterLattice.congr eT (p.rootDatum.root b)) :=
    (RelativeRoot.subgroup_changeTorus_eq eT hT _).symm
  have h := x.galoisHom_represents k K G σ
  rw [hsub, RelativeRoot.subgroup_galoisTransport, ← hroot, ← hsub] at h
  exact h

include hT hroot in
theorem galoisHom_torus_equivariant
    (U : Over (Spec (CommRingCat.of K))) (t : U ⟶ p.torus.X) (z : Γ(U.left, ⊤)) :
    (t ≫ p.inclusion.hom.hom) *
        (VectorGroup.scalarPoint (CommRingCat.of K) U z ≫
          (x.galoisHom k K G σ).hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ =
      VectorGroup.scalarPoint (CommRingCat.of K) U
          (VectorGroup.charValue (p.rootDatum.root c) U t * z) ≫
        (x.galoisHom k K G σ).hom.hom := by
  exact VectorGroup.torus_equivariant_of_scalar_descent k K G σ x.hom
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ) j p.inclusion eT hT
    (p.rootDatum.root a) (p.rootDatum.root c) hroot x.torus_equivariant U t z

end SplitPinning.NormalizedRootParametrization

end Langlands.GroupScheme
