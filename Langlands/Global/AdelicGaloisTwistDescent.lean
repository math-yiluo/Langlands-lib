import Langlands.Global.AdelicGaloisTwistMap

/-! # Canonical descent of Galois-twisted adelic points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L]

/-- The adelic test object of `L` over `Spec L`. -/
abbrev adeleTest : Over (Spec (CommRingCat.of L)) :=
  (algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L (Adeles L)))

omit [NumberField F] [FiniteDimensional F L] in
theorem adeleTest_hom :
    (adeleTest L).hom = Spec.map (CommRingCat.ofHom (algebraMap L (Adeles L))) := rfl

/-- `Spec` of the Galois automorphism of `𝔸_L`, as an isomorphism from the adelic test
object with its structure twisted by `Spec σ` to the adelic test object. -/
def adeleTestIso (σ : L ≃ₐ[F] L) :
    (Over.map (galoisBaseMap F L σ)).obj (adeleTest L) ≅ adeleTest L :=
  Over.isoMk (Scheme.Spec.mapIso (AdeleGalois.ringEquiv F L σ).toCommRingCatIso.op) (by
    change Spec.map (CommRingCat.ofHom (AdeleGalois.ringEquiv F L σ : Adeles L →+* Adeles L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L (Adeles L))) =
      Spec.map (CommRingCat.ofHom (algebraMap L (Adeles L))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact AdeleGalois.ringEquiv_algebraMap σ a)

omit [FiniteDimensional F L] in
theorem adeleTestIso_hom_left (σ : L ≃ₐ[F] L) :
    (adeleTestIso F L σ).hom.left =
      Spec.map (CommRingCat.ofHom (AdeleGalois.ringEquiv F L σ : Adeles L →+* Adeles L)) :=
  rfl

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Tensor points, seen on the ground group, are restricted along the tensor map. -/
theorem tensorAdelicEquiv_left_fst (q : G.affinePoints (CommAlgCat.of F (L ⊗[F] Adeles F))) :
    (tensorAdelicEquiv F L G q).left ≫ pullback.fst G.X.hom (Spec.algebraMap F L) =
      Spec.map (CommRingCat.ofHom
        (numberFieldAdeleTensorMap F L : L ⊗[F] Adeles F →+* Adeles L)) ≫ q.left := by
  rw [tensorAdelicEquiv_apply, affinePointMap_apply]
  have h := affinePointsBaseChangeMulEquiv_symm_left F L (L ⊗[F] Adeles F) G
    (affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G q)
  rw [MulEquiv.symm_apply_apply] at h
  rw [Over.comp_left, Category.assoc, ← h]
  rfl

/-- Lemma S: on the ground group, the twist is restriction along `Spec σ̃`. -/
theorem galoisTwist_left_fst (σ : L ≃ₐ[F] L)
    (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) :
    (galoisTwist F L G σ x).left ≫ pullback.fst G.X.hom (Spec.algebraMap F L) =
      (adeleTestIso F L σ).hom.left ≫ x.left ≫ pullback.fst G.X.hom (Spec.algebraMap F L) := by
  obtain ⟨p, rfl⟩ := (tensorAdelicEquiv F L G).surjective x
  rw [galoisTwist_tensorAdelicEquiv, tensorAdelicEquiv_left_fst, tensorAdelicEquiv_left_fst,
    TensorGaloisPoint.conjugate, Lie.affineMap_apply, Over.comp_left, adeleTestIso_hom_left,
    ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext y
  change numberFieldAdeleTensorMap F L (TensorGaloisPoint.coefficientConjugate F L (Adeles F) σ y) =
    AdeleGalois.ringEquiv F L σ (numberFieldAdeleTensorMap F L y)
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorGaloisPoint.coefficientConjugate_tmul]
    exact (AdeleGalois.ringEquiv_tensor σ a b).symm
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Canonical descent of a twisted adelic point is restriction along `Spec σ̃`. -/
theorem descentPoint_galoisTwist (σ : L ≃ₐ[F] L)
    (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) :
    descentPoint (algebraBaseMap F L) (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
        (adeleTest L) (galoisTwist F L G σ x) = (adeleTestIso F L σ).hom ≫ x := by
  apply (baseChangePointsEquiv (algebraBaseMap F L) G
    ((Over.map (galoisBaseMap F L σ)).obj (adeleTest L))).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_naturality]
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((galoisTwist F L G σ x).left ≫ pullback.fst G.X.hom (algebraBaseMap F L)) =
    (adeleTestIso F L σ).hom.left ≫ x.left ≫ pullback.fst G.X.hom (algebraBaseMap F L)
  rw [Category.id_comp]
  exact galoisTwist_left_fst F L G σ x

section Generic

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (H : GroupScheme B)

/-- Canonical descent of a point composed with the descent identification is the
pullback adjunction along the base endomorphism. -/
theorem descentPoint_comp_descentBaseChangeIso (T : Over S)
    (y : T ⟶ ((Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj H)).X) :
    descentPoint b a ha H T (y ≫ (descentBaseChangeIso b a ha H).hom.hom.hom) =
      baseChangePointsEquiv a ((Over.pullback b).mapGrp.obj H) T y := by
  apply (baseChangePointsEquiv b H ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_descent, Iso.inv_hom_id_assoc]

/-- A point is the canonical translate of a subgroup point once their canonical descents
agree. -/
theorem comp_descentHom_of_descentPoint (T : Over S) {K : GroupScheme S}
    (j : K ⟶ (Over.pullback b).mapGrp.obj H) (q : T ⟶ ((Over.pullback a).mapGrp.obj K).X)
    (y : T ⟶ ((Over.pullback b).mapGrp.obj H).X)
    (h : descentPoint b a ha H T y = baseChangePointsEquiv a K T q ≫ j.hom.hom) :
    q ≫ ((Over.pullback a).mapGrp.map j ≫ (descentBaseChangeIso b a ha H).hom).hom.hom = y := by
  apply descentPoint_injective b a ha H T
  rw [h, Grp.comp_hom_hom, ← Category.assoc, descentPoint_comp_descentBaseChangeIso,
    baseChangePointsEquiv_comp]

/-- The same statement for an arbitrary morphism `φ` equal to the canonical translate of `j`.
Keeping `φ` abstract lets concrete instances (such as `radicalGaloisHom`) be used without the
kernel unfolding the descent identification. -/
theorem comp_eq_of_descentPoint (T : Over S) {K : GroupScheme S}
    (j : K ⟶ (GroupScheme.baseChange b).obj H)
    (φ : (GroupScheme.baseChange a).obj K ⟶ (GroupScheme.baseChange b).obj H)
    (hφ : φ = (GroupScheme.baseChange a).map j ≫ (descentBaseChangeIso b a ha H).hom)
    (q : T ⟶ ((GroupScheme.baseChange a).obj K).X)
    (y : T ⟶ ((GroupScheme.baseChange b).obj H).X)
    (h : descentPoint b a ha H T y = baseChangePointsEquiv a K T q ≫ j.hom.hom) :
    q ≫ φ.hom.hom = y := by
  subst hφ
  exact comp_descentHom_of_descentPoint b a ha H T j q y h

end Generic

/-- The Galois translate of an upper adelic point of an `L`-group `H`: the same point,
restricted along `Spec σ̃`, on the base change of `H` along `Spec σ`. -/
def twistPoint (σ : L ≃ₐ[F] L) (H : GroupScheme (Spec (CommRingCat.of L)))
    (p : adeleTest L ⟶ H.X) :
    adeleTest L ⟶ ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj H).X :=
  (baseChangePointsEquiv (galoisBaseMap F L σ) H (adeleTest L)).symm
    ((adeleTestIso F L σ).hom ≫ p)

omit [FiniteDimensional F L] in
theorem baseChangePointsEquiv_twistPoint (σ : L ≃ₐ[F] L)
    (H : GroupScheme (Spec (CommRingCat.of L))) (p : adeleTest L ⟶ H.X) :
    baseChangePointsEquiv (galoisBaseMap F L σ) H (adeleTest L) (twistPoint F L σ H p) =
      (adeleTestIso F L σ).hom ≫ p :=
  MulEquiv.apply_symm_apply _ _

theorem descentPoint_galoisTwist_comp (σ : L ≃ₐ[F] L)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (j : H ⟶ AffineWeil.unitBaseChange F L G) (p : adeleTest L ⟶ H.X) :
    descentPoint (algebraBaseMap F L) (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
        (adeleTest L) (galoisTwist F L G σ (p ≫ j.hom.hom)) =
      baseChangePointsEquiv (galoisBaseMap F L σ) H (adeleTest L) (twistPoint F L σ H p) ≫
        j.hom.hom := by
  rw [descentPoint_galoisTwist, baseChangePointsEquiv_twistPoint, Category.assoc]

/-- D1: the Galois twist of a point of a subgroup is the twisted point of the canonical
Galois translate of the subgroup. -/
theorem twistPoint_comp_radicalGaloisHom (σ : L ≃ₐ[F] L)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (j : H ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G) (p : adeleTest L ⟶ H.X) :
    twistPoint F L σ H p ≫ (radicalGaloisHom j σ).hom.hom =
      galoisTwist F L G σ (p ≫ j.hom.hom) :=
  comp_eq_of_descentPoint (algebraBaseMap F L) (galoisBaseMap F L σ) (galoisBaseMap_over F L σ)
    G (adeleTest L) j (radicalGaloisHom j σ) rfl _ _ (descentPoint_galoisTwist_comp F L G σ j p)

end Langlands.Global.AdelicGaloisUnit
