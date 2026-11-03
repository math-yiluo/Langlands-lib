import Langlands.GroupScheme.Absolute.LaurentGaloisDescent
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.GmEndomorphismsProof
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Descent of invariant cocharacters of affine group schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.GaloisCocharacterDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Extension of Laurent coefficients as an algebra map over the original field. -/
def extendAlg : LaurentPolynomial k →ₐ[k] LaurentPolynomial K where
  __ := LaurentGaloisDescent.extend k K
  commutes' r := by
    change AddMonoidAlgebra.mapRingHom ℤ (algebraMap k K)
      (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 (algebraMap k K r)
    exact AddMonoidAlgebra.mapRingHom_single _ _ _

/-- Galois conjugation of Laurent coefficients fixes the original scalar field. -/
def conjugateAlg (σ : K ≃ₐ[k] K) :
    LaurentPolynomial K →ₐ[k] LaurentPolynomial K where
  __ := LaurentGaloisDescent.conjugate k K σ
  commutes' r := by
    change AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom
      (AddMonoidAlgebra.single 0 (algebraMap k K r)) =
        AddMonoidAlgebra.single 0 (algebraMap k K r)
    rw [AddMonoidAlgebra.mapRingHom_single]
    change AddMonoidAlgebra.single 0 (σ (algebraMap k K r)) = _
    rw [σ.commutes]


/-- The Laurent test scheme with its scalar structure restricted to `k`. -/
def laurentBaseIso :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) (LaurentPolynomial K))) ≅
      (Over.map (algebraBaseMap k K)).obj (Gm.relativeLaurent (CommRingCat.of K)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of (LaurentPolynomial K)))) (by
    change 𝟙 _ ≫
      (Spec.map (CommRingCat.ofHom LaurentPolynomial.C) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial K)))
    rw [Category.id_comp, ← Spec.map_comp]
    rfl)



/-- Conjugating Laurent coefficients changes only the extension-field structure of the test. -/
def conjugateTest (σ : K ≃ₐ[k] K) :
    (Over.map (galoisBaseMap k K σ)).obj (Gm.relativeLaurent (CommRingCat.of K)) ⟶
      Gm.relativeLaurent (CommRingCat.of K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.conjugate k K σ))) (by
    change Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.conjugate k K σ)) ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C) =
        Spec.map (CommRingCat.ofHom LaurentPolynomial.C) ≫
          Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact AddMonoidAlgebra.mapRingHom_single σ.toRingHom 0 r)

/-- The universal unit is unchanged by conjugating the coefficient field. -/
theorem conjugateTest_universalUnit (σ : K ≃ₐ[k] K) :
    Gm.pointsEquiv _ _
      (conjugateTest k K σ ≫ Gm.laurentPoint K) =
        Gm.pointsEquiv _ _ (Gm.laurentPoint K) := by
  rw [Gm.pointsEquiv_naturality]
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial K))).commRingCatIsoToRingEquiv.injective
  change ((Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.conjugate k K σ))).appTop ≫
    (Scheme.ΓSpecIso _).hom) _ = (Scheme.ΓSpecIso _).hom _
  rw [Scheme.ΓSpecIso_naturality]
  change LaurentGaloisDescent.conjugate k K σ
    (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of K))
      (Gm.laurentPoint K) : LaurentPolynomial K) =
    (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of K))
      (Gm.laurentPoint K) : LaurentPolynomial K)
  have hp :
      (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of K))
        (Gm.laurentPoint K) : LaurentPolynomial K) = LaurentPolynomial.T 1 :=
    Gm.affinePointsEquiv_universalPoint (CommRingCat.of K)
  rw [hp]
  exact AddMonoidAlgebra.mapRingHom_single σ.toRingHom 1 1 |>.trans
    (by rw [map_one]; rfl)

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- A cocharacter over `K`, evaluated on the universal Laurent unit and viewed over `k`. -/
def universalValue
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) :
    Lie.AffinePoints G (LaurentPolynomial K) :=
  (laurentBaseIso k K).hom ≫ baseChangePointsEquiv (algebraBaseMap k K) G _
    (Gm.laurentPoint K ≫ ν.hom.hom)

theorem universalValue_eq
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) :
    universalValue k K G ν =
      (laurentBaseIso k K).hom ≫
        baseChangePointsEquiv (algebraBaseMap k K) G
          (Gm.relativeLaurent (CommRingCat.of K)) (Gm.laurentPoint K ≫ ν.hom.hom) := rfl

/-- The Laurent coordinates of an actual cocharacter over the extension field. -/
def coordinates [IsAffineHom G.X.hom]
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) :
    Lie.coordinateAlgebra G →ₐ[k] LaurentPolynomial K :=
  Lie.pointCoordinates G (universalValue k K G ν)

/-- The canonical change of test structure is Laurent coefficient conjugation over `k`. -/
theorem conjugateTest_over_base (σ : K ≃ₐ[k] K) :
    (laurentBaseIso k K).hom ≫
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (Gm.relativeLaurent (CommRingCat.of K))).hom ≫
      (Over.map (algebraBaseMap k K)).map (conjugateTest k K σ) =
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (conjugateAlg k K σ)).op ≫
          (laurentBaseIso k K).hom := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.conjugate k K σ)) =
      Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.conjugate k K σ)) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- The changed test structure evaluates the universal point at the same unit. -/
theorem conjugateTest_universalPoint (σ : K ≃ₐ[k] K) :
    (Gm.pointsEquiv (Spec (CommRingCat.of K))
      ((Over.map (galoisBaseMap k K σ)).obj
        (Gm.relativeLaurent (CommRingCat.of K)))).symm
      (Gm.pointsEquiv (Spec (CommRingCat.of K))
        (Gm.relativeLaurent (CommRingCat.of K))
        (Gm.laurentPoint K)) =
      conjugateTest k K σ ≫ Gm.laurentPoint K :=
  (Gm.pointsEquiv _ _).injective (by
    rw [MulEquiv.apply_symm_apply, conjugateTest_universalUnit]
    rfl)

/-- The universal value after transport, before the affine-test identification. -/
theorem universalProjection_transport
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) (σ : K ≃ₐ[k] K) :
    baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
      (Gm.laurentPoint K ≫
        (transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G ν).hom.hom) =
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (Gm.relativeLaurent (CommRingCat.of K))).hom ≫
      (Over.map (algebraBaseMap k K)).map (conjugateTest k K σ) ≫
      baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
        (Gm.laurentPoint K ≫ ν.hom.hom) := by
  rw [transportCocharacter_points, conjugateTest_universalPoint,
    Category.assoc, baseChangePointsEquiv_naturality]

/-- The coefficient-conjugation comparison after any map to the original group. -/
theorem conjugateValue (σ : K ≃ₐ[k] K)
    (x : (Over.map (algebraBaseMap k K)).obj
      (Gm.relativeLaurent (CommRingCat.of K)) ⟶ G.X) :
    (laurentBaseIso k K).hom ≫
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (Gm.relativeLaurent (CommRingCat.of K))).hom ≫
      (Over.map (algebraBaseMap k K)).map (conjugateTest k K σ) ≫ x =
      Lie.affineMap G (conjugateAlg k K σ) ((laurentBaseIso k K).hom ≫ x) := by
  simpa only [Category.assoc, Lie.affineMap_apply] using
    congrArg (fun f => f ≫ x) (conjugateTest_over_base k K σ)

/-- A comparison of projected Laurent points gives the same comparison of affine values. -/
theorem universalValue_of_projection
    (ν ν' : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) (σ : K ≃ₐ[k] K) :
    baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
      (Gm.laurentPoint K ≫ ν'.hom.hom) =
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (Gm.relativeLaurent (CommRingCat.of K))).hom ≫
      (Over.map (algebraBaseMap k K)).map (conjugateTest k K σ) ≫
      baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
        (Gm.laurentPoint K ≫ ν.hom.hom) →
    universalValue k K G ν' =
      Lie.affineMap G (conjugateAlg k K σ) (universalValue k K G ν) := by
  intro h
  exact (universalValue_eq k K G ν').trans
    (((congrArg (fun p => (laurentBaseIso k K).hom ≫ p)
      h).trans
        (conjugateValue k K G σ _)).trans
          (congrArg (Lie.affineMap G (conjugateAlg k K σ))
            (universalValue_eq k K G ν).symm))

/-- Invariance under the published transport fixes every Laurent coordinate. -/
theorem coordinates_fixed [IsAffineHom G.X.hom]
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hν : ∀ σ : K ≃ₐ[k] K,
      transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G ν = ν) :
    ∀ (σ : K ≃ₐ[k] K) (c : Lie.coordinateAlgebra G),
      LaurentGaloisDescent.conjugate k K σ (coordinates k K G ν c) =
        coordinates k K G ν c := by
  intro σ c
  have hp := universalProjection_transport k K G ν σ
  rw [hν σ] at hp
  have h := congrArg (fun x => Lie.pointCoordinates G x c)
    (universalValue_of_projection k K G ν ν σ hp)
  rw [Lie.pointCoordinates_naturality] at h
  exact h.symm

/-- Invariance under the existing geometric transport of cocharacters. -/
def IsInvariant
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) : Prop :=
  ∀ σ : K ≃ₐ[k] K,
    transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G ν = ν

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom G.X.hom]
  (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  (hν : IsInvariant k K G ν)

/-- The Laurent coordinate map descended coefficient by coefficient. -/
def descendedCoordinates : Lie.coordinateAlgebra G →ₐ[k] LaurentPolynomial k :=
  LaurentGaloisDescent.descendAlgHom k K (coordinates k K G ν)
    (coordinates_fixed k K G ν hν)

theorem extend_comp_descendedCoordinates :
    (extendAlg k K).comp (descendedCoordinates k K G ν hν) = coordinates k K G ν := by
  apply AlgHom.ext
  intro c
  exact LaurentGaloisDescent.extend_descendAlgHom k K
    (coordinates k K G ν) (coordinates_fixed k K G ν hν) c

/-- The descended coordinates as an actual affine Laurent point of the original group. -/
def descendedPoint : Lie.AffinePoints G (LaurentPolynomial k) :=
  (Lie.pointCoordinates G).symm (descendedCoordinates k K G ν hν)

theorem pointCoordinates_descendedPoint :
    Lie.pointCoordinates G (descendedPoint k K G ν hν) =
      descendedCoordinates k K G ν hν :=
  (Lie.pointCoordinates G).apply_symm_apply _

/-- Extending the descended point recovers the given cocharacter on the universal unit. -/
theorem extend_descendedPoint :
    Lie.affineMap G (extendAlg k K) (descendedPoint k K G ν hν) =
      universalValue k K G ν := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, pointCoordinates_descendedPoint,
    extend_comp_descendedCoordinates]
  rfl

/-- The affine algebra test and the relative Laurent test over the original field agree. -/
def laurentAffineIso :
    (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (LaurentPolynomial k))) ≅
      Gm.relativeLaurent (CommRingCat.of k) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of (LaurentPolynomial k)))) (by rfl)

/-- The scheme morphism obtained from the descended Laurent point. -/
def descendedMorphism : (Gm (Spec (CommRingCat.of k))).X ⟶ G.X :=
  (Gm.relativeLaurentIso (CommRingCat.of k)).hom ≫
    (laurentAffineIso k).inv ≫ descendedPoint k K G ν hν

theorem laurentPoint_descendedMorphism :
    Gm.laurentPoint k ≫ descendedMorphism k K G ν hν =
      (laurentAffineIso k).inv ≫ descendedPoint k K G ν hν := by
  simp only [descendedMorphism, Gm.laurentPoint, Iso.inv_hom_id_assoc]

end Langlands.GroupScheme.GaloisCocharacterDescent
