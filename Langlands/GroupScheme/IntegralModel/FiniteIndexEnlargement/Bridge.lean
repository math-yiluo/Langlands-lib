import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.HopfMorphismBaseChange
import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Hopf-coordinate bridge for finite-index enlargement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Coordinates

variable {R : Type u} [CommRing R]
  (P : GroupScheme (Spec (CommRingCat.of R)))
  (A : CommHopfAlgCat.{u} R)
  (e : (hopfSpec (CommRingCat.of R)).obj (op A) ≅ P)

/-- Algebra-valued Hopf-coordinate points are actual points of the affine group. -/
def coordinatePointEquiv (S : Type u) [CommRing S] [Algebra R S] :
    WithConv (A →ₐ[R] S) ≃*
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶ P.X) :=
  (Spec.mapMulEquiv (R := R) (S := A) (T := S)).trans
    ((yonedaGrp.mapIso e).app
      (op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))))).groupIsoToMulEquiv

/-- The equivalence sends an algebra map to its spectrum followed by the coordinate isomorphism. -/
theorem coordinatePointEquiv_left (S : Type u) [CommRing S] [Algebra R S]
    (φ : A →ₐ[R] S) :
    (coordinatePointEquiv P A e S (toConv φ)).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        e.hom.hom.hom.left := rfl

/-- The two presentations of the base scheme over itself are canonically isomorphic. -/
def basePointIso (R : Type u) [CommRing R] :
    Over.mk (𝟙 (Spec (CommRingCat.of R))) ≅
      (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R)) :=
  Over.isoMk (Iso.refl _) (by simp [specOverSpec_over])

/-- Integral sections are the base-ring-valued coordinate points. -/
def sectionEquiv : rationalPoints P ≃* WithConv (A →ₐ[R] R) :=
  ((P.points.mapIso (basePointIso R).symm.op).groupIsoToMulEquiv).trans
    (coordinatePointEquiv P A e R).symm

/-- Coordinate evaluation of an integral section, written as an equality of scheme maps. -/
theorem sectionEquiv_spec (x : rationalPoints P) :
    Spec.map (CommRingCat.ofHom (sectionEquiv P A e x).ofConv.toRingHom) ≫
        e.hom.hom.hom.left = x.left := by
  have h := congrArg (fun y => y.left)
    ((coordinatePointEquiv P A e R).apply_symm_apply
      ((P.points.mapIso (basePointIso R).symm.op).groupIsoToMulEquiv x))
  exact h

end Coordinates

section Model

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A : CommHopfAlgCat.{u} R)
  (e : (hopfSpec (CommRingCat.of R)).obj (op A) ≅ M.group)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

/-- Evaluation of generic points in the Hopf coordinates of the original model. -/
def evaluationEquiv : rationalPoints G ≃*
    WithConv (A →ₐ[R] K) :=
  (((yonedaGrp.mapIso M.genericIso.symm).app
      (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))).groupIsoToMulEquiv.trans
    (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group)).trans
    (coordinatePointEquiv M.group A e K).symm

/-- The spectrum of evaluation is the original-model projection of the generic point. -/
theorem evaluationEquiv_spec (g : rationalPoints G) :
    Spec.map (CommRingCat.ofHom (evaluationEquiv M A e g).ofConv.toRingHom) ≫
        e.hom.hom.hom.left =
      g.left ≫ M.genericIso.inv.hom.hom.left ≫
        pullback.fst M.group.X.hom (Spec.algebraMap R K) := by
  have h := congrArg (fun y => y.left)
    ((coordinatePointEquiv M.group A e K).apply_symm_apply
      (baseChangeBasePointsEquiv (Spec.algebraMap R K) M.group
        (g ≫ M.genericIso.inv.hom.hom)))
  exact h.trans (baseChangeBasePointsEquiv_left _ _ _)

/-- The generic evaluation of an integral section is scalar extension of its
base-ring coordinate map. -/
theorem evaluationEquiv_integralPointMap (x : M.integralSections) :
    evaluationEquiv M A e (M.integralPointMap x) =
      toConv ((Algebra.ofId R K).comp (sectionEquiv M.group A e x).ofConv) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  have h : CommRingCat.ofHom (evaluationEquiv M A e (M.integralPointMap x)).ofConv.toRingHom =
      CommRingCat.ofHom
        (((Algebra.ofId R K).comp (sectionEquiv M.group A e x).ofConv).toRingHom) := by
    apply Spec.map_injective
    apply (cancel_mono e.hom.hom.hom.left).mp
    rw [evaluationEquiv_spec]
    have hi : M.genericIso.hom.hom.hom ≫ M.genericIso.inv.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) M.genericIso.hom_inv_id
    have hx : M.integralPointMap x ≫ M.genericIso.inv.hom.hom =
        baseChangeSectionHom (Spec.algebraMap R K) M.group x := by
      change (_ ≫ M.genericIso.hom.hom.hom) ≫ M.genericIso.inv.hom.hom = _
      rw [Category.assoc, hi, Category.comp_id]
    change (M.integralPointMap x ≫ M.genericIso.inv.hom.hom).left ≫
        pullback.fst M.group.X.hom (Spec.algebraMap R K) = _
    rw [hx, baseChangeSectionHom_fst]
    change _ = Spec.map (CommRingCat.ofHom
      ((algebraMap R K).comp (sectionEquiv M.group A e x).ofConv.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, sectionEquiv_spec]
  exact congrArg (fun f => f.hom) h

omit [IsDomain R] in
/-- Coordinate maps into the fraction field lift to the base ring exactly when
all their values lie in the base ring. -/
theorem exists_algHom_lift_iff {A : Type u} [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] K) :
    (∃ ψ : A →ₐ[R] R, (Algebra.ofId R K).comp ψ = φ) ↔
      ∀ a, φ a ∈ (algebraMap R K).range := by
  constructor
  · rintro ⟨ψ, rfl⟩ a
    exact ⟨ψ a, rfl⟩
  · intro h
    let e := AlgEquiv.ofInjective (Algebra.ofId R K) (IsFractionRing.injective R K)
    let ψ := e.symm.toAlgHom.comp
      (φ.codRestrict (Algebra.ofId R K).range h)
    refine ⟨ψ, ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply
      (φ.codRestrict (Algebra.ofId R K).range h a))

/-- Integral points are precisely the generic points whose coordinate values are integral. -/
theorem mem_integralPoints_iff (g : rationalPoints G) :
    g ∈ M.integralPoints ↔
      ∀ a, (evaluationEquiv M A e g).ofConv a ∈ (algebraMap R K).range := by
  rw [← exists_algHom_lift_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(sectionEquiv M.group A e x).ofConv,
      congrArg WithConv.ofConv (evaluationEquiv_integralPointMap M A e x).symm⟩
  · rintro ⟨ψ, hψ⟩
    refine ⟨(sectionEquiv M.group A e).symm (toConv ψ), ?_⟩
    apply (evaluationEquiv M A e).injective
    rw [evaluationEquiv_integralPointMap, MulEquiv.apply_symm_apply, hψ]

/-- The coordinate algebra of a smooth model is smooth. -/
theorem coordinate_smooth (hM : M.IsSmooth) :
    Algebra.Smooth R (AffineCoordinates.hopfAlgebra M.group) := by
  let : Smooth M.group.X.hom := hM
  have h : Smooth (((AffineCoordinates.hopfSpecIso M.group).hom.hom.hom).left ≫
      M.group.X.hom) := inferInstance
  rw [Over.w] at h
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap R (AffineCoordinates.hopfAlgebra M.group)))) at h
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)

/-- Flatness of the model is flatness of its Hopf-coordinate algebra. -/
theorem coordinate_flat : Module.Flat R (AffineCoordinates.hopfAlgebra M.group) := by
  have h : Flat (((AffineCoordinates.hopfSpecIso M.group).hom.hom.hom).left ≫
      M.group.X.hom) := inferInstance
  rw [Over.w] at h
  change Flat (Spec.map (CommRingCat.ofHom
    (algebraMap R (AffineCoordinates.hopfAlgebra M.group)))) at h
  exact RingHom.flat_algebraMap_iff.mp (HasRingHomProperty.Spec_iff.mp h)

end Model

section Reconstruction

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A : CommHopfAlgCat.{u} R)
  (e : (hopfSpec (CommRingCat.of R)).obj (op A) ≅ M.group)
  (B : CommHopfAlgCat.{u} R) (iB : B →ₐc[R] A)

/-- The map from the original model into the spectrum of a Hopf subalgebra. -/
def enlargementMap : M.group ⟶ (hopfSpec (CommRingCat.of R)).obj (op B) :=
  e.inv ≫ (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom iB).op

/-- A tensor-coordinate isomorphism makes the enlargement map an isomorphism
on the actual generic fibres. -/
theorem enlargementMap_generic_isIso
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom)) :
    IsIso ((baseChange (Spec.algebraMap R K)).map (enlargementMap M A e B iB)) := by
  let f := (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom iB).op
  have hf : IsIso (((baseChange (Spec.algebraMap R K)).map f).hom.hom.left) := by
    change IsIso
      (((Over.pullback (Spec.algebraMap R K)).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom iB.toAlgHom).op)).left)
    rw [HopfMorphismBaseChange.tensorSpecIso_naturality]
    let φ : CommRingCat.of (K ⊗[R] B) ⟶ CommRingCat.of (K ⊗[R] A) :=
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom).toRingHom
    let : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hiB
    infer_instance
  have : IsIso ((Over.forget _).map
      ((baseChange (Spec.algebraMap R K)).map f).hom.hom) := hf
  have : IsIso ((baseChange (Spec.algebraMap R K)).map f).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((baseChange (Spec.algebraMap R K)).map f) := by
    let ef := Grp.mkIso' (asIso ((baseChange (Spec.algebraMap R K)).map f).hom.hom)
    change IsIso ef.hom
    infer_instance
  dsimp only [enlargementMap]
  rw [Functor.map_comp]
  infer_instance

/-- A smooth Hopf algebra with the same generic coordinates defines an integral model. -/
def reconstructedModel
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B) : IntegralModel R K G := by
  let H := (hopfSpec (CommRingCat.of R)).obj (op B)
  have hsm : Smooth H.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hB)
  have ha : IsAffineHom H.X.hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    infer_instance
  let : IsIso ((baseChange (Spec.algebraMap R K)).map (enlargementMap M A e B iB)) :=
    enlargementMap_generic_isIso M A e B iB hiB
  exact
    { group := H
      genericIso :=
        (asIso ((baseChange (Spec.algebraMap R K)).map
          (enlargementMap M A e B iB))).symm ≪≫ M.genericIso }

/-- The original-to-enlarged map extends the identity on the specified generic group. -/
def reconstructedHom
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B) :
    M.Hom (reconstructedModel M A e B iB hiB hB) (𝟙 G) := by
  let : IsIso ((baseChange (Spec.algebraMap R K)).map (enlargementMap M A e B iB)) :=
    enlargementMap_generic_isIso M A e B iB hiB
  refine { hom := enlargementMap M A e B iB, generic_comm := ?_ }
  change _ ≫ (inv _ ≫ M.genericIso.hom) = M.genericIso.hom ≫ 𝟙 G
  simp

/-- Reconstruction retains smoothness of the Hopf algebra. -/
theorem reconstructedModel_isSmooth
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B) :
    (reconstructedModel M A e B iB hiB hB).IsSmooth := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hB)

/-- Reconstruction retains the open-immersion property of the coordinate inclusion. -/
theorem reconstructedHom_isOpenImmersion
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B)
    (hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom iB.toAlgHom.toRingHom))) :
    IsOpenImmersion (reconstructedHom M A e B iB hiB hB).hom.hom.hom.left := by
  let := hopen
  change IsOpenImmersion
    (e.inv.hom.hom.left ≫ Spec.map (CommRingCat.ofHom iB.toAlgHom.toRingHom))
  infer_instance

/-- Evaluation in the reconstructed model is restriction along the Hopf map. -/
theorem reconstructedModel_evaluationEquiv
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B) (g : rationalPoints G) :
    evaluationEquiv (reconstructedModel M A e B iB hiB hB) B (Iso.refl _) g =
      toConv ((evaluationEquiv M A e g).ofConv.comp iB.toAlgHom) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  have h : CommRingCat.ofHom
        (evaluationEquiv (reconstructedModel M A e B iB hiB hB) B
          (Iso.refl _) g).ofConv.toRingHom =
      CommRingCat.ofHom
        (((evaluationEquiv M A e g).ofConv.comp iB.toAlgHom).toRingHom) := by
    apply Spec.map_injective
    change _ = Spec.map (CommRingCat.ofHom
      ((evaluationEquiv M A e g).ofConv.toRingHom.comp iB.toAlgHom.toRingHom))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hN := evaluationEquiv_spec
      (reconstructedModel M A e B iB hiB hB) B (Iso.refl _) g
    change Spec.map _ ≫ 𝟙 _ = _ at hN
    rw [Category.comp_id] at hN
    rw [hN]
    change g.left ≫ (M.genericIso.inv.hom.hom.left ≫
        ((Over.pullback (Spec.algebraMap R K)).map
          (enlargementMap M A e B iB).hom.hom).left) ≫
        pullback.fst _ (Spec.algebraMap R K) = _
    simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, ← Category.assoc, Category.assoc g.left]
    rw [← evaluationEquiv_spec M A e g]
    change (Spec.map _ ≫ e.hom.hom.hom.left) ≫
        (e.inv.hom.hom.left ≫ Spec.map _) = _
    have he : e.hom.hom.hom.left ≫ e.inv.hom.hom.left = 𝟙 _ :=
      congrArg (fun f => f.hom.hom.left) e.hom_inv_id
    simp only [Category.assoc]
    rw [← Category.assoc e.hom.hom.hom.left, he, Category.id_comp]
    rfl
  exact congrArg (fun f => f.hom) h

/-- Reconstructed integral points test integrality on the included Hopf algebra. -/
theorem reconstructedModel_mem_integralPoints_iff
    (hiB : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) iB.toAlgHom))
    (hB : Algebra.Smooth R B) (g : rationalPoints G) :
    g ∈ (reconstructedModel M A e B iB hiB hB).integralPoints ↔
      ∀ b, (evaluationEquiv M A e g).ofConv (iB b) ∈
        (algebraMap R K).range := by
  rw [mem_integralPoints_iff
    (reconstructedModel M A e B iB hiB hB) B (Iso.refl _) g,
    reconstructedModel_evaluationEquiv]
  rfl

end Reconstruction

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
