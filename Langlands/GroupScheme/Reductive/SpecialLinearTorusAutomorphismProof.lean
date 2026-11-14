import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismStatement
import Langlands.GroupScheme.Reductive.SpecialLinearTypeACoord
import Langlands.GroupScheme.SpecialLinearInnerForm.AdjointPointMatrix
import Langlands.GroupScheme.SpecialLinearContragredient
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Reductive.SpecialLinearPinningProof

/-! # Matrix descriptions of torus-preserving special-linear automorphisms

Proof of `SpecialLinearTorusAutomorphismStatement`: a torus-preserving
automorphism of the split special linear group is conjugation by a matrix when
its based-root action is trivial, and conjugation by a matrix composed with
inverse transpose otherwise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RootPairingTypeA

namespace Langlands.GroupScheme.SpecialLinearTorusAutomorphism

attribute [local instance] SpecialLinear.isAffineHom_groupScheme

section Negation

variable {S : Scheme.{u}}

/-- The inversion automorphism `-𝟙` of a commutative group scheme. -/
def negIso (T : CommGroupScheme S) : T ≅ T where
  hom := -𝟙 T
  inv := -𝟙 T
  hom_inv_id := by rw [Preadditive.neg_comp_neg, Category.comp_id]
  inv_hom_id := by rw [Preadditive.neg_comp_neg, Category.comp_id]

end Negation

/-- Inner automorphisms act inversely by the inverse conjugation. -/
theorem comp_innerIso_inv {S : Scheme.{u}} (G : GroupScheme S) (g : Over.mk (𝟙 S) ⟶ G.X)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (G.innerIso g).inv.hom.hom =
      (G.constantPoint g T)⁻¹ * x * G.constantPoint g T :=
  (comp_isoOfPoints_inv _ _ T x).trans (MulAut.conj_symm_apply _ _)

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝐒𝐋" => SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)
local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-! ### Weyl-type automorphisms are matrix conjugations -/

/-- The matrix of a point read through the identity presentation. -/
theorem pointMatrix_refl (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ 𝐒𝐋.X) :
    SpecialLinearInnerForm.pointMatrix (Iso.refl _) T g =
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) T g := by
  rw [SpecialLinearInnerForm.pointMatrix_apply, Iso.refl_hom, Grp.id_hom_hom, Category.comp_id]

/-- **Weyl case.** A torus-compatible automorphism whose torus action is that of a Weyl
element of the pinned root datum is conjugation by an invertible `k`-matrix on every
test scheme. -/
theorem exists_matrix_of_weyl (p : SplitPinning 𝐒𝐋) (f : 𝐒𝐋 ≅ 𝐒𝐋) (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (w : p.rootDatum.Aut) (hw : w ∈ p.rootDatum.weylGroup)
    (hwt : ∀ χ, w.weightEquiv χ = t.hom ≫ χ) :
    ∃ X : GL (Fin (n + 1)) k, ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ 𝐒𝐋.X),
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z (g ≫ f.hom.hom.hom) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        (Matrix.GeneralLinearGroup.map (scalarMap Z) X :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z g :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          (Matrix.GeneralLinearGroup.map (scalarMap Z) X⁻¹ :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) := by
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence k 𝐒𝐋 p.isConnectedReductive
  let : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono
  have hσ : characterAut t ∈ weylImage p.inclusion := by
    have h1 : RootPairing.Equiv.weightHom p.rootDatum w ∈
        weylImage p.inclusion :=
      p.isRootDatum.abstractWeylImage_le ⟨w, hw, rfl⟩
    have h2 : RootPairing.Equiv.weightHom p.rootDatum w = (characterAut t)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      apply LinearEquiv.ext
      intro χ
      rw [LinearEquiv.mul_apply, RootPairing.Equiv.weightHom_apply, characterAut_apply, hwt,
        Iso.hom_inv_id_assoc]
      rfl
    rw [h2] at h1
    exact inv_mem_iff.mp h1
  obtain ⟨x, hx⟩ := p.exists_adjointPoint_of_weylImage hq f t hsq hσ
  obtain ⟨X, hX⟩ := SpecialLinearInnerForm.exists_matrix_for_adjoint_basePoint hq (Iso.refl _) x
  refine ⟨X, fun Z g => ?_⟩
  have h := hX Z g
  rw [hx, pointMatrix_refl, pointMatrix_refl] at h
  exact h

/-! ### Conjugating the pinned torus to the diagonal torus -/

/-- The pinned torus is conjugate to the diagonal torus by a rational point. -/
theorem exists_conj_diagonal (p : SplitPinning 𝐒𝐋) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X) (e : p.torus.toGrp ≅ (𝔻).toGrp),
      p.inclusion ≫ (GroupScheme.innerIso 𝐒𝐋 g).hom =
        e.hom ≫ SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k) :=
  (maximalSplitTorusConjugacy k 𝐒𝐋 p.isConnectedReductive).1 _ _ _ _
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus)
    ((SpecialLinear.FinSucc.isMaximalTorus_diagonalTorus n k).isMaximalSplitTorus
      (SpecialLinear.FinSucc.isSplitTorus_diagonalTorus n k))

/-- The pinned root datum carries type `A_n` coordinates, and its coroots span the
cocharacter lattice. Both are transported from the diagonal torus. -/
theorem exists_typeACoord (p : SplitPinning 𝐒𝐋) :
    Nonempty (TypeACoord p.rootDatum n) ∧
      Submodule.span ℤ (Set.range p.rootDatum.coroot) = ⊤ := by
  obtain ⟨J, _, Q, hQ, -⟩ := SpecialLinear.FinSucc.exists_coordinateRootDatum (n := n) (k := k)
  obtain ⟨g, e, he⟩ := exists_conj_diagonal p
  let E := rootDatumEquivOfTorusCompatibleIso p.isConnectedReductive p.isConnectedReductive
    p.isSplitTorus (SpecialLinear.FinSucc.isSplitTorus_diagonalTorus n k) p.isMaximalTorus
    (SpecialLinear.FinSucc.isMaximalTorus_diagonalTorus n k) (GroupScheme.innerIso 𝐒𝐋 g)
    (CommGroupScheme.isoOfGroupIso e) he p.isRootDatum hQ
  exact ⟨⟨(SpecialLinear.FinSucc.typeACoord hQ).transport E⟩,
    span_coroot_eq_top_of_equiv E (SpecialLinear.FinSucc.corootSpan_eq_top hQ)⟩

/-! ### The twisted contragredient -/

/-- The inverse-transpose automorphism conjugated by an inner automorphism. -/
def twistIso (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X) : 𝐒𝐋 ≅ 𝐒𝐋 :=
  GroupScheme.innerIso 𝐒𝐋 g ≪≫
    SpecialLinear.contragredientIso (Fin (n + 1)) (CommRingCat.of k) ≪≫
      (GroupScheme.innerIso 𝐒𝐋 g).symm

theorem twistIso_hom_comp_hom (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X) :
    (twistIso g).hom ≫ (twistIso g).hom = 𝟙 𝐒𝐋 := by
  simp only [twistIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (SpecialLinear.contragredientIso (Fin (n + 1)) (CommRingCat.of k)).hom,
    SpecialLinear.contragredientIso_hom_comp_hom, Category.id_comp, Iso.hom_inv_id]

/-- The twisted contragredient acts on the pinned torus by inversion. -/
theorem inclusion_comp_twistIso_hom (p : SplitPinning 𝐒𝐋)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X) (e : p.torus.toGrp ≅ (𝔻).toGrp)
    (he : p.inclusion ≫ (GroupScheme.innerIso 𝐒𝐋 g).hom =
      e.hom ≫ SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k)) :
    p.inclusion ≫ (twistIso g).hom =
      CommGroupScheme.groupHom (negIso p.torus).hom ≫ p.inclusion := by
  have hinv : SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k) ≫
      (GroupScheme.innerIso 𝐒𝐋 g).inv = e.inv ≫ p.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, he, Iso.inv_hom_id_assoc]
  simp only [twistIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he, Category.assoc,
    ← Category.assoc (SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k)),
    SpecialLinear.FinSucc.diagonalTorus_comp_contragredientIso_hom, Category.assoc, hinv,
    ← Category.assoc, ← Category.assoc]
  congr 1
  change CommGroupScheme.groupHom (((CommGroupScheme.isoOfGroupIso e).hom ≫ (-𝟙 _)) ≫
    (CommGroupScheme.isoOfGroupIso e).inv) = _
  rw [Preadditive.comp_neg, Category.comp_id, Preadditive.neg_comp, Iso.hom_inv_id]
  rfl

/-- The matrix of a rational point, read on any test scheme. -/
theorem exists_pointsEquiv_constantPoint
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X) :
    ∃ C : Matrix.SpecialLinearGroup (Fin (n + 1)) k, ∀ Z : Over (Spec (CommRingCat.of k)),
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
          (GroupScheme.constantPoint 𝐒𝐋 g Z) =
        Matrix.SpecialLinearGroup.map (scalarMap Z) C := by
  refine ⟨Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) _ g), fun Z => ?_⟩
  have hφ : Z.hom.appTop.hom =
      (scalarMap Z).comp (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom := by
    rw [scalarMap, ← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]
  rw [GroupScheme.constantPoint, SpecialLinear.pointsEquiv_naturality]
  change Matrix.SpecialLinearGroup.map Z.hom.appTop.hom _ = _
  rw [hφ]
  ext i j
  rfl

theorem toGL_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (C : Matrix.SpecialLinearGroup (Fin (n + 1)) A) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map φ C) =
      Matrix.GeneralLinearGroup.map φ (Matrix.SpecialLinearGroup.toGL C) :=
  Units.ext rfl

/-- The twisted contragredient on points, in `GL`. -/
theorem toGL_pointsEquiv_twistIso (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X)
    (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ 𝐒𝐋.X) :
    Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
        (x ≫ (twistIso g).hom.hom.hom)) =
      (Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
          (CommRingCat.of k) Z (GroupScheme.constantPoint 𝐒𝐋 g Z)))⁻¹ *
        GeneralLinear.matrixContragredient (Fin (n + 1)) Γ(Z.left, ⊤)
          (Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
              (CommRingCat.of k) Z (GroupScheme.constantPoint 𝐒𝐋 g Z)) *
            Matrix.SpecialLinearGroup.toGL
              (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z x) *
            (Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
              (CommRingCat.of k) Z (GroupScheme.constantPoint 𝐒𝐋 g Z)))⁻¹) *
        Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
          (CommRingCat.of k) Z (GroupScheme.constantPoint 𝐒𝐋 g Z)) := by
  simp only [twistIso, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom]
  rw [← Category.assoc, ← Category.assoc, GroupScheme.comp_innerIso_hom,
    SpecialLinear.comp_contragredientIso_hom, comp_innerIso_inv]
  simp only [map_mul, map_inv, SpecialLinear.pointsEquiv_contragredientPoints,
    SpecialLinear.toGL_matrixContragredient]

/-- A group identity behind the inverse-transpose formula. -/
theorem conj_identity {G : Type*} [Group G] (κ : G ≃* G) (c y h : G) :
    c⁻¹ * κ (c * (y * h * y⁻¹) * c⁻¹) * c =
      (c⁻¹ * κ (c * y)) * κ h * (c⁻¹ * κ (c * y))⁻¹ := by
  simp only [map_mul, map_inv]
  group

/-- **Inverse-transpose case.** A torus-compatible automorphism whose torus action is
the negative of a Weyl element is a matrix conjugation composed with inverse transpose. -/
theorem exists_matrix_of_neg_weyl (p : SplitPinning 𝐒𝐋) (f : 𝐒𝐋 ≅ 𝐒𝐋)
    (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (w : p.rootDatum.Aut) (hw : w ∈ p.rootDatum.weylGroup)
    (hwt : ∀ χ, w.weightEquiv χ = -(t.hom ≫ χ)) :
    ∃ X : GL (Fin (n + 1)) k, ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ 𝐒𝐋.X),
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z (g ≫ f.hom.hom.hom) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        (Matrix.GeneralLinearGroup.map (scalarMap Z) X :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z g)⁻¹ :
              Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
          (Matrix.GeneralLinearGroup.map (scalarMap Z) X⁻¹ :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) := by
  obtain ⟨g0, e, he⟩ := exists_conj_diagonal p
  obtain ⟨C, hC⟩ := exists_pointsEquiv_constantPoint g0
  have hsq' : p.inclusion ≫ (f ≪≫ twistIso g0).hom =
      CommGroupScheme.groupHom (t ≪≫ negIso p.torus).hom ≫ p.inclusion := by
    rw [Iso.trans_hom, ← Category.assoc, hsq, Category.assoc,
      inclusion_comp_twistIso_hom p g0 e he, ← Category.assoc]
    rfl
  obtain ⟨Y, hY⟩ := exists_matrix_of_weyl p (f ≪≫ twistIso g0) (t ≪≫ negIso p.torus) hsq'
    w hw (fun χ => by
      rw [hwt]
      change _ = (t.hom ≫ (-𝟙 p.torus)) ≫ χ
      rw [Preadditive.comp_neg, Category.comp_id, Preadditive.neg_comp])
  let c0 := Matrix.SpecialLinearGroup.toGL C
  refine ⟨c0⁻¹ * GeneralLinear.matrixContragredient (Fin (n + 1)) k (c0 * Y), fun Z g => ?_⟩
  let φ := scalarMap Z
  let κ := GeneralLinear.matrixContragredient (Fin (n + 1)) Γ(Z.left, ⊤)
  let ψ := (twistIso (k := k) (n := n) g0).hom.hom.hom
  have hc : Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
      (CommRingCat.of k) Z (GroupScheme.constantPoint 𝐒𝐋 g0 Z)) =
      Matrix.GeneralLinearGroup.map φ c0 := by
    rw [hC Z, toGL_map]
  have hψψ : ψ ≫ ψ = 𝟙 _ := by
    have h := congrArg (fun a => a.hom.hom) (twistIso_hom_comp_hom (k := k) (n := n) g0)
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using h
  have hY' : Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
      (CommRingCat.of k) Z ((g ≫ f.hom.hom.hom) ≫ ψ)) =
      Matrix.GeneralLinearGroup.map φ Y *
        Matrix.SpecialLinearGroup.toGL
          (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z g) *
        (Matrix.GeneralLinearGroup.map φ Y)⁻¹ := by
    apply Units.ext
    have h := hY Z g
    simp only [Iso.trans_hom, Grp.comp_hom_hom] at h
    rw [Category.assoc, Units.val_mul, Units.val_mul, ← map_inv]
    exact h
  have hK : Matrix.SpecialLinearGroup.toGL (SpecialLinear.pointsEquiv (Fin (n + 1))
      (CommRingCat.of k) Z (g ≫ f.hom.hom.hom)) =
      Matrix.GeneralLinearGroup.map φ (c0⁻¹ * GeneralLinear.matrixContragredient (Fin (n + 1)) k
        (c0 * Y)) *
      κ (Matrix.SpecialLinearGroup.toGL
          (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z g)) *
      (Matrix.GeneralLinearGroup.map φ (c0⁻¹ * GeneralLinear.matrixContragredient (Fin (n + 1)) k
        (c0 * Y)))⁻¹ := by
    have hgf : g ≫ f.hom.hom.hom = ((g ≫ f.hom.hom.hom) ≫ ψ) ≫ ψ := by
      rw [Category.assoc, hψψ, Category.comp_id]
    rw [hgf, toGL_pointsEquiv_twistIso, hc, hY', map_mul (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) φ),
      map_inv (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) φ), ← GeneralLinear.matrixContragredient_map,
      map_mul (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) φ)]
    exact conj_identity κ _ _ _
  have hval := congrArg (fun a : GL (Fin (n + 1)) Γ(Z.left, ⊤) =>
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) hK
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hval
  rw [← map_inv (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) φ)] at hval
  rw [hval, GeneralLinear.matrixContragredient_coe, ← map_inv]
  rfl

/-! ### The theorem -/

/-- **Torus-preserving automorphisms of `SL_{n+1}`.** -/
theorem specialLinearTorusAutomorphism : SpecialLinearTorusAutomorphismStatement.{u} := by
  intro k _ n p f t hsq δ θ
  obtain ⟨⟨C⟩, hspan⟩ := exists_typeACoord p
  have hδw : ∀ χ, δ.weightEquiv χ = t.hom ≫ χ := fun χ =>
    rootDatumEquivOfTorusCompatibleIso_weightMap _ _ _ _ _ _ f t hsq _ _ χ
  by_cases hfix : ∀ v : p.base.support, θ.val.indexEquiv v.val = v.val
  · have hs : Submodule.span ℤ (p.rootDatum.coroot '' (p.base.support : Set _)) = ⊤ := by
      rw [RootPairing.Base.span_int_coroot_support]
      exact hspan
    have hθ : θ = 1 := by
      apply Subtype.ext
      exact eq_one_of_indexEquiv_eq θ.val _ hs (fun i hi => hfix ⟨i, hi⟩)
    have hδ : δ ∈ p.rootDatum.weylGroup := (p.basedRootDatumProjection_eq_one_iff δ).mp hθ
    obtain ⟨X, hX⟩ := exists_matrix_of_weyl p f t hsq δ hδ hδw
    refine ⟨X, fun Z g => ⟨fun _ => ?_, fun ⟨v, hv⟩ => absurd (hfix v) hv⟩⟩
    rw [hX, MulEquiv.apply_symm_apply]
  · have hδ : δ ∉ p.rootDatum.weylGroup := by
      intro hδ
      apply hfix
      intro v
      have hθ1 : θ = 1 := (p.basedRootDatumProjection_eq_one_iff δ).mpr hδ
      rw [hθ1]
      rfl
    obtain ⟨w, hw, hwδ⟩ := (C.mem_weylGroup_or_exists_neg δ).resolve_left hδ
    obtain ⟨X, hX⟩ := exists_matrix_of_neg_weyl p f t hsq w hw (fun χ => by rw [hwδ, hδw])
    refine ⟨X, fun Z g => ⟨fun h => absurd h hfix, fun _ => ?_⟩⟩
    rw [hX, MulEquiv.apply_symm_apply]

end Langlands.GroupScheme.SpecialLinearTorusAutomorphism
