import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.Rational.LaurentAugmentation
import Langlands.GroupScheme.Rational.TorusPrimitiveEmbedding
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Unipotent.AdditiveCharacter

/-! # Actual pointed Laurent pullbacks and primitive coordinate functions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The actual coordinate functions additive on the group, as a submodule. -/
def primitiveFunctions : Submodule k B :=
  letI := AffineLinearEmbedding.bialgebra e
  Coalgebra.skewPrimitive k (1 : B) 1

@[simp] theorem mem_primitiveFunctions {b : B} :
    b ∈ primitiveFunctions e ↔
      letI := AffineLinearEmbedding.bialgebra e
      Bialgebra.IsPrimitiveElem k b := Iff.rfl

/-- Primitive coordinate functions vanish at the group identity. -/
theorem counit_eq_zero_of_mem_primitiveFunctions {b : B}
    (hb : b ∈ primitiveFunctions e) : AffineLinearEmbedding.counit e b = 0 := by
  let := AffineLinearEmbedding.bialgebra e
  exact hb.counit_eq_zero

/-- Bialgebra primitivity is exactly additivity on all algebra-valued points. -/
theorem mem_primitiveFunctions_iff {b : B} :
    b ∈ primitiveFunctions e ↔ IsPrimitiveFunction e b := by
  let := AffineLinearEmbedding.bialgebra e
  constructor
  · intro hb A x y
    exact Unipotent.isPrimitiveFamily_of_isPrimitiveElem e hb A x y (0 : Fin 1)
  · intro hb
    apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.2
    let A := CommAlgCat.of (CommRingCat.of k) (B ⊗[k] B)
    have h := hb A
      (AffineLinearEmbedding.pt e (A := A) Algebra.TensorProduct.includeLeft)
      (AffineLinearEmbedding.pt e (A := A) Algebra.TensorProduct.includeRight)
    change AffineLinearEmbedding.comul e b = _ at h
    simp only [coord_ofCoord] at h
    change AffineLinearEmbedding.comul e b = b ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] b at h
    change AffineLinearEmbedding.comul e b = (1 : B) ⊗ₜ[k] b + b ⊗ₜ[k] (1 : B)
    exact h.trans (add_comm _ _)

/-- The primitive-coordinate submodule is stable under the characteristic power. -/
theorem pow_mem_primitiveFunctions (p : ℕ) [Fact p.Prime] [CharP k p]
    {b : B} (hb : b ∈ primitiveFunctions e) : b ^ p ∈ primitiveFunctions e := by
  let := AffineLinearEmbedding.bialgebra e
  have : Nontrivial B := (AffineLinearEmbedding.counit e).toRingHom.domain_nontrivial
  have : CharP B p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k B) p
  have : CharP (B ⊗[k] B) p :=
    charP_of_injective_algebraMap (algebraMap k (B ⊗[k] B)).injective p
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.2
  change AffineLinearEmbedding.comul e (b ^ p) = _
  rw [map_pow, show AffineLinearEmbedding.comul e b =
    (1 : B) ⊗ₜ[k] b + b ⊗ₜ[k] (1 : B) from hb.comul_eq_tmul_add_tmul,
    add_pow_char]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow]

/-- The spectrum point classified by the counit is the identity point. -/
theorem spec_counit_eq_one :
    (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (AffineLinearEmbedding.counit e)).op =
      (1 : (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶ (groupScheme F e).X) := by
  apply (affinePointsEquiv F e _).injective
  rw [affinePointsEquiv_map, map_one]
  exact AffineLinearEmbedding.pt_homEquiv_symm e 1

/-- A pointed dominant split-torus map gives an injective Laurent algebra
pullback preserving the actual identity augmentations. -/
theorem exists_pointedLaurentPullback
    [IsReduced (groupScheme F e).X.left]
    (hdom : HasPointedSplitTorusDomination (groupScheme F e)) :
    ∃ (I : Type u) (_ : Fintype I)
      (σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ)),
      Function.Injective σ ∧
      (LaurentAugmentation.augmentation k (I → ℤ)).comp σ =
        AffineLinearEmbedding.counit e := by
  classical
  obtain ⟨P, f, hP, hd, hp⟩ := hdom
  obtain ⟨I, hI, ⟨eP⟩⟩ := hP
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let D := (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp
  let d : D ≅ P := Diagonalizable.splitIso (CommRingCat.of k)
    (AddEquiv.refl (I → ℤ)) ≪≫ eP.symm
  let q : D.X ⟶ (groupScheme F e).X := d.hom.hom.hom ≫ f
  let σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ) :=
    (algSpec.fullyFaithful.preimage q).unop.hom
  have hσ : (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ).op = q :=
    algSpec.fullyFaithful.map_preimage q
  have hq : η[D.X] ≫ q = η[(groupScheme F e).X] := by
    dsimp only [q]
    rw [← Category.assoc, IsMonHom.one_hom]
    change (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P.X) ≫ f = 1 at hp
    simpa only [Hom.one_def, SemiCartesianMonoidalCategory.toUnit_unit,
      Category.id_comp] using hp
  have hd' : IsDominant q.left := by
    let : IsDominant f.left := hd
    dsimp only [q]
    change IsDominant (d.hom.hom.hom.left ≫ f.left)
    infer_instance
  have hinj : Function.Injective σ := by
    let ψ := CommRingCat.ofHom σ.toRingHom
    have hψ : Spec.map ψ = q.left := congrArg CommaMorphism.left hσ
    let : IsReduced (Spec (CommRingCat.of B)) := ‹IsReduced (groupScheme F e).X.left›
    let : IsDominant (Spec.map ψ) := hψ.symm ▸ hd'
    let : IsSchemeTheoreticallyDominant (Spec.map ψ) :=
      IsSchemeTheoreticallyDominant.of_isDominant _
    have happ : Function.Injective (Spec.map ψ).appTop := (Spec.map ψ).app_injective ⊤
    have heq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
        (Scheme.ΓSpecIso _).hom := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have hi : Function.Injective ψ.hom := by
      rw [heq, CommRingCat.hom_comp, CommRingCat.hom_comp,
        RingHom.coe_comp, RingHom.coe_comp]
      exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective.comp
        (happ.comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective)
    exact hi
  refine ⟨I, inferInstance, σ, hinj, ?_⟩
  suffices h : CommAlgCat.ofHom (R := CommRingCat.of k)
        ((LaurentAugmentation.augmentation k (I → ℤ)).comp σ) =
      CommAlgCat.ofHom (R := CommRingCat.of k) (AffineLinearEmbedding.counit e) from
    congrArg CommAlgCat.Hom.hom h
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  change (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom σ ≫ CommAlgCat.ofHom
      (LaurentAugmentation.augmentation k (I → ℤ))).op = _
  rw [op_comp, Functor.map_comp, hσ, spec_counit_eq_one]
  have hε : (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (LaurentAugmentation.augmentation k (I → ℤ))).op =
      (1 : (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶ D.X) := by
    have hc := Diagonalizable.counit_eq (CommRingCat.of k) (I → ℤ)
    change CommAlgCat.ofHom (LaurentAugmentation.augmentation k (I → ℤ)) =
      CommAlgCat.ofHom (AffineLinearEmbedding.counit
        (Diagonalizable.grpCorepresentation (CommRingCat.of k) (I → ℤ))) at hc
    rw [hc]
    exact spec_counit_eq_one _
  rw [hε]
  simp only [Hom.one_def, Category.assoc, hq]

end Langlands.GroupScheme.Corepresented
