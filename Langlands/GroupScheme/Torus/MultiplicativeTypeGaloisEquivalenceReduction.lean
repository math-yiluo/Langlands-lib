import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisEquivalenceStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessStatement
import Langlands.GroupScheme.Torus.GaloisModuleRealizationProof

/-! # Finite Galois character anti-equivalence from full faithfulness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace SplitMultiplicativeType

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- A morphism of character actions is equivariant for the canonical Galois actions. -/
theorem characterAction_hom_equivariant {H G : SplitMultiplicativeType k L}
    (φ : characterAction k L H ⟶ characterAction k L G) (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj H.obj)) :
    φ.hom.hom.hom (characterLattice.galoisRepresentation k L H.obj σ χ) =
      characterLattice.galoisRepresentation k L G.obj σ (φ.hom.hom.hom χ) := by
  have h := congrArg (fun ψ => ψ.hom.hom χ) (φ.comm σ)
  simpa only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply,
    characterAction_ρ_apply] using h

/-- The underlying additive map of a morphism of character actions. -/
def characterActionAddHom {H G : SplitMultiplicativeType k L}
    (φ : characterAction k L H ⟶ characterAction k L G) :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj H.obj) →+
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj G.obj) :=
  φ.hom.hom.hom.toAddMonoidHom

@[simp]
theorem characterActionAddHom_apply {H G : SplitMultiplicativeType k L}
    (φ : characterAction k L H ⟶ characterAction k L G)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj H.obj)) :
    characterActionAddHom φ χ = φ.hom.hom.hom χ := rfl

/-- The integral representation underlying an object of the target action category,
for the canonical `ℤ`-module structure of its additive group. -/
def actionRepresentation (A : Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L)) :
    @Representation ℤ (L ≃ₐ[k] L) A.V _ _ _ (AddCommGroup.toIntModule A.V) where
  toFun σ := (A.ρ σ).hom.hom.toAddMonoidHom.toIntLinearMap
  map_one' := DFunLike.ext _ _ fun v => by
    change (A.ρ 1).hom.hom v = v
    simp
  map_mul' σ τ := DFunLike.ext _ _ fun v => by
    change (A.ρ (σ * τ)).hom.hom v = (A.ρ σ).hom.hom ((A.ρ τ).hom.hom v)
    simp [End.mul_def]

@[simp]
theorem actionRepresentation_apply (A : Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L))
    (σ : L ≃ₐ[k] L) (v : A.V) :
    actionRepresentation A σ v = (A.ρ σ).hom.hom v := rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- Faithfulness from the full-faithfulness proposition. -/
theorem characterFunctor_faithful_of
    (hFF : MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}) :
    (characterFunctor k L).Faithful := by
  refine ⟨fun {X Y} f g hfg => ?_⟩
  obtain ⟨M, _, _, ⟨i⟩⟩ := X.unop.property
  obtain ⟨M', _, _, ⟨i'⟩⟩ := Y.unop.property
  have hiff := hFF k L Y.unop.obj X.unop.obj M' M i' i
    (characterActionAddHom ((characterFunctor k L).map f))
  obtain ⟨a, -, ha⟩ := hiff.mp fun σ χ =>
    characterAction_hom_equivariant ((characterFunctor k L).map f) σ χ
  have hf : f.unop.hom = a := ha _ fun χ => rfl
  have hg : g.unop.hom = a := ha _ fun χ => by
    rw [characterActionAddHom_apply, hfg]
    rfl
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  rw [hf, hg]

/-- Fullness from the full-faithfulness proposition. -/
theorem characterFunctor_full_of
    (hFF : MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}) :
    (characterFunctor k L).Full := by
  refine ⟨fun {X Y} φ => ?_⟩
  obtain ⟨M, _, _, ⟨i⟩⟩ := X.unop.property
  obtain ⟨M', _, _, ⟨i'⟩⟩ := Y.unop.property
  have hiff := hFF k L Y.unop.obj X.unop.obj M' M i' i (characterActionAddHom φ)
  obtain ⟨a, ha, -⟩ := hiff.mp fun σ χ => characterAction_hom_equivariant φ σ χ
  refine ⟨(ObjectProperty.homMk a : Y.unop ⟶ X.unop).op, ?_⟩
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro χ
  exact ha χ

/-- Essential surjectivity from the published Galois-module realization. -/
theorem characterFunctor_essSurj :
    (characterFunctor k L).EssSurj := by
  refine ⟨fun A => ?_⟩
  have hfg : AddGroup.FG A.V := by
    rw [← Module.Finite.iff_addGroup_fg]
    convert (inferInstance : Module.Finite ℤ A.V)
    exact Subsingleton.elim _ _
  obtain ⟨T, i, e, -, he⟩ :=
    multiplicativeTypeGaloisModuleRealization k L A.V (actionRepresentation A)
  let X : SplitMultiplicativeType k L := ⟨T, ⟨A.V, inferInstance, hfg, ⟨i⟩⟩⟩
  refine ⟨op X, ⟨Action.mkIso (ObjectProperty.isoMk _
    (LinearEquiv.toModuleIso e.symm.toIntLinearEquiv)) fun σ => ?_⟩⟩
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro χ
  change e.symm (characterLattice.galoisRepresentation k L T σ χ) =
    (A.ρ σ).hom.hom (e.symm χ)
  obtain ⟨m, rfl⟩ := e.surjective χ
  rw [← he σ m, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rfl

/-- The finite Galois character anti-equivalence, assuming the full-faithfulness
proposition. -/
theorem characterFunctor_isEquivalence_of
    (hFF : MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}) :
    (characterFunctor k L).IsEquivalence where
  faithful := characterFunctor_faithful_of hFF
  full := characterFunctor_full_of hFF
  essSurj := characterFunctor_essSurj

end SplitMultiplicativeType

/-- The equivalence statement follows from the full-faithfulness statement. -/
theorem multiplicativeTypeGaloisEquivalence_of_fullFaithfulness
    (hFF : MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}) :
    MultiplicativeTypeGaloisEquivalenceStatement.{u} :=
  fun _ _ _ _ _ _ _ => SplitMultiplicativeType.characterFunctor_isEquivalence_of hFF

end Langlands.GroupScheme
