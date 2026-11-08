import Langlands.GroupScheme.Dynamic.ComparisonExtension
import Langlands.GroupScheme.Dynamic.ReductiveComparison
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Dynamic.QuotientFiberBaseChange
import Langlands.GroupScheme.Dynamic.FlagQuotientStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientStatement
import Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionStatement
import Langlands.GroupScheme.Reductive.PseudoReductiveRationalUnipotentPointStatement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.PseudoParabolicQuotientCorepresentedReduction
import Langlands.CommutativeAlgebra.TensorRationalPointDensity
import Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange
import Langlands.GroupScheme.Dynamic.FlagQuotientProjection
import Langlands.GroupScheme.CorepresentedSmoothGeometry
import Mathlib.FieldTheory.IsSepClosed

/-! # The separably closed case of CGP Proposition C.1.6

Over a separably closed field `k`, the DVR lifting property holds for homogeneous quotients of
corepresented pseudo-reductive groups by dynamic parabolic subgroups. The proof builds the
comparison data over `Ω = AlgebraicClosure k` from the Library statements on unipotent radicals
and on proper dynamic flag quotients, and applies `Corepresented.exists_extension_of_comparison`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open Corepresented Dynamic.OppositeCell

theorem corepresentedDynamicParabolicQuotientDVRLifting_of_isSepClosed
    (hradE : UnipotentRadicalExistenceStatement.{u})
    (hradQ : UnipotentRadicalQuotientStatement.{u})
    (hflag : DynamicFlagQuotientExistenceStatement.{u})
    (hsep : PseudoReductiveSeparableExtensionStatement.{u})
    (hc : PseudoReductiveRationalUnipotentPointStatement.{u})
    (k : Type u) [Field k] [IsSepClosed k]
    (hrat : ∀ (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra.FiniteType k R']
      [Nontrivial R'] [Algebra.IsGeometricallyReduced k R'], Nonempty (R' →ₐ[k] k)) :
    CorepresentedDynamicParabolicQuotientDVRLifting k := by
  intro F B e χ Q q hG hsm hsurj hqc hf R _ _ _ _ hF x
  have := algebraFiniteType_of_isPseudoReductive hG
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : IsAffine (groupScheme F e).X.left := isAffine_of_isAffineHom (groupScheme F e).X.hom
  have := hsm
  have := hsurj
  have := hqc
  -- The algebraic closure and the base change of `G`.
  let Ω := AlgebraicClosure k
  have : ConnectedSpace (baseChangeGroup F e Ω).X.left :=
    (groupScheme F e).connectedSpace_baseChange_of_smooth_affine (Corepresented.scalarMap k Ω)
  have : Smooth (baseChangeGroup F e Ω).X.hom := by
    change Smooth (pullback.snd (groupScheme F e).X.hom (Corepresented.scalarMap k Ω))
    infer_instance
  have : IsAffineHom (baseChangeGroup F e Ω).X.hom := by
    change IsAffineHom (pullback.snd (groupScheme F e).X.hom (Corepresented.scalarMap k Ω))
    infer_instance
  -- The unipotent radical and the reductive quotient `H`.
  obtain ⟨U, i, hi⟩ := hradE Ω (baseChangeGroup F e Ω)
  obtain ⟨H, π, hπ, hH⟩ := hradQ Ω (baseChangeGroup F e Ω) U i hi
  have hHred : IsConnectedReductive H :=
    ⟨hH.smooth, hH.isAffineHom, hH.connectedSpace,
      (hsep Ω (AlgebraicClosure Ω) H hH).hasTrivialUnipotentRadical⟩
  have := hH.smooth
  have := hH.isAffineHom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Surjective π.hom.hom.left := hπ.2.1
  -- The cocharacters.
  let lam := opposite χ
  let χ'' := opposite (Dynamic.baseChangeCocharacter (Corepresented.scalarMap k Ω) lam ≫ π)
  have hχ : opposite χ'' = Dynamic.baseChangeCocharacter (Corepresented.scalarMap k Ω) lam ≫ π :=
    Dynamic.powerHom_neg_one_comp_powerHom_neg_one _
  have hχ' : χ'' = Dynamic.baseChangeCocharacter (Corepresented.scalarMap k Ω) χ ≫ π := by
    change CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫
      (Dynamic.baseChangeCocharacter (Corepresented.scalarMap k Ω)
        (CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ) ≫ π) = _
    rw [Dynamic.baseChangeCocharacter_powerHom, ← Category.assoc, ← Category.assoc,
      Category.assoc (CommGroupScheme.groupHom _), Dynamic.powerHom_neg_one_comp_powerHom_neg_one]
  -- The proper flag quotient of `H`.
  obtain ⟨Q₀, π₀, hprop, hf₀, hsec⟩ := hflag Ω H hHred χ''
  have := hprop
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ''
  have : Mono (Dynamic.Affine.parabolicHom χ'').hom.hom := hP.1
  have : Smooth (Dynamic.Affine.parabolicScheme χ'').X.hom :=
    (dynamicSmooth Ω H χ'' _ (Dynamic.Affine.parabolicHom χ'')).1 hP
  have : Surjective (Dynamic.Affine.parabolicScheme χ'').X.hom := surjective_hom _
  have : QuasiCompact (Dynamic.Affine.parabolicScheme χ'').X.hom := by
    have : IsClosedImmersion (Dynamic.Affine.parabolicHom χ'').hom.hom.left :=
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ''
    rw [← Over.w (Dynamic.Affine.parabolicHom χ'').hom.hom]
    infer_instance
  obtain ⟨hπ₀f, hπ₀s, hπ₀q⟩ :=
    Dynamic.flat_surjective_quasiCompact_of_localSections (Dynamic.Affine.parabolicHom χ'') π₀
    (by rw [hP.2]; exact hf₀) hsec
  have := hπ₀f
  have := hπ₀s
  have := hπ₀q
  -- The comparison map.
  have : Flat ((Over.pullback (Corepresented.scalarMap k Ω)).map q).left :=
    MorphismProperty.overPullbackMap (P := @Flat) (Corepresented.scalarMap k Ω) q inferInstance
  have : Surjective ((Over.pullback (Corepresented.scalarMap k Ω)).map q).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) (Corepresented.scalarMap k Ω) q hsurj
  have : QuasiCompact ((Over.pullback (Corepresented.scalarMap k Ω)).map q).left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) (Corepresented.scalarMap k Ω) q hqc
  obtain ⟨φ, hφ⟩ := exists_comparison_desc π χ q
    (dynamicParabolicQuotient_fiber_baseChange (Corepresented.scalarMap k Ω) χ q hf) π₀
    (by rw [← hχ']; exact hf₀)
  -- The kernel condition.
  have hker := hker_of_kernel π lam i hπ.2.2.2
    (hc k Ω (groupScheme F e) hG lam U i hi.isClosedSubgroup hi.isUnipotent hi.isNormal)
  -- Density of rational points.
  have := isDomain_of_smooth_connected (e := e)
  have := isGeometricallyReduced_of_smooth (e := e)
  have hdense : ∀ (K₁ K₂ : Type u) [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]
      (f₁ : K₁ ⊗[k] B) (f₂ : K₂ ⊗[k] B), f₁ ≠ 0 → f₂ ≠ 0 →
        ∃ a : B →ₐ[k] k, Algebra.TensorProduct.map (AlgHom.id k K₁) a f₁ ≠ 0 ∧
          Algebra.TensorProduct.map (AlgHom.id k K₂) a f₂ ≠ 0 :=
    fun K₁ K₂ _ _ _ _ f₁ f₂ h₁ h₂ =>
      CommutativeAlgebra.TensorRationalPointDensity.exists_algHom_tensor_ne_zero hrat f₁ h₁ f₂ h₂
  -- The DVR `Ω ⊗ R`.
  have := CommutativeAlgebra.DVRAlgebraicBaseChange.isDomain_tensor k Ω R
  have := CommutativeAlgebra.DVRAlgebraicBaseChange.isDiscreteValuationRing_tensor k Ω R
  exact exists_extension_of_comparison χ q hf π χ'' hχ π₀ hf₀ φ hφ hker hrat hdense R hF
    (CommutativeAlgebra.DVRAlgebraicBaseChange.isFractionRing_tensor k Ω R) x

end Langlands.GroupScheme
