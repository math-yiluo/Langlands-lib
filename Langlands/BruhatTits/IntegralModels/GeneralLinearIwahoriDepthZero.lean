import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient
import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison
import Langlands.BruhatTits.IntegralModels.FiniteReductiveQuotient
import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen

/-! # Depth-zero theory of the `GL_N` Iwahori model

The general depth-zero results on supplied model data, specialized to the published Iwahori model
data `iwahoriModelData F N` and its reductive quotient `iwahoriQuotientData F N`, whose quotient is
the diagonal torus. The residue-field points of the torus are `N`-tuples of units of `𝓀[F]`, and
the general reduction map is the diagonal of the residue matrix, so it agrees with the
group-level projection `generalLinearIwahoriDiagonal`. The general quotient theorem identifies
`I` modulo the kernel of reduction, which is `I^+`, with `(𝓀[F]ˣ)^N`; the general index theorem
gives `[I : I^+] = (q - 1)^N`; and the general
compactness and openness results show that `I` and `I^+` are compact open subgroups of `GL_N(F)`.
See the paired Markdown file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A] {n : ℕ}
  (b : Module.Basis (Fin n) R A)

/-- The unit of a section that is base changed, transported along an algebra isomorphism and
mapped by an algebra map. -/
theorem sectionUnitsEquiv_baseChange_congr_map (R' : CommRingCat.{u}) [Algebra R R']
    {A₁ : Type u} [Ring A₁] [Algebra R' A₁] {m : ℕ} (b₁ : Module.Basis (Fin m) R' A₁)
    (e : R' ⊗[R] A ≃ₐ[R'] A₁) {B : Type u} [Ring B] [Algebra R' B] {k : ℕ}
    (b' : Module.Basis (Fin k) R' B) (f : A₁ →ₐ[R'] B) (x : rationalPoints (groupScheme b)) :
    (sectionUnitsEquiv b' (((baseChangeSectionHom (WeilGm.baseMap R R') (groupScheme b) x ≫
        (baseChangeIso b R').hom.hom.hom) ≫ (congrIso (b.baseChange R') b₁ e).hom.hom.hom) ≫
        (map b₁ b' f).hom.hom) : B) =
      f (e ((1 : R') ⊗ₜ[R] (sectionUnitsEquiv b x : A))) := by
  rw [sectionUnitsEquiv_map, sectionUnitsEquiv_congrIso, sectionUnitsEquiv_baseChange]
  rfl

end Langlands.GroupScheme.FiniteFreeAlgebraUnits

namespace Langlands.BruhatTits.IntegralModels

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits
open Langlands.GeneralLinear.BlockShape (singletons singletonLevi singletons_index)

/-! ### The residue-field points of the diagonal torus -/

/-- The residue-field points of the diagonal torus are the `N`-tuples of units of `𝓀[F]`. -/
def diagTorusPointsEquiv : rationalPoints (diagTorus F N) ≃* (Fin N → 𝓀[F]ˣ) :=
  (sectionUnitsEquiv (diagBasis F N)).trans MulEquiv.piUnits

/-- The diagonal torus has `(q - 1)^N` residue-field points, where `q = |𝓀[F]|`. -/
theorem card_diagTorus_rationalPoints :
    Nat.card (rationalPoints (diagTorus F N)) = (Nat.card 𝓀[F] - 1) ^ N := by
  rw [Nat.card_congr (diagTorusPointsEquiv F N).toEquiv, Nat.card_pi, Nat.card_units,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The reduction map is the diagonal of the residue matrix -/

/-- The reduction of an integral section to the diagonal torus: the residues of the diagonal
entries of its unit in the Iwahori order. -/
theorem diagTorusPointsEquiv_reductiveReduction
    (x : (iwahoriModelData F N).neutral.integralSections) (i : Fin N) :
    ((diagTorusPointsEquiv F N ((iwahoriQuotientData F N).reductiveReduction x) i : 𝓀[F]ˣ) :
        𝓀[F]) =
      IsLocalRing.residue 𝒪[F]
        (((sectionUnit F N x : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
  have hcomp : (iwahoriQuotientData F N).reductiveReduction x =
      (((baseChangeSectionHom (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))
          (FiniteFreeAlgebraUnits.groupScheme (iwahoriBasis F N)) x) ≫
          (baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F])).hom.hom.hom) ≫
        (congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
          (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl).hom.hom.hom) ≫
        (specialDiagMap F N).hom.hom :=
    (show _ = (baseChangeSectionHom (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))
        (FiniteFreeAlgebraUnits.groupScheme (iwahoriBasis F N)) x) ≫
        (((baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F])).hom.hom.hom ≫
        (congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
          (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl).hom.hom.hom) ≫
        (specialDiagMap F N).hom.hom) from rfl).trans (by simp only [Category.assoc])
  have key := sectionUnitsEquiv_baseChange_congr_map (iwahoriBasis F N) (CommRingCat.of 𝓀[F])
    (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl (diagBasis F N) (specialDiag F N) x
  rw [hcomp]
  change (sectionUnitsEquiv (diagBasis F N) _ : Fin N → 𝓀[F]) i = _
  rw [key, AlgEquiv.coe_refl, id_eq, specialDiag_one_tmul]
  rfl

/-- **The general depth-zero reduction on the Iwahori subgroup.** If a point of `I` is the image
of `v ∈ GL_N(𝒪[F])`, its reduction to the diagonal torus is the diagonal of the residue of `v`. -/
theorem diagTorusPointsEquiv_parahoricReduction
    (g : (iwahoriModelData F N).neutral.integralPoints) {v : GL (Fin N) 𝒪[F]}
    (hg : GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N v)
    (i : Fin N) :
    ((diagTorusPointsEquiv F N ((iwahoriQuotientData F N).parahoricReduction g) i : 𝓀[F]ˣ) :
        𝓀[F]) =
      IsLocalRing.residue 𝒪[F] ((v : Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
  obtain ⟨x, rfl⟩ := (iwahoriModelData F N).neutralSectionsEquiv.surjective g
  rw [SpecialFibreQuotientData.parahoricReduction_neutralSectionsEquiv,
    diagTorusPointsEquiv_reductiveReduction]
  have hm := congrArg (fun M : Matrix (Fin N) (Fin N) F => M i i)
    (iwahoriIntegralPointMap_matrix F N x)
  have hm' : (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
      ((iwahoriModelData F N).neutral.integralPointMap x) : Matrix (Fin N) (Fin N) F) i i =
        algebraMap 𝒪[F] F ((v : Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
    have h := congrArg (fun w : GL (Fin N) F => (w : Matrix (Fin N) (Fin N) F) i i) hg
    exact h
  have heq : ((sectionUnit F N x : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i i =
      (v : Matrix (Fin N) (Fin N) 𝒪[F]) i i :=
    IsFractionRing.injective 𝒪[F] F (hm.symm.trans hm')
  rw [heq]

/-- The Iwahori integral points of the model data are the group-level Iwahori subgroup. -/
theorem iwahoriModelData_integralPoints :
    (iwahoriModelData F N).neutral.integralPoints = generalLinearIwahoriPoints F N := by
  rw [← (iwahoriModelData F N).neutralPoints_eq, iwahoriModelData_neutralPoints]

/-- The diagonal entries of the group-level projection `generalLinearIwahoriDiagonal`: if a
point of `I` is the image of `v ∈ GL_N(𝒪[F])`, its `i`-th block is the residue of `v i i`. -/
theorem generalLinearIwahoriDiagonal_apply (g : generalLinearIwahoriPoints F N)
    {v : GL (Fin N) 𝒪[F]}
    (hv : GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N v)
    (i : Fin N) (a b : Fin ((singletons N).size i)) :
    ((generalLinearIwahoriDiagonal F N g i : GL (Fin ((singletons N).size i)) 𝓀[F]) :
        Matrix (Fin ((singletons N).size i)) (Fin ((singletons N).size i)) 𝓀[F]) a b =
      IsLocalRing.residue 𝒪[F] ((v : Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
  change ((generalLinearReductionPreimageResidue F N ((singletons N).parabolic 𝓀[F]) g :
      GL (Fin N) 𝓀[F]) : Matrix (Fin N) (Fin N) 𝓀[F]) ((singletons N).index i a)
        ((singletons N).index i b) = _
  rw [generalLinearReductionPreimageResidue_apply g hv, singletons_index, singletons_index,
    glResidueMap_apply]

/-- **Comparison with the group-level projection.** On `I`, the general depth-zero reduction to
the diagonal torus, read as a Levi element of the singleton block shape, is the group-level
projection `generalLinearIwahoriDiagonal` (reduce, then take the diagonal blocks). -/
theorem singletonLevi_parahoricReduction
    (g : (iwahoriModelData F N).neutral.integralPoints) :
    singletonLevi 𝓀[F] (diagTorusPointsEquiv F N ((iwahoriQuotientData F N).parahoricReduction g)) =
      generalLinearIwahoriDiagonal F N
        ⟨g, (iwahoriModelData_integralPoints F N).le g.2⟩ := by
  obtain ⟨v, -, hv⟩ := (mem_generalLinearReductionPreimage ((singletons N).parabolic 𝓀[F])
    (g : _)).mp ((iwahoriModelData_integralPoints F N).le g.2)
  funext i
  apply Units.ext
  ext a b
  rw [generalLinearIwahoriDiagonal_apply F N ⟨g, (iwahoriModelData_integralPoints F N).le g.2⟩
    hv]
  obtain rfl : a = b := Subsingleton.elim a b
  rw [Langlands.GeneralLinear.BlockShape.singletonLevi_apply, GeneralLinear.scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    diagTorusPointsEquiv_parahoricReduction F N g hv]

/-! ### `I/I^+` and the index -/

/-- **KP 13.2.6 for the Iwahori model.** The general depth-zero quotient: `I` modulo the
kernel of reduction is the group of residue-field points of the diagonal torus, that is,
`N`-tuples of units of `𝓀[F]`. -/
def iwahoriDepthZeroQuotientEquiv :
    (iwahoriModelData F N).neutral.integralPoints ⧸
        (iwahoriQuotientData F N).parahoricReduction.ker ≃* (Fin N → 𝓀[F]ˣ) :=
  letI : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  ((iwahoriQuotientData F N).depthZeroQuotientEquiv
      (iwahoriQuotientData_isReductiveQuotient F N).1
      (iwahoriQuotientData_isReductiveQuotient F N).2.1).trans
    (diagTorusPointsEquiv F N)

@[simp] theorem iwahoriDepthZeroQuotientEquiv_mk
    (g : (iwahoriModelData F N).neutral.integralPoints) :
    iwahoriDepthZeroQuotientEquiv F N (QuotientGroup.mk g) =
      diagTorusPointsEquiv F N ((iwahoriQuotientData F N).parahoricReduction g) :=
  rfl

/-- The kernel of the general reduction on `I` is `I^+`. -/
theorem iwahoriQuotientData_ker_parahoricReduction :
    (iwahoriQuotientData F N).parahoricReduction.ker =
      (generalLinearIwahoriPositivePoints F N).subgroupOf
        (iwahoriModelData F N).neutral.integralPoints := by
  rw [(iwahoriQuotientData F N).ker_parahoricReduction
    (iwahoriQuotientData_isReductiveQuotient F N).2.1, iwahoriQuotientData_positivePoints]

/-- **The general index theorem for the Iwahori model**: `[I : I^+] = (q - 1)^N`, where
`q = |𝓀[F]|`, obtained from `localField_index_positivePoints_subgroupOf` and the count of
residue-field points of the diagonal torus. -/
theorem iwahori_index_positivePoints_subgroupOf :
    ((iwahoriQuotientData F N).positivePoints.subgroupOf
      (iwahoriModelData F N).neutral.integralPoints).index = (Nat.card 𝓀[F] - 1) ^ N := by
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _
    (iwahoriQuotientData_isReductiveQuotient F N).1
    (iwahoriQuotientData_isReductiveQuotient F N).2.1]
  exact card_diagTorus_rationalPoints F N

/-! ### `I` and `I^+` are compact open -/

section Topology

open Langlands.AlgebraicGeometry.PointTopology

local instance generalLinearIwahoriDepthZeroAffine :
    IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)

/-- `I` is open in `GL_N(F)` with its canonical topology. -/
theorem isOpen_generalLinearIwahoriPoints :
    letI : TopologicalSpace (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
      rationalPointTopology F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X
    IsOpen (generalLinearIwahoriPoints F N :
      Set (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))) := by
  rw [← iwahoriModelData_integralPoints]
  exact (iwahoriModelData F N).neutral.isOpen_integralPoints_localField

/-- `I` is compact in `GL_N(F)` with its canonical topology. -/
theorem isCompact_generalLinearIwahoriPoints :
    letI : TopologicalSpace (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
      rationalPointTopology F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X
    IsCompact (generalLinearIwahoriPoints F N :
      Set (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))) := by
  rw [← iwahoriModelData_integralPoints]
  exact (iwahoriModelData F N).neutral.isCompact_integralPoints_localField

/-- `I^+` is open in `GL_N(F)` with its canonical topology. -/
theorem isOpen_generalLinearIwahoriPositivePoints :
    letI : TopologicalSpace (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
      rationalPointTopology F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X
    IsOpen (generalLinearIwahoriPositivePoints F N :
      Set (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))) := by
  have : LocallyOfFiniteType (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.hom :=
    have := GeneralLinear.smoothStatement (Fin N) (CommRingCat.of F)
    inferInstance
  rw [← iwahoriQuotientData_positivePoints]
  exact (iwahoriQuotientData F N).localField_isOpen_positivePoints

/-- `I^+` is compact in `GL_N(F)` with its canonical topology. -/
theorem isCompact_generalLinearIwahoriPositivePoints :
    letI : TopologicalSpace (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
      rationalPointTopology F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X
    IsCompact (generalLinearIwahoriPositivePoints F N :
      Set (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))) := by
  have : LocallyOfFiniteType (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.hom :=
    have := GeneralLinear.smoothStatement (Fin N) (CommRingCat.of F)
    inferInstance
  rw [← iwahoriQuotientData_positivePoints]
  exact (iwahoriQuotientData F N).localField_isCompact_positivePoints

end Topology

end Langlands.BruhatTits.IntegralModels
