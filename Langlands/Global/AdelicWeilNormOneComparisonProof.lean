import Langlands.Global.AdelicWeilNormOneMap
import Langlands.GroupScheme.Rational.AffineCharacterNaturalValues
import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction
import Langlands.GroupScheme.AffineWeilEmbeddingProductPoints
import Langlands.Algebra.SeparableTensorProof
import Langlands.Algebra.TensorNormSplit
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Finset.NoncommProd

/-! # The canonical norm-one comparison for affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints AffineWeil WeilFactor
open Langlands.Algebra.SeparableTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000

section Characters

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.Etale F L] {G : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "W" => AffineWeil.groupScheme F L G

private def diagonalCharacterUnits (ψ : AlgebraicCharacter F W)
    (A : CommAlgCat.{u} (CommRingCat.of L)) : G.affinePoints A →* Aˣ :=
  (characterUnits F W ψ ((resA F L).obj A)).comp ((embNat F G).app A).hom

private theorem diagonalCharacterUnits_naturality (ψ : AlgebraicCharacter F W)
    {A B : CommAlgCat.{u} (CommRingCat.of L)} (f : A ⟶ B) (p : G.affinePoints A) :
    diagonalCharacterUnits ψ B (G.affinePointMap f p) =
      Units.map f.hom.toMonoidHom (diagonalCharacterUnits ψ A p) := by
  have h := ConcreteCategory.congr_hom ((embNat F G).naturality f) p
  change ((embNat F G).app B).hom (G.affinePointMap f p) =
    (W).affinePointMap ((resA F L).map f) (((embNat F G).app A).hom p) at h
  change characterUnits F W ψ ((resA F L).obj B)
      (((embNat F G).app B).hom (G.affinePointMap f p)) =
    Units.map ((resA F L).map f).hom.toRingHom.toMonoidHom
      (characterUnits F W ψ ((resA F L).obj A) (((embNat F G).app A).hom p))
  rw [h]
  exact characterUnits_naturality F W ψ ((resA F L).map f) (((embNat F G).app A).hom p)

/-- The restriction to the diagonal factor on each upper-field coefficient algebra. -/
private def diagonalCharacter (ψ : AlgebraicCharacter F W) : AlgebraicCharacter L G :=
  (AffineCharacterNaturalValues.character G (diagonalCharacterUnits ψ)
    (diagonalCharacterUnits_naturality ψ)).toMul

private theorem characterUnits_diagonalCharacter (ψ : AlgebraicCharacter F W)
    (A : CommAlgCat.{u} (CommRingCat.of L)) (p : G.affinePoints A) :
    characterUnits L G (diagonalCharacter ψ) A p =
      characterUnits F W ψ ((resA F L).obj A) (((embNat F G).app A).hom p) :=
  AffineCharacterNaturalValues.character_values G (diagonalCharacterUnits ψ)
    (diagonalCharacterUnits_naturality ψ) A p

end Characters

section SplitCoefficients

variable {F L Ω : Type u} [Field F] [Field L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [FiniteDimensional F L]
  [Algebra.Etale F L] {G : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

local notation "W" => AffineWeil.groupScheme F L G

variable (R : CommAlgCat.{u} (CommRingCat.of Ω))

private abbrev coefficientTest : CommAlgCat.{u} (CommRingCat.of F) := CommAlgCat.of F R

private abbrev conjugateTest (τ : L →ₐ[F] Ω) := embeddingCoefficientAlgebra F L Ω R τ

/-- The two ground-field structures on the conjugate coefficient ring agree. -/
private def forgetConjugate (τ : L →ₐ[F] Ω) :
    (resA F L).obj (conjugateTest R τ) ⟶ coefficientTest (F := F) R :=
  CommAlgCat.ofHom
    { RingHom.id R with
      commutes' a := congrArg (algebraMap Ω R) (τ.commutes a) }

variable [Finite (L →ₐ[F] Ω)] (hsplit : Function.Bijective (embeddingEvaluation F L Ω))

/-- Weil points over the split coefficient algebra as a product of actual conjugate points. -/
private def splitPoints : (W).affinePoints (coefficientTest (F := F) R) ≃*
    (∀ τ : L →ₐ[F] Ω, G.affinePoints (conjugateTest R τ)) :=
  (pointsEquiv F L G R).trans (tensorEmbeddingPointsEquiv F L Ω hsplit G R)

/-- Evaluation of a tensor after forgetting the conjugate scalar structure. -/
private def evaluateConjugate (τ σ : L →ₐ[F] Ω) :
    L ⊗[F] (resA F L).obj (conjugateTest R τ) →ₐ[L] conjugateTest R σ :=
  ((tensorEmbeddingEvaluationMap F L Ω hsplit R σ).hom).comp
    (Algebra.TensorProduct.lTensor (S := L) L (forgetConjugate R τ).hom)

omit [FiniteDimensional F L] [Algebra.Etale F L] in
private theorem evaluateConjugate_tmul (τ σ : L →ₐ[F] Ω) (b : L)
    (r : (resA F L).obj (conjugateTest R τ)) :
    (show R from evaluateConjugate R hsplit τ σ (b ⊗ₜ[F] r)) =
      algebraMap Ω R (σ b) * (show R from r) := by
  change tensorEmbeddingEvaluation F L Ω hsplit R σ
    (b ⊗ₜ[F] ((forgetConjugate R τ).hom r)) = _
  exact tensorEmbeddingEvaluation_tmul F L Ω hsplit R σ b (show R from r)

omit [FiniteDimensional F L] [Algebra.Etale F L] in
private theorem evaluateConjugate_self (τ : L →ₐ[F] Ω) :
    evaluateConjugate R hsplit τ τ = mulMap F (conjugateTest R τ) := by
  apply AlgHom.ext
  intro x
  induction x with
  | tmul b r =>
    change (show R from evaluateConjugate R hsplit τ τ (b ⊗ₜ[F] r)) =
      (show R from Langlands.Algebra.GraphIdempotent.graphMul
        (structureMap F (conjugateTest R τ)) (b ⊗ₜ[F] r))
    rw [evaluateConjugate_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [FiniteDimensional F L] in
private theorem evaluateConjugate_graphIdem_of_ne {τ σ : L →ₐ[F] Ω} (h : σ ≠ τ) :
    evaluateConjugate R hsplit τ σ (graphIdem F (conjugateTest R τ)) = 0 := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : L, σ b ≠ τ b := by
    by_contra! h'
    exact h (AlgHom.ext h')
  let e := graphIdem F (conjugateTest R τ)
  let X := (resA F L).obj (conjugateTest R τ)
  let a : L ⊗[F] X →+* R := (evaluateConjugate R hsplit τ σ).toRingHom
  let r : X := structureMap F (conjugateTest R τ) b
  have hgraph : (b ⊗ₜ[F] (1 : X)) * e = ((1 : L) ⊗ₜ[F] r) * e :=
    (graphIdem_spec (A := F) (conjugateTest R τ)).tmul_one_mul b
  have hleft : a (b ⊗ₜ[F] (1 : X)) = algebraMap Ω R (σ b) := by
    have hmul := evaluateConjugate_tmul R hsplit τ σ b (1 : X)
    change a (b ⊗ₜ[F] (1 : X)) = algebraMap Ω R (σ b) * 1 at hmul
    rwa [mul_one] at hmul
  have hright : a ((1 : L) ⊗ₜ[F] r) = algebraMap Ω R (τ b) := by
    have hmul := evaluateConjugate_tmul R hsplit τ σ 1 r
    change a ((1 : L) ⊗ₜ[F] r) = algebraMap Ω R (σ 1) * algebraMap Ω R (τ b) at hmul
    rwa [map_one, map_one, one_mul] at hmul
  have he := congrArg a hgraph
  rw [map_mul, map_mul, hleft, hright] at he
  have hu : IsUnit (algebraMap Ω R (σ b - τ b)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hb)).map (algebraMap Ω R)
  change a e = 0
  apply hu.mul_right_eq_zero.mp
  rw [map_sub, sub_mul, he, sub_self]

/-- On split tests, the transported graph factor is the indicated single coordinate. -/
private theorem splitPoints_embNat (τ : L →ₐ[F] Ω) (p : G.affinePoints (conjugateTest R τ))
    [DecidableEq (L →ₐ[F] Ω)] :
    splitPoints (G := G) R hsplit
      ((W).affinePointMap (forgetConjugate R τ) (((embNat F G).app (conjugateTest R τ)).hom p)) =
      Pi.mulSingle τ p := by
  let X := (resA F L).obj (conjugateTest R τ)
  let w : (W).affinePoints X := ((embNat F G).app (conjugateTest R τ)).hom p
  let q : G.affinePoints (CommAlgCat.of L (L ⊗[F] X)) := pointsEquiv F L G X w
  have hn : pointsEquiv F L G R ((W).affinePointMap (forgetConjugate R τ) w) =
      G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := L) L
        (forgetConjugate R τ).hom)) q :=
    pointsEquiv_naturality F L G (forgetConjugate R τ).hom w
  have hcoordinates (σ : L →ₐ[F] Ω) :
      splitPoints (G := G) R hsplit ((W).affinePointMap (forgetConjugate R τ) w) σ =
        G.affinePointMap (CommAlgCat.ofHom (evaluateConjugate R hsplit τ σ)) q := by
    change tensorEmbeddingPointsEquiv F L Ω hsplit G R
      (pointsEquiv F L G R ((W).affinePointMap (forgetConjugate R τ) w)) σ = _
    rw [hn, tensorEmbeddingPointsEquiv_apply, ← MonoidHom.comp_apply,
      ← GroupScheme.affinePointMap_comp]
    rfl
  funext σ
  rw [hcoordinates]
  by_cases h : σ = τ
  · subst σ
    rw [Pi.mulSingle_eq_same, evaluateConjugate_self]
    have hdiag := projNat_embNat_apply (A := F) G (conjugateTest R τ) p
    change G.affinePointMap (CommAlgCat.ofHom (mulMap F (conjugateTest R τ))) q = p at hdiag
    exact hdiag
  · rw [Pi.mulSingle_eq_of_ne h]
    let e := graphIdem F (conjugateTest R τ)
    have he := (graphIdem_spec (A := F) (conjugateTest R τ)).isIdempotentElem
    have hsnd : IdempotentPoints.snd G e q = 1 := by
      change IdempotentPoints.snd G e ((pointsEquiv F L G X)
        ((pointsEquiv F L G X).symm ((factorEquivX F G (conjugateTest R τ)).symm p).1)) = 1
      rw [MulEquiv.apply_symm_apply]
      exact ((factorEquivX F G (conjugateTest R τ)).symm p).2
    have hproj : q = IdempotentPoints.proj G e q :=
      (IdempotentPoints.eq_proj_iff G he).mpr ⟨rfl, hsnd⟩
    have heval : evaluateConjugate R hsplit τ σ e = 0 :=
      evaluateConjugate_graphIdem_of_ne R hsplit h
    rw [hproj, IdempotentPoints.proj_map G _ he heval, IdempotentPoints.proj_zero]

/-- The split coefficient-first tensor as an algebra over the coefficient ring. -/
private def normSplitEquiv : R ⊗[F] L ≃ₐ[R] ((L →ₐ[F] Ω) → R) where
  __ := (Algebra.TensorProduct.comm F R L).toRingEquiv.trans
    (tensorEmbeddingEquiv F L Ω hsplit R)
  commutes' r := by
    funext τ
    change tensorEmbeddingEquiv F L Ω hsplit R ((1 : L) ⊗ₜ[F] r) τ = r
    rw [tensorEmbeddingEquiv_tmul, map_one, map_one, one_mul]

/-- In split coordinates, the transferred character has the product of the coordinate values. -/
private theorem normCharacter_val_split [Fintype (L →ₐ[F] Ω)] [DecidableEq (L →ₐ[F] Ω)]
    (χ : AlgebraicCharacter L G) (p : (W).affinePoints (coefficientTest (F := F) R)) :
    (show R from (characterUnits F W (AffineWeil.normCharacter F L G χ) (coefficientTest R) p).val) =
      ∏ σ : L →ₐ[F] Ω, (show R from
        (characterUnits L G χ (conjugateTest R σ) (splitPoints (G := G) R hsplit p σ)).val) := by
  let A := coefficientTest (F := F) R
  let T := CommAlgCat.of L (L ⊗[F] R)
  let q : G.affinePoints T := pointsEquiv F L G R p
  let v : (L ⊗[F] R)ˣ := characterUnits L G χ T q
  have hn : characterUnits F W (AffineWeil.normCharacter F L G χ) A p =
      Langlands.Algebra.tensorNormUnits F L A v :=
    normCharacter_affineUnits F L G χ A p
  calc
    _ = Langlands.Algebra.tensorNorm F L R (v : L ⊗[F] R) := congrArg Units.val hn
    _ = ∏ σ : L →ₐ[F] Ω, tensorEmbeddingEvaluation F L Ω hsplit R σ (v : L ⊗[F] R) := by
      rw [Langlands.Algebra.tensorNorm_eq_prod (normSplitEquiv R hsplit)]
      apply Finset.prod_congr rfl
      intro σ _
      change tensorEmbeddingEvaluation F L Ω hsplit R σ
          (Algebra.TensorProduct.comm F R L (Algebra.TensorProduct.comm F L R (v : L ⊗[F] R))) =
        tensorEmbeddingEvaluation F L Ω hsplit R σ (v : L ⊗[F] R)
      rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro σ _
      let f := tensorEmbeddingEvaluationMap F L Ω hsplit R σ
      have hp : splitPoints (G := G) R hsplit p σ = G.affinePointMap f q :=
        tensorEmbeddingPointsEquiv_apply F L Ω hsplit G R q σ
      rw [hp]
      exact (congrArg Units.val (characterUnits_naturality L G χ f q)).symm

include hsplit in
private theorem characterUnits_normCharacter_split (ψ : AlgebraicCharacter F W)
    (p : (W).affinePoints (coefficientTest (F := F) R)) :
    characterUnits F W ψ (coefficientTest R) p =
      characterUnits F W (AffineWeil.normCharacter F L G (diagonalCharacter ψ))
        (coefficientTest R) p := by
  classical
  let : Fintype (L →ₐ[F] Ω) := Fintype.ofFinite _
  let A := coefficientTest (F := F) R
  let e := splitPoints (G := G) R hsplit
  let χ := diagonalCharacter ψ
  let f := (characterUnits F W ψ A).comp e.symm.toMonoidHom
  let g := (characterUnits F W (AffineWeil.normCharacter F L G χ) A).comp e.symm.toMonoidHom
  have h : f = g := by
    apply MonoidHom.pi_ext
    intro τ x
    let X := conjugateTest R τ
    let w : (W).affinePoints ((resA F L).obj X) := ((embNat F G).app X).hom x
    let y : (W).affinePoints A := (W).affinePointMap (forgetConjugate R τ) w
    have hy : e y = Pi.mulSingle τ x := splitPoints_embNat R hsplit τ x
    change characterUnits F W ψ A (e.symm (Pi.mulSingle τ x)) =
      characterUnits F W (AffineWeil.normCharacter F L G χ) A (e.symm (Pi.mulSingle τ x))
    rw [← hy, MulEquiv.symm_apply_apply]
    apply Units.ext
    change (show R from (characterUnits F W ψ A y).val) =
      (show R from (characterUnits F W (AffineWeil.normCharacter F L G χ) A y).val)
    have hv : (show R from (characterUnits F W ψ A y).val) =
        (show R from (characterUnits L G χ X x).val) := by
      have hn := characterUnits_naturality F W ψ (forgetConjugate R τ) w
      have hs := characterUnits_diagonalCharacter ψ X x
      exact (congrArg Units.val hn).trans (congrArg Units.val hs).symm
    rw [normCharacter_val_split R hsplit χ y, hv]
    change (show R from (characterUnits L G χ X x).val) =
      ∏ σ : L →ₐ[F] Ω, (show R from (characterUnits L G χ (conjugateTest R σ) (e y σ)).val)
    rw [hy, Finset.prod_eq_single_of_mem τ (Finset.mem_univ τ)]
    · rw [Pi.mulSingle_eq_same]
    · intro σ _ hne
      rw [Pi.mulSingle_eq_of_ne hne, map_one]
      rfl
  have hp := DFunLike.congr_fun h (e p)
  change characterUnits F W ψ A (e.symm (e p)) =
    characterUnits F W (AffineWeil.normCharacter F L G χ) A (e.symm (e p)) at hp
  rwa [MulEquiv.symm_apply_apply] at hp

end SplitCoefficients

section Descent

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra.Etale F L] {G : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "W" => AffineWeil.groupScheme F L G

/-- The original character and the norm transfer agree on every affine test. -/
private theorem characterUnits_normCharacter (ψ : AlgebraicCharacter F W)
    (A : CommAlgCat.{u} (CommRingCat.of F)) (p : (W).affinePoints A) :
    characterUnits F W ψ A p =
      characterUnits F W (AffineWeil.normCharacter F L G (diagonalCharacter ψ)) A p := by
  let Ω := AlgebraicClosure F
  let R : CommAlgCat.{u} (CommRingCat.of Ω) := CommAlgCat.of Ω (Ω ⊗[F] A)
  let B := coefficientTest (F := F) (Ω := Ω) R
  let j₀ : A →ₐ[F] Ω ⊗[F] A := Algebra.TensorProduct.includeRight
  let f : A →+* (Ω ⊗[F] A) := j₀.toRingHom
  have hcomm (a : F) :
      (1 : Ω) ⊗ₜ[F] (algebraMap F A a) = (algebraMap F Ω a) ⊗ₜ[F] (1 : A) :=
    j₀.commutes a
  let j : A ⟶ B := by
    letI : Algebra (CommRingCat.of F) B := B.algebra
    refine CommAlgCat.ofHom (X := A) (Y := B) { f with commutes' := ?_ }
    exact hcomm
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap F Ω).injective
  have hsplit : Function.Bijective (embeddingEvaluation F L Ω) :=
    embeddingEvaluationStatement F L Ω (fun _ => IsAlgClosed.splits _)
  have h := characterUnits_normCharacter_split R hsplit ψ ((W).affinePointMap j p)
  rw [characterUnits_naturality, characterUnits_naturality] at h
  exact Units.map_injective (f := f.toMonoidHom) hf h

end Descent

/-- The canonical adelic Weil comparison identifies the full actual norm-one subgroups,
and preserves the topology and the canonical principal points. -/
theorem normOneComparison : NormOneComparisonStatement.{u} := by
  intro F L _ _ _ _ _ G _ _
  refine ⟨isHomeomorph_adelicPointsEquiv F L G, adelicPointsEquiv_rational F L G,
    le_antisymm (map_normOneSubgroup_le F L G) ?_⟩
  intro x hx
  let p := (adelicPointsEquiv F L G).symm x
  have hp : adelicPointsEquiv F L G p = x := (adelicPointsEquiv F L G).apply_symm_apply x
  refine ⟨p, ?_, hp⟩
  change p ∈ normOneSubgroup F (AffineWeil.groupScheme F L G)
  apply (mem_normOneSubgroup F (AffineWeil.groupScheme F L G) p).mpr
  intro ψ
  let : Algebra.Etale F L :=
    ⟨Algebra.FormallyEtale.of_isSeparable F L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let χ := diagonalCharacter ψ
  have he := characterUnits_normCharacter ψ (CommAlgCat.of F (Adeles F)) p
  have hnorm :
      characterNorm F (AffineWeil.groupScheme F L G) ψ p =
        characterNorm F (AffineWeil.groupScheme F L G) (normCharacter F L G χ) p :=
    congrArg (IdeleAbsoluteValue.full F) he
  rw [hnorm, characterNorm_normCharacter_apply, hp]
  exact (mem_normOneSubgroup L G x).mp hx χ

end Langlands.Global.AdelicWeilRestriction
