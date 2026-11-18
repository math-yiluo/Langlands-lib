import Langlands.GroupScheme.IdentityJetAffineConjugation
import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetSectionAlgebras

/-! # Actual conjugate subgroup jet and algebraic orbit kernels -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineCoordinates Corepresented IdentityJet

attribute [local instance] IdentityJet.jetSectionAlgebra

private theorem map_universalCutPoint_of_coordinates
    {R : CommRingCat.{u}} {F : CommAlgCat R ⥤ GrpCat.{u}} {B : CommAlgCat R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) (K : Ideal B)
    {A C : CommAlgCat R} (φ : tensorQuotient K A ⟶ C)
    (y : (algSpec R).obj (op C) ⟶ (groupScheme F e).X)
    (hy : ∀ c : B, (e.homEquiv.symm (affinePointsEquiv F e C y)).hom c =
      φ.hom (1 ⊗ₜ[R] Ideal.Quotient.mk K c)) :
    F.map φ (universalCutPoint e K A) = affinePointsEquiv F e C y := by
  apply e.homEquiv.symm.injective
  rw [homEquiv_symm_map, universalCutPoint, Equiv.symm_apply_apply]
  apply CommAlgCat.hom_ext
  ext c
  exact (hy c).symm

private theorem orbitMap_tmul_classifying
    {R : CommRingCat.{u}} {F : CommAlgCat R ⥤ GrpCat.{u}} {B : CommAlgCat R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) {m : ℕ} {K : Ideal B}
    (hK : augIdeal e ^ m ≤ K) {A : CommAlgCat R} (g : F.obj A) (a : A) (c : B) :
    (orbitMap e hK g).hom (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • (e.homEquiv.symm (universalCutConj e K g)).hom c := by
  change (a ⊗ₜ[R] 1) * (e.homEquiv.symm (universalCutConj e K g)).hom c = _
  exact (smul_eq_tmul_one_mul a _).symm

private theorem tensorCoordinates_tmul_jet {R : CommRingCat.{u}} {S : Scheme.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left] (b : S ⟶ Spec R)
    (K : GroupScheme S) [IsAffineHom K.X.hom] (j : K ⟶ (GroupScheme.baseChange b).obj G)
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ambientTensorCoordinates G b j n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • jetCoordinateMap K (ambientProjection G b j) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  rw [ambientTensorCoordinates_tmul, ambientQuotientCoordinates,
    quotientCoordinates_mk, jetCoordinateMap_restrict]

namespace SelfNormalizingAmbient.ProperQuotientJetData

attribute [local instance] IdentityJet.jetSectionAlgebra

private theorem source_affine {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine G.X.left] {i : H ⟶ G} (hi : IsClosedSubgroup i) : IsAffineHom H.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

private theorem baseChange_affine {S T : Scheme.{u}} (K : GroupScheme S)
    [IsAffineHom K.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom := by
  change IsAffineHom (Limits.pullback.snd K.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChange_affine

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i}
  (D : ProperQuotientJetData i Q)
  {S : Scheme.{u}} (b : S ⟶ Spec R)
  (g : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X)

/-- The algebraic orbit quotient attached to the actual conjugating section. -/
def conjugateOrbitMap (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →ₗ[Γ(S, U)]
      Γ(S, U) ⊗[R] (algebra G ⧸ jetIdeal (corepresentation G) D.ideal n) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact orbitLinearMap (corepresentation G)
    (show augIdeal (corepresentation G) ^ (n + 1) ≤
      jetIdeal (corepresentation G) D.ideal n from le_sup_right)
    (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(S, U))
      (parameterAffinePoint G b g U))

/-- The actual original jet algebra comparison over the original base ring. -/
def originalJetAlgebraHom (hi : IsClosedSubgroup i) (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    tensorQuotient (jetIdeal (corepresentation G) D.ideal n) (CommAlgCat.of R Γ(S, U)) ⟶
      CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  letI := jetSectionScalarTower H_b b n U
  exact CommAlgCat.ofHom ((D.originalBaseChangeJetAlgEquiv b hi n U).restrictScalars R).toAlgHom

/-- This base-ring homomorphism retains the actual coordinate formula. -/
theorem originalJetAlgebraHom_tmul_mk (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    (D.originalJetAlgebraHom b hi n U).hom
        (a ⊗ₜ[R] Ideal.Quotient.mk (jetIdeal (corepresentation G) D.ideal n) c) =
      a • jetCoordinateMap H_b (ambientProjection G b ((GroupScheme.baseChange b).map i)) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  exact D.originalBaseChangeJetAlgEquiv_tmul_mk b hi n U a c

/-- The original actual affine jet point is the transported universal cut point. -/
theorem originalJetAffinePoint_eq_universal (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    letI : IsAffineHom H.X.hom := source_affine hi
    (functor G).map (D.originalJetAlgebraHom b hi n U)
        (universalCutPoint (corepresentation G) (jetIdeal (corepresentation G) D.ideal n)
          (CommAlgCat.of R Γ(S, U))) =
      affinePointsEquiv (functor G) (corepresentation G)
        (CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U))
        (affineJetPoint H_b (functor G) (corepresentation G) b
          (ambientProjection G b ((GroupScheme.baseChange b).map i))
          (ambientProjection_over G b ((GroupScheme.baseChange b).map i)) n U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  let : IsAffineHom H.X.hom := source_affine hi
  apply map_universalCutPoint_of_coordinates
  intro c
  have hc := congrArg (fun f : algebra G →+*
      Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U) => f c)
    (affineJetPoint_coordinates H_b (functor G) (corepresentation G) b
      (ambientProjection G b ((GroupScheme.baseChange b).map i))
      (ambientProjection_over G b ((GroupScheme.baseChange b).map i)) n U)
  exact hc.trans (by
    simpa only [one_smul] using (D.originalJetAlgebraHom_tmul_mk b hi n U 1 c).symm)

/-- The transported coefficient map is exactly actual jet projection on functions. -/
theorem originalJetAlgebraHom_left (hi : IsClosedSubgroup i) (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    ((tensorQuotientLeft (jetIdeal (corepresentation G) D.ideal n) (CommAlgCat.of R Γ(S, U)) ≫
      D.originalJetAlgebraHom b hi n U).hom.toRingHom) =
      ((projection H_b n).app U).hom := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  ext a
  change D.originalBaseChangeJetAlgEquiv b hi n U (a ⊗ₜ[R] 1) = _
  exact (D.originalBaseChangeJetAlgEquiv b hi n U).commutes a

/-- The actual jet conjugator is the actual parameter point under this coefficient map. -/
theorem jetConjugatorPoint_eq_mapParameter (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    letI : IsAffineHom H.X.hom := source_affine hi
    affinePointsEquiv (functor G) (corepresentation G)
        (CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U))
        (jetConjugatorPoint G b (H := H_b) g n U) =
      (functor G).map
        (tensorQuotientLeft (jetIdeal (corepresentation G) D.ideal n) (CommAlgCat.of R Γ(S, U)) ≫
          D.originalJetAlgebraHom b hi n U)
        (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(S, U))
          (parameterAffinePoint G b g U)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  let : IsAffineHom H.X.hom := source_affine hi
  let φ := tensorQuotientLeft (jetIdeal (corepresentation G) D.ideal n) (CommAlgCat.of R Γ(S, U)) ≫
    D.originalJetAlgebraHom b hi n U
  exact (congrArg (affinePointsEquiv (functor G) (corepresentation G)
      (CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U)))
    (jetConjugatorPoint_eq_parameterPullback G b (H := H_b) g n U φ
      (D.originalJetAlgebraHom_left b hi n U))).trans
        (affinePointsEquiv_naturality (functor G) (corepresentation G) φ
          (parameterAffinePoint G b g U))

/-- The actual conjugated affine jet point is the transported universal cut conjugate. -/
theorem conjugateJetAffinePoint_eq_universal (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    letI : IsAffineHom H.X.hom := source_affine hi
    (functor G).map (D.originalJetAlgebraHom b hi n U)
        (universalCutConj (corepresentation G) (jetIdeal (corepresentation G) D.ideal n)
          (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(S, U))
            (parameterAffinePoint G b g U))) =
      affinePointsEquiv (functor G) (corepresentation G)
        (CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U))
        (affineJetPoint H_b (functor G) (corepresentation G) b
          (ambientProjection G b ((GroupScheme.baseChange b).map i ≫
            (((GroupScheme.baseChange b).obj G).innerIso g).hom))
          (ambientProjection_over G b _) n U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  let : IsAffineHom H.X.hom := source_affine hi
  rw [map_universalCutConj, D.originalJetAffinePoint_eq_universal]
  have hp := congrArg (affinePointsEquiv (functor G) (corepresentation G)
      (CommAlgCat.of R Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U)))
    (affineJetPoint_inner G b ((GroupScheme.baseChange b).map i) g n U)
  simp only [map_mul, map_inv] at hp
  rw [D.jetConjugatorPoint_eq_mapParameter b g hi n U] at hp
  exact hp.symm

/-- The classifying coordinate of the universal cut conjugate is the actual conjugate jet function. -/
theorem originalJetAlgebraHom_conjugateCoordinate (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
      (projection H_b n ⁻¹ᵁ U)
    (D.originalJetAlgebraHom b hi n U).hom
        (((corepresentation G).homEquiv.symm
          (universalCutConj (corepresentation G) (jetIdeal (corepresentation G) D.ideal n)
            (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(S, U))
              (parameterAffinePoint G b g U)))).hom c) =
      jetCoordinateMap H_b
        (ambientProjection G b ((GroupScheme.baseChange b).map i ≫
          (((GroupScheme.baseChange b).obj G).innerIso g).hom)) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  let : IsAffineHom H.X.hom := source_affine hi
  have hp := D.conjugateJetAffinePoint_eq_universal b g hi n U
  have hc := congrArg (fun y => ((corepresentation G).homEquiv.symm y).hom c) hp
  rw [homEquiv_symm_map] at hc
  exact hc.trans (congrArg (fun f : algebra G →+*
      Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U) => f c)
    (affineJetPoint_coordinates H_b (functor G) (corepresentation G) b
      (ambientProjection G b ((GroupScheme.baseChange b).map i ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom))
      (ambientProjection_over G b _) n U))

/-- Actual conjugate jet restriction factors through the algebraic orbit map. -/
theorem originalBaseChangeJetEquiv_comp_conjugateOrbit (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : IsAffineHom H.X.hom := source_affine hi
    (D.originalBaseChangeJetEquiv b hi n U).toLinearMap.comp (D.conjugateOrbitMap b g n U) =
      ambientTensorCoordinates G b ((GroupScheme.baseChange b).map i ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom) n U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H_b := (GroupScheme.baseChange b).obj H
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H_b n ≫ b)
    (projection H_b n ⁻¹ᵁ U)
  let : IsAffineHom H.X.hom := source_affine hi
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    change D.originalBaseChangeJetEquiv b hi n U
      ((orbitMap (corepresentation G) le_sup_right
        (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(S, U))
          (parameterAffinePoint G b g U))).hom
        (a ⊗ₜ[R] Ideal.Quotient.mk _ c)) = _
    rw [orbitMap_tmul_classifying, (D.originalBaseChangeJetEquiv b hi n U).map_smul]
    have hc := D.originalJetAlgebraHom_conjugateCoordinate b g hi n U c
    change D.originalBaseChangeJetEquiv b hi n U _ = _ at hc
    exact (congrArg (a • ·) hc).trans
      (tensorCoordinates_tmul_jet G b H_b ((GroupScheme.baseChange b).map i ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom) n U a c).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The actual conjugate subgroup jet restriction has exactly the algebraic orbit kernel. -/
theorem ker_conjugateTensorCoordinates (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : IsAffineHom H.X.hom := source_affine hi
    LinearMap.ker (ambientTensorCoordinates G b ((GroupScheme.baseChange b).map i ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom) n U) =
      LinearMap.ker (D.conjugateOrbitMap b g n U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : IsAffineHom H.X.hom := source_affine hi
  rw [← D.originalBaseChangeJetEquiv_comp_conjugateOrbit b g hi n U]
  ext z
  change D.originalBaseChangeJetEquiv b hi n U (D.conjugateOrbitMap b g n U z) = 0 ↔
    D.conjugateOrbitMap b g n U z = 0
  exact (D.originalBaseChangeJetEquiv b hi n U).map_eq_zero_iff

end SelfNormalizingAmbient.ProperQuotientJetData
end Langlands.GroupScheme
