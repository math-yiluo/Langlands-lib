import Langlands.GroupScheme.Reductive.DominantMultipleExterior
import Langlands.GroupScheme.Reductive.ExtremalMatrixCoefficient
import Langlands.GroupScheme.Reductive.CovariantCellFixedLine
import Langlands.GroupScheme.Dynamic.PositiveWeightParabolicDistinction
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Normalized covariant coordinates from top weight lines -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DominantMultiple

open AffineCoordinates

variable {k : Type u} [Field k]
  {G H P Q U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom P.X.hom] [IsAffineHom Q.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Evaluating a restricted character is evaluating the original character on the image
point. -/
theorem characterEval_characterRestrict {K L : GroupScheme (Spec (CommRingCat.of k))}
    (f : K ⟶ L) (ψ : rationalCharacters L) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ K.X) :
    characterEval (characterRestrict f ψ) T x = characterEval ψ T (x ≫ f.hom.hom) := by
  rw [characterEval_apply, characterEval_apply, characterRestrict_apply, Grp.comp_hom_hom,
    Category.assoc]

/-- Left covariance restricts along a factorization through the covariance group. -/
theorem mem_leftCovariantSubspace_restrict (iP : P ⟶ G) (i : H ⟶ G) (fP : H ⟶ P)
    (hfP : fP ≫ iP = i) (ψ : rationalCharacters P) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace iP (characterCoordinate P ψ)) :
    f ∈ leftCovariantSubspace i (characterCoordinate H (characterRestrict fP ψ)) := by
  rw [mem_leftCovariantSubspace_iff_points] at hf ⊢
  intro T h g
  have hh : h ≫ i.hom.hom = (h ≫ fP.hom.hom) ≫ iP.hom.hom := by
    rw [← hfP, Grp.comp_hom_hom, Category.assoc]
  rw [hh, hf T (h ≫ fP.hom.hom) g, pointAlgebraHom_characterCoordinate,
    pointAlgebraHom_characterCoordinate, characterEval_characterRestrict]

/-- Value one at the identity on every test gives counit one. -/
theorem counit_eq_one_of_forall {f : algebra G}
    (hf : ∀ T : Over (Spec (CommRingCat.of k)), pointAlgebraHom G T 1 f = 1) :
    AffineLinearEmbedding.counit (corepresentation G) f = 1 := by
  have h := hf (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  rw [pointAlgebraHom_one_apply] at h
  have : Nontrivial ((algΓ (CommRingCat.of k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  apply (algebraMap k ((algΓ (CommRingCat.of k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop).injective
  rw [h, map_one]

/-- A normalized covariant coordinate from the top weight line of an exterior power. Its
covariance character is computed on the image of the cocharacter. -/
theorem exists_topWeight_coefficient {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : Fin N → ℤ)
    (he : χ ≫ ρ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e)
    (M : ℤ) (hM : ∀ a, e a ≤ M)
    (iP : P ⟶ G) (hP : (Dynamic.parabolic (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iP)
    (iQ : Q ⟶ G) (hQ : (Dynamic.parabolic χ).IsRepresentedBy iQ)
    (i : H ⟶ G) (fP : H ⟶ P) (hfP : fP ≫ iP = i)
    (j : U ⟶ G) (κ : U ⟶ Q) (hκ : κ ≫ iQ = j)
    (hU : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ U.X) (ψ : rationalCharacters Q),
      characterEval ψ T (u ≫ κ.hom.hom) = 1) :
    ∃ (ψ : rationalCharacters P) (f : algebra G),
      f ∈ leftCovariantSubspace i (characterCoordinate H (characterRestrict fP ψ)) ∧
      f ∈ rightInvariantSubspace j ∧
      AffineLinearEmbedding.counit (corepresentation G) f = 1 ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
        (x : T ⟶ P.X), x ≫ iP.hom.hom = t ≫ χ.hom.hom →
          characterEval ψ T x =
            Gm.pointsEquiv _ T t ^ ((Chevalley.topCard e M : ℤ) * M) := by
  classical
  let d := Chevalley.topCard e M
  let ρ' := Chevalley.exteriorRepresentation N d (CommRingCat.of k) ρ
  let w : Set.powersetCard (Fin N) d → ℤ := fun s => ∑ a ∈ (s : Finset (Fin N)), e a
  have hw : χ ≫ ρ' = GeneralLinear.diagonalCocharacter _ (CommRingCat.of k) w := by
    change χ ≫ (ρ ≫ Chevalley.exteriorGroupHom N d (CommRingCat.of k)) = _
    rw [← Category.assoc, he, Chevalley.diagonalCocharacter_comp_exteriorGroupHom]
  let ν := Dynamic.oppositeCocharacter χ
  have hν : ν ≫ ρ' = GeneralLinear.diagonalCocharacter _ (CommRingCat.of k) (-w) :=
    MatrixRepresentation.oppositeCocharacter_comp ρ' χ w hw
  let s₀ := Chevalley.topPoint e M
  have hs₀ : ∀ s, s ≠ s₀ → (-w) s₀ < (-w) s := fun s hs =>
    neg_lt_neg (Chevalley.sum_lt_sum_topPoint e M hM s hs)
  have hQ' : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ := by
    simpa only [ν, Dynamic.oppositeCocharacter_oppositeCocharacter] using hQ
  let ψ := MatrixRepresentation.minimumWeightCharacter ρ' ν (-w) hν iP hP s₀ hs₀
  refine ⟨ψ, diagonalMatrixCoefficient ρ' s₀, ?_, ?_, ?_, ?_⟩
  · exact mem_leftCovariantSubspace_restrict iP i fP hfP ψ
      (diagonalMatrixCoefficient_mem_leftCovariantSubspace ρ' ν (-w) hν iP hP s₀ hs₀)
  · rw [mem_rightInvariantSubspace]
    intro T u g
    have hinv := pointAlgebraHom_mul_inv_diagonalMatrixCoefficient ρ' ν (-w) hν s₀ hs₀
      iQ hQ' T (u ≫ κ.hom.hom)⁻¹ g
    have hu : ((u ≫ κ.hom.hom)⁻¹ ≫ iQ.hom.hom)⁻¹ = u ≫ j.hom.hom := by
      rw [GrpObj.inv_comp, inv_inv, ← hκ, Grp.comp_hom_hom, Category.assoc]
    rw [hu] at hinv
    rw [hinv, pointAlgebraHom_characterCoordinate, characterEval_neg, map_inv, hU]
    simp
  · exact counit_eq_one_of_forall fun T => pointAlgebraHom_one_diagonalMatrixCoefficient ρ' s₀ T
  · intro T t x hx
    apply Units.ext
    rw [MatrixRepresentation.minimumWeightCharacter_eval, hx]
    have hpm : ρ'.pointMatrix T (t ≫ χ.hom.hom) =
        GeneralLinear.diagonalUnits Γ(T.left, ⊤) w (Gm.pointsEquiv _ T t) := by
      rw [MatrixRepresentation.pointMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, hw,
        GeneralLinear.pointsEquiv_diagonalCocharacter]
    rw [hpm, GeneralLinear.coe_diagonalUnits, Matrix.diagonal_apply_eq]
    have hws : w s₀ = (Chevalley.topCard e M : ℤ) * M := Chevalley.sum_topPoint e M
    rw [hws]

/-! ### Pairings computed on cocharacter points -/

section Pairing

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A character whose values along a cocharacter are the `c`-th powers pairs to `c` with it. -/
theorem latticePairing_eq_of_points (σ : characterLattice T) (mu : cocharacterLattice T) (c : ℤ)
    (h : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ (Gm (Spec (CommRingCat.of k))).X),
      Gm.pointsEquiv _ V (t ≫ (CommGroupScheme.groupHom mu).hom.hom ≫
        (CommGroupScheme.groupHom σ).hom.hom) = Gm.pointsEquiv _ V t ^ c) :
    latticePairing T σ mu = c := by
  have hmuσ : mu ≫ σ = (gmEndEquiv k).symm c := by
    apply CommGroupScheme.hom_ext_points
    intro V t
    rw [gmEndEquiv_symm_comp, comp_groupHom_comp]
    apply (Gm.pointsEquiv _ V).injective
    rw [map_zpow, Category.assoc, h]
  rw [latticePairing_apply, hmuσ, AddEquiv.apply_symm_apply]

end Pairing

/-! ### Conjugation invariance of characters -/

section Conjugation

/-- Rational characters are invariant under inner automorphisms. -/
theorem innerIso_hom_comp_character {K : GroupScheme (Spec (CommRingCat.of k))}
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X) (ψ : rationalCharacters K) :
    (K.innerIso n).hom ≫ ψ.toMul = ψ.toMul := by
  apply hom_ext_points
  intro V x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  apply (Gm.pointsEquiv _ V).injective
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_mul, map_inv,
    mul_comm (Gm.pointsEquiv _ V _), mul_assoc, mul_inv_cancel, mul_one]

/-- A rational point fixing a cocharacter under conjugation lies in its dynamic centralizer. -/
theorem mem_centralizer_of_comp_innerIso {K : GroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ K)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X)
    (h : χ ≫ (K.innerIso n).hom = χ) :
    n ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer]
  intro V a t
  have ha : a ≫ n = K.constantPoint n V := by
    have : a = Over.homMk V.hom (by simp) := by
      ext
      simpa using Over.w a
    rw [this]
    rfl
  rw [ha]
  have hc := congrArg (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ K =>
    t ≫ f.hom.hom) h
  simp only [Grp.comp_hom_hom] at hc
  rw [← Category.assoc, comp_innerIso_hom] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc)

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

omit [IsAffineHom G.X.hom] [IsAffineHom P.X.hom] in
/-- A character of a group containing a normalizing point is fixed by the corresponding
automorphism of the torus. -/
theorem characterAut_characterRestrict_eq (iP : P ⟶ G) (hiP : Mono iP.hom.hom)
    (tP : T.toGrp ⟶ P) (incl : T.toGrp ⟶ G) (htP : tP ≫ iP = incl)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : T ≅ T)
    (hn : IsNormalizingPoint incl n σ)
    (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) (hn' : n' ≫ iP.hom.hom = n)
    (ψ : rationalCharacters P) :
    characterAut σ (rationalCharacters.equivCharacterLattice T (characterRestrict tP ψ)) =
      rationalCharacters.equivCharacterLattice T (characterRestrict tP ψ) := by
  have h1 : tP ≫ (P.innerIso n').hom = CommGroupScheme.groupHom σ.hom ≫ tP := by
    have key : (tP ≫ (P.innerIso n').hom) ≫ iP = (CommGroupScheme.groupHom σ.hom ≫ tP) ≫ iP := by
      rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, htP, hn', Category.assoc, htP]
      exact hn
    apply hom_ext_points
    intro V x
    have hx := congrArg (fun f : T.toGrp ⟶ G => x ≫ f.hom.hom) key
    apply (cancel_mono iP.hom.hom).mp
    simp only [Grp.comp_hom_hom, Category.assoc] at hx ⊢
    exact hx
  have h2 : CommGroupScheme.groupHom σ.hom ≫ (tP ≫ ψ.toMul) = tP ≫ ψ.toMul := by
    rw [← Category.assoc, ← h1, Category.assoc, innerIso_hom_comp_character]
  set x := rationalCharacters.equivCharacterLattice T (characterRestrict tP ψ) with hxdef
  have h3 : σ.hom ≫ x = x := by
    apply CommGroupScheme.hom_ext_points
    intro V y
    rw [comp_groupHom_comp]
    change (y ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ (tP ≫ ψ.toMul).hom.hom =
      y ≫ (tP ≫ ψ.toMul).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, h2]
  rw [characterAut_apply, ← h3, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, h3]

end Conjugation

end Langlands.GroupScheme.DominantMultiple
