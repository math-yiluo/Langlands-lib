import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.GeneralLinearMaximalTorusRegularPointStatement
import Langlands.GroupScheme.IntegralModel.GeneralLinearCongruencePoints
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDensity
import Langlands.GroupScheme.Reductive.GeneralLinearMaximal
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalTransport
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Regular rational points of maximal tori in the general linear group -/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open _root_.Langlands.GroupScheme.GeneralLinear

universe u

private def regularityScalar {A : Type u} [CommRing A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) : A :=
  M.charpoly.resultant M.charpoly.derivative n (n - 1)

private theorem regularityScalar_map {A B : Type u} [CommRing A] [CommRing B] {n : ℕ}
    (f : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    regularityScalar (f.mapMatrix M) = f (regularityScalar M) := by
  change (M.map f).charpoly.resultant (M.map f).charpoly.derivative n (n - 1) = _
  rw [Matrix.charpoly_map, Polynomial.derivative_map, Polynomial.resultant_map_map]
  rfl

private theorem isUnit_regularityScalar_iff {K : Type u} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) :
    IsUnit (regularityScalar M) ↔ M.charpoly.Separable := by
  let p := M.charpoly
  have hp : p.natDegree = n := by simp [p, Matrix.charpoly_natDegree_eq_dim]
  have hd := p.natDegree_derivative_le
  have h := Polynomial.resultant_add_right_deg p p.derivative p.natDegree
    p.derivative.natDegree (p.natDegree - 1 - p.derivative.natDegree) le_rfl
  rw [Nat.add_sub_of_le hd, M.charpoly_monic.coeff_natDegree, one_pow, one_mul] at h
  change IsUnit (p.resultant p.derivative n (n - 1)) ↔ p.Separable
  rw [← hp, h]
  exact Polynomial.isUnit_resultant_iff_isCoprime M.charpoly_monic

private theorem mem_basicOpen_of_fieldPoint_iff {K : Type u} [Field K] {X : Scheme.{u}}
    (p : Spec (CommRingCat.of K) ⟶ X) (r : Γ(X, ⊤)) (s : Spec (CommRingCat.of K)) :
    p s ∈ X.basicOpen r ↔
      IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop r)) := by
  change s ∈ p ⁻¹ᵁ X.basicOpen r ↔ _
  rw [Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine']
  let v : PrimeSpectrum K := s
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop r) ∉
    v.asIdeal ↔ _
  rw [Ideal.eq_bot_of_prime v.asIdeal, Ideal.mem_bot, isUnit_iff_ne_zero]

private theorem regularityScalar_evaluation {R K : CommRingCat.{u}} {n : ℕ}
    {V : Over (Spec R)} (j : V ⟶ (groupScheme (Fin n) R).X)
    {W : Over (Spec R)} (p : W ⟶ V) (φ : Γ(W.left, ⊤) →+* K) :
    regularityScalar (φ.mapMatrix (pointsEquiv (Fin n) R W (p ≫ j)).val) =
      φ (p.left.appTop (regularityScalar (pointsEquiv (Fin n) R V j).val)) := by
  rw [regularityScalar_map, pointsEquiv_naturality]
  congr 1
  exact regularityScalar_map p.left.appTop.hom _

private theorem separable_charpoly_inner {K : Type u} [Field K] {n : ℕ}
    (g x : rationalPoints (groupScheme (Fin n) (CommRingCat.of K))) :
    (rationalPointsEquiv n (CommRingCat.of K)
      (x ≫ ((groupScheme (Fin n) (CommRingCat.of K)).innerIso g).hom.hom.hom)).val.charpoly.Separable
      ↔ (rationalPointsEquiv n (CommRingCat.of K) x).val.charpoly.Separable := by
  rw [comp_innerIso_hom, constantPoint_self, map_mul, map_mul, map_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem mem_range_diagonalTorus_iff {R : CommRingCat.{u}} {n : ℕ}
    {V : Over (Spec R)} (v : V ⟶ (groupScheme (Fin n) R).X) :
    v ∈ (SubgroupFunctor.range (diagonalTorus (Fin n) R)).carrier V ↔
      IsDiagonalGL (pointsEquiv (Fin n) R V v) := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact isDiagonalGL_diagonalTorus (Fin n) R z
  · intro h
    refine ⟨(splitTorus.pointsEquiv (ULift.{u} (Fin n)) V).symm (diagUnits h), ?_⟩
    apply (pointsEquiv (Fin n) R V).injective
    rw [pointsEquiv_diagonalTorus, MulEquiv.apply_symm_apply, diagonalTorusUnits_diagUnits]

private theorem rationalPointsEquiv_diagonalTorus_val {K : Type u} [Field K] {n : ℕ}
    (t : rationalPoints (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin n)))) :
    let R := CommRingCat.of K
    (rationalPointsEquiv n R (rationalPoints.map (diagonalTorus (Fin n) R) t)).val =
      Matrix.diagonal (fun i => globalSectionsEquiv R
        (splitTorus.pointsEquiv (ULift.{u} (Fin n)) _ t ⟨i⟩).val) := by
  dsimp only
  change (glRingEquiv (globalSectionsEquiv (CommRingCat.of K))
    (pointsEquiv (Fin n) _ _ (t ≫ (diagonalTorus (Fin n) _).hom.hom))).val = _
  rw [pointsEquiv_diagonalTorus]
  ext i j
  simp only [glRingEquiv_apply, coe_diagonalTorusUnits, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem exists_diagonalTorus_regular {K : Type u} [Field K] [Infinite K] (n : ℕ) :
    let R := CommRingCat.of K
    ∃ t : rationalPoints (splitTorus (Spec R) (ULift.{u} (Fin n))),
      (rationalPointsEquiv n R (rationalPoints.map (diagonalTorus (Fin n) R) t)).val.charpoly.Separable := by
  dsimp only
  let R := CommRingCat.of K
  let embed := Infinite.natEmbedding K
  let d (i : Fin n) := embed i.val - embed n
  have hd₀ (i : Fin n) : d i ≠ 0 := sub_ne_zero.mpr
    (fun h => (Nat.ne_of_lt i.isLt) (embed.injective h))
  have hd : Function.Injective d :=
    fun i j h => Fin.ext (embed.injective (sub_left_inj.mp h))
  let e := splitTorus.pointsEquiv (ULift.{u} (Fin n)) (Over.mk (𝟙 (Spec R)))
  let t := e.symm (fun i => Units.map (globalSectionsEquiv R).symm.toMonoidHom
    (Units.mk0 (d i.down) (hd₀ i.down)))
  refine ⟨t, ?_⟩
  rw [rationalPointsEquiv_diagonalTorus_val]
  have hm : (fun i => globalSectionsEquiv R
      (splitTorus.pointsEquiv (ULift.{u} (Fin n)) _ t ⟨i⟩).val) = d := by
    funext i
    change globalSectionsEquiv R (e t ⟨i⟩).val = _
    rw [show e t = _ from MulEquiv.apply_symm_apply _ _]
    exact (globalSectionsEquiv R).apply_symm_apply (d i)
  rw [hm, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
  exact hd

private theorem diagonal_of_commute_regularDiagonal {K : Type u} [Field K] {n : ℕ}
    {t : rationalPoints (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin n)))}
    (hsep : (rationalPointsEquiv n (CommRingCat.of K)
      (rationalPoints.map (diagonalTorus (Fin n) (CommRingCat.of K)) t)).val.charpoly.Separable)
    {V : Over (Spec (CommRingCat.of K))}
    (v : V ⟶ (groupScheme (Fin n) (CommRingCat.of K)).X)
    (hv : Commute v ((groupScheme (Fin n) (CommRingCat.of K)).constantPoint
      (rationalPoints.map (diagonalTorus (Fin n) (CommRingCat.of K)) t) V)) :
    IsDiagonalGL (pointsEquiv (Fin n) (CommRingCat.of K) V v) := by
  let R := CommRingCat.of K
  let d (a : Fin n) : Γ(Spec R, ⊤) :=
    (splitTorus.pointsEquiv (ULift.{u} (Fin n)) _ t ⟨a⟩).val
  let z := rationalPoints.map (diagonalTorus (Fin n) R) t
  let base := Over.mk (𝟙 (Spec R))
  let φ := V.hom.appTop.hom
  have hd : Function.Injective (fun i => globalSectionsEquiv R (d i)) := by
    rw [rationalPointsEquiv_diagonalTorus_val, Matrix.charpoly_diagonal,
      Polynomial.separable_prod_X_sub_C_iff] at hsep
    exact hsep
  have hz : (pointsEquiv (Fin n) R base z).val = Matrix.diagonal d := by
    change (pointsEquiv (Fin n) R base (t ≫ (diagonalTorus (Fin n) R).hom.hom)).val = _
    rw [pointsEquiv_diagonalTorus, coe_diagonalTorusUnits]
  have hp : (pointsEquiv (Fin n) R V ((groupScheme (Fin n) R).constantPoint z V)).val =
      Matrix.diagonal (fun i => φ (d i)) := by
    rw [pointsEquiv_constantPoint]
    change (pointsEquiv (Fin n) R base z).val.map φ = _
    rw [hz, Matrix.diagonal_map (map_zero φ)]
  intro i j hij
  let M := (pointsEquiv (Fin n) R V v).val
  have h := (hv.map (pointsEquiv (Fin n) R V)).map (Units.coeHom (Matrix (Fin n) (Fin n) Γ(V.left, ⊤)))
  change M * (pointsEquiv (Fin n) R V ((groupScheme (Fin n) R).constantPoint z V)).val =
    (pointsEquiv (Fin n) R V ((groupScheme (Fin n) R).constantPoint z V)).val * M at h
  rw [hp] at h
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) Γ(V.left, ⊤) => A i j) h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hd' : IsUnit (d j - d i) := by
    rw [← isUnit_map_iff (globalSectionsEquiv R), map_sub, isUnit_iff_ne_zero]
    exact sub_ne_zero.mpr (fun h => hij ((hd h).symm))
  have hunit := hd'.map φ
  have hzero : M i j * φ (d j - d i) = 0 := by
    rw [map_sub, mul_sub, hentry, mul_comm (φ (d i)), sub_self]
  exact hunit.mul_left_eq_zero.mp hzero

set_option maxHeartbeats 800000 in
/-- A rational point of the regular locus of a maximal torus has that
torus as its centralizer on all test schemes. -/
theorem generalLinearMaximalTorusRegularPoint :
    GeneralLinearMaximalTorusRegularPointStatement.{u} := by
  intro F _ _ n G T j hj
  let R := CommRingCat.of F
  obtain ⟨K, hK, hAlg, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting F T.toGrp hj.1
  let := hK
  let := hAlg
  let := hfin
  let := hgal
  let : Infinite K := Infinite.of_injective (algebraMap F K) (RingHom.injective _)
  let RK := CommRingCat.of K
  let b := Spec.map (CommRingCat.ofHom (algebraMap F K))
  let G' := (GroupScheme.baseChange b).obj G
  let T' := (CommGroupScheme.baseChange b).obj T
  let GK := groupScheme (Fin n) RK
  let j' : T'.toGrp ⟶ G' := (GroupScheme.baseChange b).map j
  let E : G' ≅ GK := baseChangeIso (Fin n) b
  let jK := j' ≫ E.hom
  let D := splitTorus.commGroupScheme (Spec RK) (ULift.{u} (Fin n))
  let i : D.toGrp ⟶ GK := diagonalTorus (Fin n) RK
  have hG : IsConnectedReductive G := isConnectedReductive_generalLinear F (Fin n)
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hj' : IsMaximalTorus j' := (maximalTorusBaseChange F K G T j hj.1 hj.2.1).mp hj
  have hjK := hj'.comp_iso E
  have hjKsplit : IsMaximalSplitTorus jK :=
    ⟨⟨hsplit, hjK.2.1⟩, fun S f hf a ha => hjK.2.2 S f a hf.1.isTorus hf.2 ha⟩
  have hi : IsMaximalSplitTorus i := isMaximalSplitTorus_diagonalTorus (n := Fin n) K
  obtain ⟨q, e, he⟩ := (maximalSplitTorusConjugacy K GK
    (isConnectedReductive_generalLinear K (Fin n))).1 T' D jK i hjKsplit hi
  let C := E ≪≫ GK.innerIso q
  have hC : j' ≫ C.hom = e.hom ≫ i := by
    simpa only [C, jK, Iso.trans_hom, Category.assoc] using he
  have hconjugate (t : rationalPoints T'.toGrp) :
      rationalPoints.map i (rationalPoints.map e.hom t) =
        rationalPoints.map jK t ≫ (GK.innerIso q).hom.hom.hom := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, he]
  let r := regularityScalar (pointsEquiv (Fin n) R T.X j.hom.hom).val
  let U := T.X.left.basicOpen r
  have hU : (U : Set T.X.left).Nonempty := by
    obtain ⟨w, hw⟩ := exists_diagonalTorus_regular (K := K) n
    let s : rationalPoints T'.toGrp := rationalPoints.map e.inv w
    have hs : rationalPoints.map e.hom s = w := by
      have hcomp : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 D.X := by
        rw [← Grp.comp_hom_hom, Iso.inv_hom_id]
        rfl
      simp only [s, rationalPoints.map_apply, Category.assoc, hcomp, Category.comp_id]
    have hsep : (rationalPointsEquiv n RK (rationalPoints.map jK s)).val.charpoly.Separable := by
      apply (separable_charpoly_inner q (rationalPoints.map jK s)).mp
      rw [← hconjugate s, hs]
      exact hw
    let base := Over.mk (𝟙 (Spec RK))
    let p := baseChangePointsEquiv b T.toGrp base s
    have hm : (rationalPointsEquiv n RK (rationalPoints.map jK s)).val =
        (globalSectionsEquiv RK).toRingHom.mapMatrix
          (pointsEquiv (Fin n) R ((Over.map b).obj base) (p ≫ j.hom.hom)).val := by
      simp only [jK, rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc]
      change (glRingEquiv (globalSectionsEquiv RK)
        (pointsEquiv (Fin n) RK base ((s ≫ j'.hom.hom) ≫ E.hom.hom.hom))).val = _
      rw [pointsEquiv_comp_baseChangeIso_hom]
      have hpoint : baseChangePointsEquiv b G base (s ≫ j'.hom.hom) = p ≫ j.hom.hom :=
        baseChangePointsEquiv_comp b j base s
      rw [hpoint]
      rfl
    let v : Spec RK := Classical.choice (inferInstanceAs (Nonempty (PrimeSpectrum K)))
    refine ⟨p.left v, (mem_basicOpen_of_fieldPoint_iff p.left r v).mpr ?_⟩
    have heval : regularityScalar (rationalPointsEquiv n RK (rationalPoints.map jK s)).val =
        globalSectionsEquiv RK (p.left.appTop r) :=
      hm ▸ regularityScalar_evaluation j.hom.hom p (globalSectionsEquiv RK).toRingHom
    exact heval ▸ (isUnit_regularityScalar_iff _).mpr hsep
  have hdense := hj.1.hasDenseRationalPoints_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨p, hpU, hp⟩ := hdense.inter_open_nonempty U U.isOpen hU
  obtain ⟨t, v, rfl⟩ := Set.mem_iUnion.mp hp
  let x := rationalPoints.map j t
  have hx : (rationalPointsEquiv n R x).val.charpoly.Separable := by
    have ht := (mem_basicOpen_of_fieldPoint_iff t.left r v).mp hpU
    have heval : regularityScalar (rationalPointsEquiv n R x).val =
        globalSectionsEquiv R (t.left.appTop r) :=
      regularityScalar_evaluation j.hom.hom t (globalSectionsEquiv R).toRingHom
    exact (isUnit_regularityScalar_iff _).mp (heval.symm ▸ ht)
  let : Mono j.hom.hom := IsClosedSubgroup.mono_overHom hj.2.1
  refine ⟨t, hx, ⟨inferInstance, range_eq_pointCentralizer G x ?_⟩⟩
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc F K
  let : Surjective b := hb₁
  let : Flat b := hb₂
  let : QuasiCompact b := hb₃
  apply SubgroupFunctor.le_range_of_baseChange_le b j
  rw [← SubgroupFunctor.range_baseChangeHom, pointCentralizer_baseChange]
  let x' := baseChangeSectionHom b G x
  let y := x' ≫ C.hom.hom.hom
  let w := rationalPoints.map e.hom (baseChangeSectionHom b T.toGrp t)
  have hy : y = rationalPoints.map i w := by
    change baseChangeSectionHom b G (t ≫ j.hom.hom) ≫ C.hom.hom.hom =
      (baseChangeSectionHom b T.toGrp t ≫ e.hom.hom.hom) ≫ i.hom.hom
    rw [baseChangeSectionHom_naturality, Category.assoc, ← Grp.comp_hom_hom]
    change baseChangeSectionHom b T.toGrp t ≫ (j' ≫ C.hom).hom.hom = _
    rw [hC, Grp.comp_hom_hom]
    exact (Category.assoc _ _ _).symm
  have hysep : (rationalPointsEquiv n RK (rationalPoints.map i w)).val.charpoly.Separable := by
    rw [← hy]
    change (rationalPointsEquiv n RK ((x' ≫ E.hom.hom.hom) ≫
      (GK.innerIso q).hom.hom.hom)).val.charpoly.Separable
    apply (separable_charpoly_inner q (x' ≫ E.hom.hom.hom)).mpr
    change (rationalPointsEquiv n RK
      (rationalPoints.map E.hom (baseChangeSectionHom b G x))).val.charpoly.Separable
    rw [rationalPointsEquiv_baseChangeSectionHom]
    change ((rationalPointsEquiv n R x).val.map (algebraMap F K)).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hx.map
  intro V z hz
  change z ∈ (G'.pointCentralizer x').carrier V at hz
  rw [mem_pointCentralizer] at hz
  change z * G'.constantPoint x' V = G'.constantPoint x' V * z at hz
  have hCommute : Commute (z ≫ C.hom.hom.hom) (GK.constantPoint (rationalPoints.map i w) V) := by
    rw [← hy]
    have h := congrArg (fun a : V ⟶ G'.X => a ≫ C.hom.hom.hom) hz
    simpa only [Commute, SemiconjBy, y, MonObj.mul_comp, constantPoint_comp] using h
  have hMem : z ≫ C.hom.hom.hom ∈ (SubgroupFunctor.range (j' ≫ C.hom)).carrier V := by
    rw [hC, SubgroupFunctor.range_iso_comp, mem_range_diagonalTorus_iff]
    exact diagonal_of_commute_regularDiagonal hysep _ hCommute
  have h := (MaximalTorusParameterExistence.mem_range_comp_iso_iff j' C _).mp hMem
  have hcancel : C.hom.hom.hom ≫ C.inv.hom.hom = 𝟙 G'.X := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id]
    rfl
  simp only [Category.assoc, hcancel] at h
  exact (Category.comp_id (show V ⟶ G'.X from z)) ▸ h

end Langlands.GroupScheme
