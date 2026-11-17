import Langlands.GroupScheme.Rational.TorusWeightPolynomial
import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Dynamic.UnipotentPrimitiveCoordinate
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy

/-! # The first intrinsic cyclic cutoff is the dynamic unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Corepresented

open AffineLine UnipotentPrimitive

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Reading the only exponent identifies the rank-one exponent lattice with the integers. -/
def rankOneExponentEquiv : (PUnit.{u + 1} → ℤ) ≃+ ℤ where
  toFun m := m PUnit.unit
  invFun n _ := n
  left_inv m := by ext i; cases i; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The rank-one Laurent algebra is the usual Laurent polynomial algebra. -/
def rankOneLaurentEquiv (A : CommAlgCat.{u} R) :
    AddMonoidAlgebra A (PUnit.{u + 1} → ℤ) ≃ₐ[R] LaurentPolynomial A :=
  AddMonoidAlgebra.domCongr R A rankOneExponentEquiv

/-- The algebra morphism of the rank-one Laurent comparison. -/
abbrev rankOneLaurentHom (A : CommAlgCat.{u} R) :
    laurent PUnit A ⟶ CommAlgCat.of R (LaurentPolynomial A) :=
  CommAlgCat.ofHom (rankOneLaurentEquiv A).toAlgHom

theorem rankOneLaurentHom_const (A : CommAlgCat.{u} R) :
    constHom PUnit A ≫ rankOneLaurentHom A =
      CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A)) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change rankOneLaurentEquiv A (AddMonoidAlgebra.single 0 a) = LaurentPolynomial.C a
  simp [rankOneLaurentEquiv]

theorem rankOneLaurentHom_units (A : CommAlgCat.{u} R) :
    (fun i => Units.map (rankOneLaurentHom A).hom.toMonoidHom (universalUnits PUnit A i)) =
      fun _ : PUnit => unitT A := by
  funext i
  apply Units.ext
  change rankOneLaurentEquiv A (AddMonoidAlgebra.single (Pi.single i 1) 1) =
    LaurentPolynomial.T 1
  cases i
  simp [rankOneLaurentEquiv, rankOneExponentEquiv]

/-- Rank-one split-torus conjugation through the supplied cocharacter. -/
def rankOneAction (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) : TorusAction F PUnit :=
  TorusAction.ofAutomorphicAction e
    ((AutomorphicAction.conjugation χ).transport (splitTorus.gmIso _).inv (Iso.refl _))

/-- The first intrinsic cyclic cutoff for the conjugation action of a cocharacter. -/
abbrev rankOneFirstCut (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) :
    SubgroupFunctor (groupScheme F e) :=
  cutSubgroupFunctor (isCutOutBy_weightIdeal e (rankOneAction e χ)
    (cyclicTail (fun _ : PUnit => 1) 1))

theorem rankOne_torusPt (A : CommAlgCat.{u} R) (t : PUnit → Aˣ) :
    torusPt PUnit A t ≫ (splitTorus.gmIso (Spec R)).inv.hom.hom =
      unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (t PUnit.unit) := by
  apply (Gm.affinePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R A)))).injective
  rw [affinePointsEquiv_unitPoint]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
    (Gm.pointsEquiv _ _ (torusPt PUnit A t ≫ (splitTorus.gmIso (Spec R)).inv.hom.hom)) = _
  rw [RelativeRoot.CharacterFpqc.gmIso_inv_points]
  exact congrFun ((splitTorus.algebraPointsEquiv PUnit A).apply_symm_apply t) PUnit.unit

theorem affinePoint_rankOneAction (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
    {A : CommAlgCat.{u} R} (t : PUnit → Aˣ) (x : F.obj A) :
    affinePoint e ((rankOneAction e χ).act t x) =
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (t PUnit.unit) ≫ χ.hom.hom) *
        affinePoint e x *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (t PUnit.unit) ≫ χ.hom.hom)⁻¹ := by
  change (affinePointsEquiv F e A).symm
    (affinePointsEquiv F e A
      (((AutomorphicAction.conjugation χ).transport (splitTorus.gmIso _).inv
        (Iso.refl _)).act (torusPt PUnit A t) ((affinePointsEquiv F e A).symm x))) = _
  rw [MulEquiv.symm_apply_apply, AutomorphicAction.transport_act]
  simp only [Iso.refl_hom, Iso.refl_inv]
  rw [AutomorphicAction.conjugation_act, rankOne_torusPt]
  rfl

theorem rankOne_map_hat (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    F.map (rankOneLaurentHom A) (hat (rankOneAction e χ) x) =
      (rankOneAction e χ).act (fun _ => unitT A)
        (F.map (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A))) x) := by
  change F.map (rankOneLaurentHom A)
    ((rankOneAction e χ).act (universalUnits PUnit A) (F.map (constHom PUnit A) x)) = _
  rw [(rankOneAction e χ).naturality, rankOneLaurentHom_units]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, rankOneLaurentHom_const]
  rfl

theorem coord_rankOne_unitT (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
    {A : CommAlgCat.{u} R} (x : F.obj A) (b : B) :
    coord e ((rankOneAction e χ).act (fun _ => unitT A)
      (F.map (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A))) x)) b =
      AddMonoidAlgebra.mapRingHom ℤ (coord e x).toRingHom (coaction χ b) := by
  let c : A ⟶ CommAlgCat.of R (LaurentPolynomial A) :=
    CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := A))
  have hc : pointRing (affinePoint e (F.map c x)) =
      CommRingCat.ofHom (LaurentPolynomial.C.comp (coord e x).toRingHom) := by
    ext b
    rw [pointRing_affinePoint, coord_map]
    rfl
  rw [← pointRing_affinePoint, affinePoint_rankOneAction, pointRing_conj]
  change (coaction χ ≫ laurentCoeffMap (pointRing (affinePoint e (F.map c x))) ≫
    laurentEval _ (unitT A)) b = _
  rw [hc]
  exact eval₂_T_mapRingHom (coord e x).toRingHom (coaction χ b)

/-- The intrinsic rank-one coaction is exactly the dynamic conjugation coaction after
the canonical exponent comparison. -/
theorem rankOne_rho_eq_coaction (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) (b : B) :
    rankOneLaurentEquiv B (rho e (rankOneAction e χ) b) = coaction χ b := by
  calc
    _ = coord e (F.map (rankOneLaurentHom B) (hat (rankOneAction e χ) (univ e))) b := by
      rw [coord_map]
      rfl
    _ = coord e ((rankOneAction e χ).act (fun _ => unitT B)
        (F.map (CommAlgCat.ofHom (UnipotentPrimitive.constHom (R := R) (A := B)))
          (univ e))) b := by rw [rankOne_map_hat]; rfl
    _ = AddMonoidAlgebra.mapRingHom ℤ (coord e (univ e)).toRingHom (coaction χ b) :=
      coord_rankOne_unitT e χ (univ e) b
    _ = coaction χ b := by rw [coord_univ]; simp

theorem rankOne_comp_eq_coaction_coeff (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
    (m : PUnit → ℤ) (b : B) :
    comp e (rankOneAction e χ) m b = (coaction χ b).coeff (m PUnit.unit) := by
  have h := congrArg (fun q : LaurentPolynomial B => q.coeff (m PUnit.unit))
    (rankOne_rho_eq_coaction e χ b)
  have hm : (fun _ : PUnit => m PUnit.unit) = m := by ext i; cases i; rfl
  simpa [rankOneLaurentEquiv, rankOneExponentEquiv, hm, comp_apply] using h

theorem dynamicCounit_eq_coordinateCounit (b : B) :
    counit e b = AffineLinearEmbedding.counit e b := by
  have h := pointRing_affinePoint e (1 : F.obj (CommAlgCat.of R R)) b
  rw [affinePoint_one, pointRing_one, CommRingCat.comp_apply, Spec.preimage_map] at h
  simpa [coord_one] using h

theorem mem_rankOne_firstTail (m : PUnit.{u + 1} → ℤ) :
    m ∈ cyclicTail (fun _ : PUnit => (1 : ℤ)) 1 ↔ 0 < m PUnit.unit := by
  constructor
  · rintro ⟨n, -, hn, h⟩
    have h' : (n : ℤ) = m PUnit.unit := by simpa using congrFun h PUnit.unit
    rw [← h']
    exact_mod_cast hn
  · intro hm
    refine ⟨(m PUnit.unit).toNat, by omega, by omega, ?_⟩
    ext i
    cases i
    simp [Int.toNat_of_nonneg hm.le]

/-- On every coefficient algebra the first intrinsic cutoff consists exactly of the
affine points of the actual dynamic unipotent subgroup. -/
theorem mem_rankOne_firstCut_iff (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
    {A : CommAlgCat.{u} R} (x : F.obj A) :
    x ∈ weightSubgroup e (rankOneAction e χ) (cyclicTail (fun _ : PUnit => 1) 1) A ↔
      x ∈ affineSubgroups (Dynamic.unipotent χ) A := by
  change _ ↔ affinePoint e x ∈ (Dynamic.unipotent χ).carrier _
  rw [mem_weightSubgroup, mem_unipotent_iff (e := e) χ]
  simp only [counit_comp]
  simp only [rankOne_comp_eq_coaction_coeff, mem_rankOne_firstTail]
  have hp (b : B) : pointRing (affinePoint e x) b = coord e x b :=
    pointRing_affinePoint (A := A) e x b
  have hε (b : B) : (ConcreteCategory.hom (counit e)) b =
      AffineLinearEmbedding.counit e b := dynamicCounit_eq_coordinateCounit e b
  simp only [hp, map_sub, AlgHom.commutes, hε, sub_eq_zero]
  constructor
  · intro h
    refine ⟨fun b n hn => ?_, fun b => ?_⟩
    · have hn0 : (fun _ : PUnit.{u + 1} => n) ≠ 0 := by
        intro heq
        have := congrFun heq PUnit.unit
        change n = 0 at this
        omega
      simpa [hn0] using h b (fun _ => n) (by omega)
    · simpa using h b 0 (by simp)
  · rintro ⟨hneg, hzero⟩ b m hm
    by_cases hm0 : m = 0
    · subst m
      simpa using hzero b
    · have hmn : m PUnit.unit < 0 := by
        have hne : m PUnit.unit ≠ 0 := by
          intro h
          apply hm0
          ext i
          cases i
          exact h
        omega
      simpa [hm0] using hneg b (m PUnit.unit) hmn

/-- Over any commutative ring the first intrinsic cyclic weight cutoff is the actual
orbit-extension-and-contraction subgroup on every scheme test. -/
theorem rankOne_firstCut_eq_unipotent (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) :
    rankOneFirstCut e χ = Dynamic.unipotent χ := by
  rw [← cutSubgroupFunctor_affineSubgroups (isAffineCutOutBy_unipotent χ)]
  ext T x
  exact mem_rankOne_firstCut_iff e χ (pointsEquiv F e T x)

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.Dynamic.Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The first intrinsic cyclic cutoff in the actual coordinate model of an affine group,
transported back to that group on every scheme test. -/
def intrinsicFirstCut : SubgroupFunctor G :=
  (Corepresented.rankOneFirstCut (AffineCoordinates.corepresentation G)
    (cocharacter χ)).comap (AffineCoordinates.groupSchemeIso G).inv

/-- For any affine group over any commutative ring, the first intrinsic cyclic cutoff
equals its actual dynamic unipotent subgroup. -/
theorem intrinsicFirstCut_eq_unipotent :
    intrinsicFirstCut χ = Dynamic.unipotent χ := by
  unfold intrinsicFirstCut
  rw [Corepresented.rankOne_firstCut_eq_unipotent]
  exact (Dynamic.unipotent_eq_comap_of_iso χ (AffineCoordinates.groupSchemeIso G).symm).symm

end Langlands.GroupScheme.Dynamic.Affine
