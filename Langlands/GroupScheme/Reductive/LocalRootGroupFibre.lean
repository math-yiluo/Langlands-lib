import Langlands.GroupScheme.Dynamic.UnipotentGrading
import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.CentralizerRootsProof
import Langlands.GroupScheme.Reductive.RankOneCellData
import Langlands.GroupScheme.Reductive.RankOnePositiveRootProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness

/-! # The root group of a split reductive group over a ring and its field fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The corepresented model of `G`. -/
abbrev model : GroupScheme (Spec (CommRingCat.of R)) :=
  Corepresented.groupScheme (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G)

/-- The torus in the corepresented model. -/
abbrev modelTorus : splitTorus (Spec (CommRingCat.of R)) I ⟶ model (G := G) :=
  i ≫ (AffineCoordinates.groupSchemeIso G).inv

/-- The cocharacter `mu` of the torus, in the corepresented model. -/
abbrev centCochar : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ model (G := G) :=
  Dynamic.Affine.cocharacter (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i)

theorem centCochar_eq : centCochar i mu =
    CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ modelTorus i :=
  Category.assoc _ _ _

/-- The dynamic centralizer `Z = Z_G(mu)`, itself a corepresented group. -/
abbrev Zc := Corepresented.centralizerScheme (centCochar i mu)

/-- The inclusion `Z ⟶ G` in the model. -/
abbrev jZ : Zc i mu ⟶ model (G := G) := Corepresented.centralizerHom (centCochar i mu)

/-- The torus factors through `Z`. -/
def torusZ : splitTorus (Spec (CommRingCat.of R)) I ⟶ Zc i mu :=
  (Corepresented.isRepresentedBy_centralizerHom (centCochar i mu)).liftOfLE (modelTorus i)
    (by
      rw [centCochar_eq]
      exact range_le_centralizer_groupHom_comp (T := splitTorus.commGroupScheme _ I) (modelTorus i)
        (splitTorus.exponentCocharacter _ I mu))

theorem torusZ_comp : torusZ i mu ≫ jZ i mu = modelTorus i :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _

/-- The cocharacter `nu` of the torus, as a cocharacter of `Z`. -/
abbrev unipCochar : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ Zc i mu :=
  CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ torusZ i mu

/-- The root group `U = U_Z(nu)`, a corepresented group. -/
abbrev Uc := Corepresented.unipotentScheme (unipCochar i mu nu)

/-- Its inclusion into `Z`. -/
abbrev jU : Uc i mu nu ⟶ Zc i mu := Corepresented.unipotentHom (unipCochar i mu nu)

/-- The coordinate ring of `U`. -/
abbrev coordU := quotientAlgebra (unipotentIdeal (unipCochar i mu nu))

/-! ### Base change of exponent cocharacters -/

theorem baseChangeCocharacter_groupHom_comp {S S' : Scheme.{u}} (b : S' ⟶ S) {H : GroupScheme S}
    (n : I → ℤ) (j : splitTorus S I ⟶ H) :
    Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I n) ≫ j) =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter S' I n) ≫
        ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map j) := by
  have h := splitTorus.groupHom_exponentCocharacter_baseChange S I b n
  rw [← h, Category.assoc, Iso.hom_inv_id_assoc, Dynamic.baseChangeCocharacter,
    Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]

/-! ### Field fibres -/

section Fibre

variable (K : Type u) [Field K] [Algebra R K]

/-- The base change of `Z` to a field. -/
abbrev ZK := (GroupScheme.baseChange (algebraBaseMap R K)).obj (Zc i mu)

/-- The inclusion of `Z_K` into `G_K`. -/
abbrev jZK : ZK i mu K ⟶ (GroupScheme.baseChange (algebraBaseMap R K)).obj G :=
  (GroupScheme.baseChange (algebraBaseMap R K)).map (jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom)

/-- The torus of `Z_K`. -/
abbrev tK : splitTorus (Spec (CommRingCat.of K)) I ⟶ ZK i mu K :=
  (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv ≫
    (GroupScheme.baseChange (algebraBaseMap R K)).map (torusZ i mu)

theorem tK_comp : tK i mu K ≫ jZK i mu K = splitTorus.baseChangeHom (K := K) G I i := by
  rw [Category.assoc, ← Functor.map_comp, ← Category.assoc, torusZ_comp, modelTorus,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem isRepresentedBy_jZK : (Dynamic.centralizer (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter _ I mu) ≫ splitTorus.baseChangeHom (K := K) G I i)).IsRepresentedBy
    (jZK i mu K) := by
  have h0 := (Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i)).baseChange
      (algebraBaseMap R K)
  rw [← Dynamic.centralizer_baseChange, baseChangeCocharacter_groupHom_comp] at h0
  exact h0

theorem isClosedSubgroup_jZK : IsClosedSubgroup (jZK i mu K) :=
  (Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i)).baseChange
      (algebraBaseMap R K)

/-- The base change of `U` to a field. -/
abbrev UK := (GroupScheme.baseChange (algebraBaseMap R K)).obj (Uc i mu nu)

theorem isRepresentedBy_jUK : (Dynamic.unipotent (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter _ I nu) ≫ tK i mu K)).IsRepresentedBy
    ((GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)) := by
  have h0 := (Corepresented.isRepresentedBy_unipotentHom (unipCochar i mu nu)).baseChange
    (algebraBaseMap R K)
  rw [← Dynamic.unipotent_baseChange, baseChangeCocharacter_groupHom_comp] at h0
  exact h0

/-- **The field root group.** If on the fibre over `K` the roots of `G_K` orthogonal to `mu`
are `±α`, and `⟨α, nu⟩ > 0`, then the base change of `U` is `𝔾ₐ`, with the torus acting through
`α`. -/
theorem exists_fibreIso (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap R K)).obj G))
    (hmaxK : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
      (splitTorus.baseChangeHom (K := K) G I i))
    (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (hα : haveI := hGK.isAffineHom; α ∈ roots (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := K) G I i))
    (hroots : haveI := hGK.isAffineHom; ∀ β ∈ roots (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := K) G I i),
      latticePairing _ β (splitTorus.exponentCocharacter _ I mu) = 0 → β = α ∨ β = -α)
    (hαmu : latticePairing _ α (splitTorus.exponentCocharacter _ I mu) = 0)
    (hnu : 0 < latticePairing _ α (splitTorus.exponentCocharacter _ I nu)) :
    ∃ Φ : Ga K ≅ UK i mu nu K, ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X)
        (x : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction α Z t x ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom := by
  have hT : IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I).toGrp :=
    isSplitTorus_splitTorus I
  have hZK : IsConnectedReductive (ZK i mu K) :=
    dynamicCentralizerReductive K _ hGK _ _ _ (isClosedSubgroup_jZK i mu K)
      (isRepresentedBy_jZK i mu K)
  have ht : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)
      (tK i mu K) :=
    IsMaximalTorus.of_comp (isClosedSubgroup_jZK i mu K) (by rwa [tK_comp])
  have hrootsZ := dynamicCentralizerRoots K _ hGK _ hT _ hmaxK _ _ _ (isClosedSubgroup_jZK i mu K)
    (isRepresentedBy_jZK i mu K) hZK (tK i mu K) (tK_comp i mu K)
  have := hGK.isAffineHom
  have := hZK.isAffineHom
  have hmemZ : ∀ β, β ∈ roots (T := splitTorus.commGroupScheme _ I) (tK i mu K) → β = α ∨ β = -α := by
    intro β hβ
    rw [hrootsZ] at hβ
    exact hroots β hβ.1 hβ.2
  have hrank : ∀ β ∈ roots (T := splitTorus.commGroupScheme _ I) (tK i mu K),
      ∀ β₂ ∈ roots (T := splitTorus.commGroupScheme _ I) (tK i mu K),
      ¬ LinearIndependent ℤ ![β, β₂] := by
    intro β hβ β₂ hβ₂ hli
    rw [LinearIndependent.pair_iff] at hli
    rcases hmemZ β hβ with rfl | rfl <;> rcases hmemZ β₂ hβ₂ with rfl | rfl
    · have := hli 1 (-1) (by simp)
      omega
    · have := hli 1 1 (by simp)
      omega
    · have := hli 1 1 (by simp)
      omega
    · have := hli 1 (-1) (by simp)
      omega
  have hαZ : α ∈ roots (T := splitTorus.commGroupScheme _ I) (tK i mu K) := by
    rw [hrootsZ]
    exact ⟨hα, hαmu⟩
  obtain ⟨x, hx, hxeq⟩ := rankOne_exists_rootGroup rankOnePositiveRootUniqueness splitRootLieLine
    hZK hT (tK i mu K) ht hrank α hαZ (splitTorus.exponentCocharacter _ I nu) hnu
  let Φ := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hx (isRepresentedBy_jUK i mu nu K)
  refine ⟨Φ, fun Z t a => ?_⟩
  have hΦ : Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu) = x :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hx _
  rw [hΦ]
  exact hxeq Z t a

end Fibre

/-! ### Character values on unit points -/

section CharValue

open AffineLine

variable {K : Type u} [Field K] {D : Type u} [CommRing D] [Algebra K D]

/-- On the point of a cocharacter at a unit `u`, a character takes the value `u ^ ⟨χ, ν⟩`. -/
theorem charValue_unitPoint {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (χ : characterLattice S) (ν : cocharacterLattice S) (u : Dˣ) :
    VectorGroup.charValue χ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K D))))
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
          (CommGroupScheme.groupHom ν).hom.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of D)).inv ((u ^ latticePairing S χ ν : Dˣ) : D) := by
  have hid : ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K D))) ⟶
      (Gm (Spec (CommRingCat.of K))).X,
      x ≫ (CommGroupScheme.groupHom (𝟙 (Gm (Spec (CommRingCat.of K))))).hom.hom = x :=
    fun x => Category.comp_id x
  rw [VectorGroup.charValue, ← comp_groupHom_comp, eq_gmEndEquiv_zsmul K (ν ≫ χ),
    comp_groupHom_zsmul, hid, latticePairing_apply, map_zpow, unitPoint,
    MulEquiv.apply_symm_apply, ← map_zpow]
  rfl

theorem weightPointAction_scalarPoint {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (χ : characterLattice S) (T : Over (Spec (CommRingCat.of K))) (t : T ⟶ S.X)
    (c : Γ(T.left, ⊤)) :
    VectorGroup.weightPointAction χ T t (VectorGroup.scalarPoint (CommRingCat.of K) T c) =
      VectorGroup.scalarPoint (CommRingCat.of K) T (VectorGroup.charValue χ T t * c) := by
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_weightPointAction, Pi.smul_apply, VectorGroup.coordinates_scalarPoint,
    VectorGroup.coordinates_scalarPoint, smul_eq_mul]

end CharValue

/-! ### The parameter family on a field fibre -/

section Family

variable {K : Type u} [Field K] [Algebra R K] (Φ : Ga K ≅ UK i mu nu K)
  (D : Type u) [CommRing D] [Algebra R D] [Algebra K D] [IsScalarTower R K D]

/-- The point of `U_K` over `Spec D` with parameter `d`. -/
def fibrePoint (d : D) : RingCoordinates.testOver K D ⟶ (UK i mu nu K).X :=
  VectorGroup.scalarPoint (CommRingCat.of K) (RingCoordinates.testOver K D)
      ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) ≫ Φ.hom.hom.hom

/-- The `R`-algebra map classifying the underlying point of `fibrePoint`. -/
def fibreAlgHom (d : D) : coordU i mu nu →ₐ[CommRingCat.of R] D :=
  RingCoordinates.baseAlgHom (fibrePoint i mu nu Φ D d)

variable {D} {D' : Type u} [CommRing D'] [Algebra R D'] [Algebra K D'] [IsScalarTower R K D']

omit [Algebra R D] [IsScalarTower R K D] [Algebra R D'] [IsScalarTower R K D'] in
theorem fibrePoint_comp (g : D →ₐ[K] D') (d : D) :
    RingCoordinates.specMapK g ≫ fibrePoint i mu nu Φ D d = fibrePoint i mu nu Φ D' (g d) := by
  rw [fibrePoint, fibrePoint, ← Category.assoc, VectorGroup.scalarPoint_comp]
  congr 2
  exact Corepresented.appTop_ΓSpecIso_inv_of_specMap_eq (CommRingCat.ofHom g.toRingHom) _ rfl d

theorem fibreAlgHom_comp (g : D →ₐ[K] D') (d : D) :
    fibreAlgHom i mu nu Φ D' (g d) =
      (g.restrictScalars (CommRingCat.of R)).comp (fibreAlgHom i mu nu Φ D d) := by
  rw [fibreAlgHom, fibreAlgHom, ← fibrePoint_comp, RingCoordinates.baseAlgHom_comp]

omit [Algebra R D] [IsScalarTower R K D] in
variable (D) in
theorem fibrePoint_bijective : Function.Bijective (fibrePoint i mu nu Φ D) := by
  have h1 : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of D)).inv :=
    ((Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv.symm).bijective
  have h2 : Function.Bijective (VectorGroup.scalarPoint (CommRingCat.of K) (RingCoordinates.testOver K D)) := by
    refine ⟨fun c c' h => ?_, fun v => ⟨_, VectorGroup.scalarPoint_coordinate _ v⟩⟩
    have := congrArg (fun v => (VectorGroup.coordinates _ 1 _ v).toAdd 0) h
    simpa only [VectorGroup.coordinates_scalarPoint] using this
  have h3 : Function.Bijective fun v : RingCoordinates.testOver K D ⟶ (Ga K).X => v ≫ Φ.hom.hom.hom :=
    (isoPointsEquiv Φ (RingCoordinates.testOver K D)).bijective
  exact h3.comp (h2.comp h1)

variable (D) in
theorem fibreAlgHom_bijective : Function.Bijective (fibreAlgHom i mu nu Φ D) :=
  RingCoordinates.baseAlgHom_bijective.comp (fibrePoint_bijective i mu nu Φ D)

omit [Algebra R D] [IsScalarTower R K D] in
/-- Conjugation by the cocharacter `nu` scales the parameter by `u ^ ⟨α, nu⟩`. -/
theorem fibrePoint_conj (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (hΦ : ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction α Z t x ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom)
    (u : Dˣ) (d : D) :
    (AffineLine.unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
        (Dynamic.baseChangeCocharacter (algebraBaseMap R K) (unipCochar i mu nu)).hom.hom) *
        (fibrePoint i mu nu Φ D d ≫
          ((GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
        (AffineLine.unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
          (Dynamic.baseChangeCocharacter (algebraBaseMap R K) (unipCochar i mu nu)).hom.hom)⁻¹ =
      fibrePoint i mu nu Φ D
          (((u ^ latticePairing _ α (splitTorus.exponentCocharacter _ I nu) : Dˣ) : D) * d) ≫
        ((GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom := by
  rw [baseChangeCocharacter_groupHom_comp]
  have h1 := hΦ (RingCoordinates.testOver K D)
    (AffineLine.unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu)).hom.hom)
    (VectorGroup.scalarPoint (CommRingCat.of K) (RingCoordinates.testOver K D)
      ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d))
  rw [weightPointAction_scalarPoint, charValue_unitPoint, ← map_mul] at h1
  simp only [fibrePoint, Grp.comp_hom_hom, Category.assoc] at h1 ⊢
  exact h1

/-- The classifying map of the universal parameter point is a universal line. -/
theorem isUniversalLine_fibre :
    CommutativeAlgebra.GradedLine.IsUniversalLine K (fibreAlgHom i mu nu Φ K[X] Polynomial.X) := by
  intro D _ _ _ _
  have h : (fun d : D => ((Polynomial.aeval d).restrictScalars R).comp
      (fibreAlgHom i mu nu Φ K[X] Polynomial.X)) = fibreAlgHom i mu nu Φ D := by
    funext d
    have := fibreAlgHom_comp i mu nu Φ (Polynomial.aeval d) Polynomial.X
    rw [Polynomial.aeval_X] at this
    exact this.symm
  rw [h]
  exact fibreAlgHom_bijective i mu nu Φ D

/-- **The scaling identity on a field fibre.** The classifying map of the universal parameter
point intertwines the grading of the coordinate ring of `U` with `Y ↦ T^m Y`, where
`m = ⟨α, nu⟩`. -/
theorem scaling_fibre (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (hΦ : ∀ (Z : Over (Spec (CommRingCat.of K)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
      (t ≫ (tK i mu K).hom.hom) *
          (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
          (t ≫ (tK i mu K).hom.hom)⁻¹ =
        VectorGroup.weightPointAction α Z t x ≫
          (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom)
    (m : ℕ) (hm : latticePairing _ α (splitTorus.exponentCocharacter _ I nu) = m)
    (a : coordU i mu nu) :
    AddMonoidAlgebra.mapRingHom ℤ ((fibreAlgHom i mu nu Φ K[X] Polynomial.X :
        coordU i mu nu →ₐ[CommRingCat.of R] K[X]) : coordU i mu nu →+* K[X])
        (unipCoaction (unipCochar i mu nu) a) =
      Polynomial.aeval (LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.C Polynomial.X :
        LaurentPolynomial K[X]) (fibreAlgHom i mu nu Φ K[X] Polynomial.X a) := by
  let D₀ := LaurentPolynomial K[X]
  refine Corepresented.scaling_of_conj (unipCochar i mu nu) m
    (RingCoordinates.testOverHom (CommRingCat.of R) K K[X] ≫ GroupScheme.baseChangePointsEquiv
      (RingCoordinates.baseMap (CommRingCat.of R) K) (Uc i mu nu) _ (fibrePoint i mu nu Φ K[X] Polynomial.X))
    (RingCoordinates.testOverHom (CommRingCat.of R) K D₀ ≫ GroupScheme.baseChangePointsEquiv
      (RingCoordinates.baseMap (CommRingCat.of R) K) (Uc i mu nu) _
        (fibrePoint i mu nu Φ D₀ (LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.C Polynomial.X)))
    ?_ ?_ a
  · have h := fibreAlgHom_comp i mu nu Φ
      (Polynomial.aeval (LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.C Polynomial.X : D₀))
      Polynomial.X
    rw [Polynomial.aeval_X] at h
    exact h
  · have h1 := RingCoordinates.specMapOver_comp_testOverHom (G := Uc i mu nu)
      ((Algebra.ofId K[X] D₀).restrictScalars K) (fibrePoint i mu nu Φ K[X] Polynomial.X)
    rw [fibrePoint_comp] at h1
    change RingCoordinates.specMapOver (constIncl (R := CommRingCat.of R)) ≫ _ = _ at h1
    rw [h1, Category.assoc, Category.assoc, ← GroupScheme.baseChangePointsEquiv_comp,
      ← GroupScheme.baseChangePointsEquiv_comp, ← RingCoordinates.testOverHom_comp_conj]
    congr 2
    have h2 := fibrePoint_conj i mu nu Φ α hΦ (unitT K[X])
      ((Algebra.ofId K[X] D₀).restrictScalars K Polynomial.X)
    rw [hm, zpow_natCast, ← zpow_natCast, unitT_zpow] at h2
    exact h2

end Family

/-! ### The coordinate ring of the root group -/

section Coordinate

variable [Smooth G.X.hom]

theorem finiteType_coordU : Algebra.FiniteType R (coordU i mu nu) := by
  have hB : Algebra.Smooth (CommRingCat.of R) (AffineCoordinates.algebra G) :=
    (DynamicSmooth.smooth_algSpec_iff (AffineCoordinates.algebra G)).1
      (smooth_of_over_iso ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))
        (inferInstance : Smooth G.X.hom))
  have h1 : Algebra.FiniteType R (quotientAlgebra (centralizerIdeal (centCochar i mu))) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective

/-- **The coordinate ring of `U` is a polynomial ring.** If on every field fibre the base change
of `U` is `𝔾ₐ` with the torus acting through a character `α` with `⟨α, nu⟩ = m > 0`, then over a
reduced local ring the coordinate ring of `U` is `R[x]` for a homogeneous `x` of degree `m`. -/
theorem exists_coordinate [IsLocalRing R] [IsReduced R] {m : ℕ} (hm0 : 0 < m)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
        (Φ : Ga K ≅ UK i mu nu K),
        (∀ (Z : Over (Spec (CommRingCat.of K)))
            (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
          (t ≫ (tK i mu K).hom.hom) *
              (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
                (jU i mu nu)).hom.hom) *
              (t ≫ (tK i mu K).hom.hom)⁻¹ =
            VectorGroup.weightPointAction α Z t x ≫
              (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) ∧
        latticePairing _ α (splitTorus.exponentCocharacter _ I nu) = m) :
    ∃ x ∈ CommutativeAlgebra.GradedLine.homog (isGrading_unipCoaction (unipCochar i mu nu)) m,
      Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu) := by
  have := finiteType_coordU i mu nu
  exact CommutativeAlgebra.GradedLine.exists_aeval_bijective_of_universal
    (isGrading_unipCoaction (unipCochar i mu nu))
    (fun a n hn => unipCoaction_coeff_neg (unipCochar i mu nu) a hn)
    (unipCoaction_coeff_zero (unipCochar i mu nu)) hm0 fun K _ _ => by
      obtain ⟨α, Φ, hΦ, hm⟩ := hfib K
      exact ⟨fibreAlgHom i mu nu Φ K[X] Polynomial.X, isUniversalLine_fibre i mu nu Φ,
        CommutativeAlgebra.GradedLine.coeff_eq_zero_of_scaling hm0
          (scaling_fibre i mu nu Φ α hΦ m hm)⟩

end Coordinate

end Langlands.GroupScheme.LocalRootGroup
